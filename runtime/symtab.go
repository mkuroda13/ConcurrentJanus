package main

import (
	"cmp"
	"fmt"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"sync"
)

var memreg *regexp.Regexp = regexp.MustCompile(`^([\&\$\#]*\w+)\s*\[\s*([\&\$\#]*\w+(?:[\.\:]\d+)*)\s*\]`)
var inreg *regexp.Regexp = regexp.MustCompile(`^([\&\$\#]*)(\w+)((?:[\.\:]\d+)*)`)

type varentry struct {
	value         int
	size 		  int //1 mans normal variable, 0 means part of an array, 2+ means head of array and contains size of array
	lastupdatepid int //-1 means its uninit
	lastupdatepc  int //-1 means its uninit
}
type symtab struct {
	//Value of type varentry
	alloctable map[string]int
	varmem map[int]varentry
	heapmem   map[int]int
	semconds map[string]*sync.Cond
	alclimit int
}


func newSymtab() *symtab {
	tab := symtab{}
	tab.alloctable = make(map[string]int)
	tab.varmem = make(map[int]varentry)
	tab.heapmem = make(map[int]int)
	tab.semconds = make(map[string]*sync.Cond)
	tab.alclimit = 1
	return &tab
}
func (r *runtime) NotifySem(name string){
	v,ex := r.semconds[name]
	if !ex{
		v = sync.NewCond(exmut)
		r.semconds[name] = v
	}
	v.Signal()
}
func (r *runtime) WaitSem(name string) bool{
	//this infinity loops but it should be okay cuz if it does program executes more V than P thereby its very wrong
	//return true if its done waiting, false if terminated
	v,ex := r.semconds[name]
	if !ex{
		v = sync.NewCond(exmut)
		r.semconds[name] = v
	}
	semtolisten := make(chan bool)
	go func(){
		v.Wait()
		semtolisten <- true
	}()
	select {
	case <- r.runclose:
		r.runclose <- true
		return false
	case <- r.rundoner:
		r.rundoner <- true
		return false
	case <- semtolisten:
		return true
	}
	
}
func (r *runtime) AllocSym(s string, size int) int{
	//allocate new entry in alloctable, does not update pid and pc
	l := r.alclimit
	r.alloctable[s] = l
	for i := range size{
		r.symtab.varmem[l+i] = varentry{0,size,-1,-1}
	}
	r.alclimit += size
	return l
}
func (r *runtime) ReadSym(s string, pc *pc, rev bool) int {
	match := memreg.FindStringSubmatch(s)
	if match != nil {
		var mloc int
		i,er := strconv.Atoi(match[2])
		if er == nil{
			mloc = i
		} else {
			mloc = r.ReadSym(match[2], pc, rev)
		}

		name,idx := r.GetAllocIndex(match[1],pc,rev,mloc) //idx = loc of array base
		val := r.varmem[idx+mloc]
		//if not running in reverse, add dag
		if !rev {
			r.addEdge(val.lastupdatepid, val.lastupdatepc, name+"["+strconv.Itoa(mloc)+"]", false, pc.pid, pc.pc)
		}

		if match[1] == "M"{
			val := r.symtab.heapmem[mloc]
			if VAR_DEBUG{
				fmt.Printf("ReadOp: rtgt: %s, reval: M[%d], rloc: %d, rval: %d\n",s,mloc,0,val)
			}
			return val
		} else {
			val := r.varmem[idx+mloc]
			if VAR_DEBUG{
				fmt.Printf("ReadOp: rtgt: %s, reval: %s[%d], rloc: %d, rval: %d\n",s,match[1],mloc,idx+mloc,val.value)
			}
			return val.value
		}
	} else {
		pt := r.isPtr(s)
		if pt {
			idx := r.GetConvCut(s,pc)
			return r.alloctable[idx]
		}
		name,idx := r.GetAllocIndex(s,pc,rev,1)
		val := r.varmem[idx]
		//if not running in reverse, add dag
		if !rev {
			r.addEdge(val.lastupdatepid, val.lastupdatepc, name, false, pc.pid, pc.pc)
		}
		if VAR_DEBUG{
			fmt.Printf("ReadOp: rtgt: %s, reval: %s, rloc: %d, rval: %d\n",s,name,idx,val.value)
		}
		return val.value
		
	}
}
func (r *runtime) GetAllocIndex(s string,pc *pc, rev bool, size int) (string,int) {
	//name of variable, index
	key,ct,alc := r.convert(s,pc)
	for {
		v, ex := r.symtab.alloctable[key]
		if ex {
			return key,v
		}
		if !ct {
			if alc {
				idx := r.AllocSym(key,size)
				return key,idx
			} else {
				panic("unknown variable")
			}
		}
		key,ex = r.cut(key)
		if !ex {
			if alc {
				idx := r.AllocSym(key,size)
				return key,idx
			} else {
				panic("unknown variable")
			}
		}
	}
}
func (s *symtab) GetConvCut(name string, pc *pc) string {
	//for pointer operation, no actual allocation done
	key,ct,alc := s.convert(name,pc)
	for {
		if !ct {
			if alc {
				return key
			} else {
				panic("unknown variable")
			}
		} else {
			_, ex := s.alloctable[key]
			if ex {
				return key
			}
			key,ct = s.cut(key)
		}
	}
}
func (r *runtime) WriteSym(s string, value int, pc *pc) {
	match := memreg.FindStringSubmatch(s)
	if match != nil {
		var mloc int
		i,er := strconv.Atoi(match[2])
		if er == nil{
			mloc = i
		} else {
			mloc = r.ReadSym(match[2], pc, false)
		}
		if match[1] == "M"{
			r.heapmem[mloc] = value
			if VAR_DEBUG{
				fmt.Printf("WriteOp: wtgt: %s, weval: M[%d], wloc: %d, wval: %d\n",s,mloc,0,value)
			}
			r.WriteSym("M", 0, pc)
		} else {
			name,idx := r.GetAllocIndex(match[1],pc,rev,mloc)
			old := r.varmem[idx]
			r.varmem[idx] = varentry{0,old.size,pc.pid,pc.pc}
			r.addEdge(old.lastupdatepid, old.lastupdatepc, name+"["+strconv.Itoa(mloc)+"]", true, pc.pid, pc.pc)
			r.varmem[idx+mloc] = varentry{value,0,pc.pid,pc.pc}
			if VAR_DEBUG{
				fmt.Printf("WriteOp: wtgt: %s, weval: %s[%d], wloc: %d, wval: %d\n",s,match[1],mloc,idx+mloc,value)
			}
		}
	} else {
		pt := r.isPtr(s)
		if pt {
			idx := r.GetConvCut(s,pc)
			r.alloctable[idx] = value
			return
		}
		name,idx := r.GetAllocIndex(s,pc,rev,1)
		old := r.varmem[idx]
		r.varmem[idx] = varentry{value,1,pc.pid,pc.pc}
		if VAR_DEBUG && s != "M"{
			fmt.Printf("WriteOp: wtgt: %s, weval: %s, wloc: %d, wval: %d\n",s,name,idx,value)
		}
		r.addEdge(old.lastupdatepid, old.lastupdatepc, name, true, pc.pid, pc.pc)
	}
}

func (r *runtime) WriteSymRev(s string, value int, pc *pc) {
	match := memreg.FindStringSubmatch(s)
	if match != nil {
		var mloc int
		i,er := strconv.Atoi(match[2])
		if er == nil{
			mloc = i
		} else {
			mloc = r.ReadSym(match[2], pc, true)
		}
		r.ReadSym(match[1],pc,true)
		if match[1] == "M"{
			r.symtab.heapmem[mloc] = value
			if VAR_DEBUG{
				fmt.Printf("WriteOp: wtgt: %s, weval: M[%d], wloc: %d, wval: %d\n",s,mloc,0,value)
			}
			r.WriteSymRev("M", 0, pc)
		} else {
			_,idx := r.GetAllocIndex(match[1],pc,true,1)
			r.varmem[idx+mloc] = varentry{value,0,pc.pid,pc.pc}
			name,idx := r.GetAllocIndex(s,pc,true,1)
			//modify dag
			lpid := -1
			lpc := -1
			if pc.pid >= len(r.dag.incedges) {
				goto L0
			}
			if pc.pc >= len(r.dag.incedges[pc.pid]) {
				goto L0
			}
			for _, edge := range r.dag.incedges[pc.pid][pc.pc] {
				if edge.wt && edge.varname == name+"["+strconv.Itoa(mloc)+"]" {
					lpid = edge.pid
					lpc = edge.pc
				}
			}
		L0:
			r.symtab.varmem[idx] = varentry{value, r.symtab.varmem[idx].size, lpid, lpc}
			if VAR_DEBUG{
				fmt.Printf("WriteOp: wtgt: %s, weval: %s[%d], wloc: %d, wval: %d\n",s,match[1],mloc,idx+mloc,value)
			}
		}
		
	} else {
		pt := r.isPtr(s)
		if pt {
			idx := r.GetConvCut(s,pc)
			r.alloctable[idx] = value
			return
		}
		name,idx := r.GetAllocIndex(s,pc,true,1)
		//modify dag
		lpid := -1
		lpc := -1
		if pc.pid >= len(r.dag.incedges) {
			goto L1
		}
		if pc.pc >= len(r.dag.incedges[pc.pid]) {
			goto L1
		}
		for _, edge := range r.dag.incedges[pc.pid][pc.pc] {
			if edge.wt && edge.varname == name {
				lpid = edge.pid
				lpc = edge.pc
			}
		}
	L1:
		r.symtab.varmem[idx] = varentry{value, r.symtab.varmem[idx].size, lpid, lpc}
		if VAR_DEBUG && s != "M"{
			fmt.Printf("WriteOp: wtgt: %s, weval: %s, wloc: %d, wval: %d\n",s,name,idx,value)
		}
	}
}
func (tab *symtab) isPtr(name string) bool {
	return strings.Contains(name,"&")
}
//$ means its newly allocated one, and should not search downwards
//& means its ptr to the variable
//# will be allocated directly
func (tab *symtab) convert(name string, pc *pc) (string,bool,bool) {
	//b1 = false if name should not be cut
	//b2 = true if allocatable
	match := inreg.FindStringSubmatch(name)
	if match != nil{
		s := match[2]
		if !strings.Contains(match[1],"#"){
			for _,v := range pc.stackdepth{
				s += ":"
				for i,v1 := range v{
					if i != 0{
						s += "."
					}
					s += strconv.Itoa(v1)
				}
			}
		}
		s += match[3]
		return s,!strings.Contains(match[1],"$"),strings.Contains(match[1],"#")||strings.Contains(match[1],"$")
	}
	panic("unknown variable")
}
func (tab *symtab) cut(name string) (string,bool) {
	//convert n.0.0 -> n.0, return false if cannot cut
	i := strings.LastIndexAny(name,".:")
	if i != -1{
		return name[:i],true
	}
	return name,false
	
}

func (tab *symtab) PrintSym() {
	fmt.Print("---Symbol Status---\n")
	tkeys := make([]string,0,len(tab.alloctable))

	for i,_ := range tab.alloctable{
		tkeys = append(tkeys, i)
	}
	slices.SortFunc(tkeys,func (x string, y string) int {
		return cmp.Compare(len(x),len(y))
	})
	for _,i := range tkeys{
		e := tab.alloctable[i]
		if e != 0{
			v := tab.varmem[e]
			if v.size == 1 && !strings.Contains(i,"tmp"){
				fmt.Printf("%s -> [%d] -> %d\n",i,e,v.value)
			} else if v.size >= 2{
				fmt.Printf("%s -> [%d,%d] -> [",i,e,e+v.size-1)
				for i := range v.size{
					if i != 0{
						fmt.Print(",")
					}
					fmt.Print(tab.varmem[e+i].value)
				}
				fmt.Print("]\n")
			}
		}
	}
	
	fmt.Print("\n ---Memory Status---\n")
	for i,e := range tab.heapmem{
		fmt.Printf("%d: %d\n", i,e)
	}
}
