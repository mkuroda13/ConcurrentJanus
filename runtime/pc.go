package main

import (
	"fmt"
	"slices"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/mkuroda13/ConcurrentJanus/util"
)

type pc struct {
	head       int //LineNo of next instruction to be run
	pc         int //Ctr that increases by 1 every exec
	pid        int
	originpid  int //pid of the caller, focus will fall back to that once terminated
	executing  bool
	stackdepth [][]int
}

func newPC() *pc {
	return &pc{0, 0, 0, 0, false, make([][]int, 0)}
}

const (
	STOP = iota
	RUN_FWD
	RUN_FWD_ONCE
	RUN_BWD
	RUN_BWD_ONCE
	RUN_FWD_DAG
	RUN_FWD_ONCE_DAG
	TERMINATE
)

func (p *pc) execute(r *runtime) int {
	//0 means suspended
	//1 means reached EOF
	//2 means terminated
	for {
		select {
		case rev := <-r.runonce:
			//run once mode
			if r.isRunnable(p.pid, rev) && !p.executing {
				//check if dag allows it to run, if yes then execute, send rundone
				ret := p.executeBlock(r, rev)
				r.rundone <- true
				switch ret {
				case 1:
					//EOF
					util.Unclog(r.runclose)
					r.runclose <- true
					return 1
				case 2:
					//End of non main proc
					return 2
				}
			} else {
				//otherwise broadcast msg to another, block until rundone, which will also be broadcasted
				r.runonce <- rev
				<-r.rundoner
				r.rundoner <- true
			}
		case rev := <-r.runever:
			//run forever mode
			//broadcast run msg
			r.runever <- rev
			for {
				select {
				case <-r.runclose:
					r.runclose <- true
					return 0
				default:
					if r.isRunnable(p.pid, rev) {
						//check if dag allows it to run, if yes then execute, send dagupdate if modified dag
						ret := p.executeBlock(r, rev)
						//TODO add if dag actually does update check
						util.Unclog(r.dagupdate) // unclogs buffer so that it will not be blocked
						r.dagupdate <- true
						switch ret {
						case 1:
							//EOF, suspend the execution
							util.Unclog(r.runclose)
							r.runclose <- true
							return 1
						case 2:
							//End of non main proc
							r.termproc <- procchange{p.pid, p.originpid}
							return 2
						}
					} else {
						//otherwise block until dagupdate, which will also be broadcasted
						select {
						case <-r.runclose:
							r.runclose <- true
							return 0
						case <-r.dagupdate:
							r.dagupdate <- true
							continue
						}
					}
				}
			}
		case <-r.runclose:
			r.runclose <- true
			return 0
		}
	}
}

func (p *pc) executeBlock(r *runtime, rev bool) int {
	exmut.Lock()
	p.executing = true
	defer func() {
		p.executing = false
	}()
	inst := ""
	if rev {
		p.pc--
	}
	rt := p.executeOnce(r, rev, &inst)
	if rt != 0 {
		return rt
	}
	//executed between 0~2 times, always ends on head=3*n
	for p.head%3 != 0 {
		rt = p.executeOnce(r, rev, &inst)
		if rt == 3 {
			return rt
		}
		if rt != 0 {
			break
		}
	}
	if rev {
		r.runModifyDagRev(p.pid)
	}
	fmt.Print("P", p.pid, ",", p.pc, ">\n", inst, "\n")
	r.dag.exechistory = append(r.dag.exechistory, exhistory{p.pid,p.pc,inst,rev})
	if EXEC_DEBUG{
		if !rev{
			r.exmap[pidandpc{p.pid,p.pc}] = inst
		} else {
			i := ""
			k := strings.Split(inst,"\n")
			slices.Reverse(k)
			for _,i1 := range k {
				if i1 != ""{
					i += i1
					i += "\n"
				}
			}
			if i != r.exmap[pidandpc{p.pid,p.pc}]{
				panic("Unmatched execution: P" + strconv.Itoa(p.pid) + "," + strconv.Itoa(p.pc)+"\n"+
				"Expected: \n"+r.exmap[pidandpc{p.pid,p.pc}] +
				"Got: \n"+i)
			}
		}
	}
	if !rev {
		p.pc++
	}
	exmut.Unlock()
	if SLOW_DEBUG != 0 {
		time.Sleep(SLOW_DEBUG)
	}
	return rt
}

var exmut *sync.Mutex = &sync.Mutex{}

func (p *pc) executeOnce(r *runtime, rev bool, insts *string) int {
	//return of 0 means successful finish
	//1 is EOF/end of main block, execution of all subprocess should be suspended (though only main thread is supposed to live at this point)
	//2 is end of non-main block, execution of this process should be terminated
	//3 is suspension of proc mid-execution, pc and head does not get modified
	//4 is jump, indicates head is updated to corrent spot during execution, so we only need to update pc
	if !rev {
		if len(*(r.file)) <= p.head {
			p.head = len(*(r.file)) - 1
			return 1
		}
	} else {
		p.head--
		if p.head < 0 {
			p.head = 0
			return 1
		}
	}
	s := 1
	for _, inst := range r.instset {
		match := inst.re.FindStringSubmatch((*r.file)[p.head])
		if match != nil {
			if !rev {
				ex := (*r.file)[p.head]
				s = inst.fwd(r, p, match)
				*insts += ex
				*insts += "\n"
				if s == 2 {
					r.termproc <- procchange{p.pid, p.originpid}
					p.head++
				} else if s == 3 {
					s = 0
				} else if s == 4 {
					s = 0
				} else {
					p.head++
				}
			} else {
				ex := (*r.file)[p.head]
				s = inst.bwd(r, p, match)
				*insts += ex
				*insts += "\n"
				if s == 2 {
					r.termproc <- procchange{p.pid, p.originpid}
				} else if s == 3 {
					s = 0
					p.head++
				} else if s == 4 {
					s = 0
					p.head++
				}
			}
			goto L1
		}
	}
	fmt.Printf("Instruction unknown [%s]\n", (*r.file)[p.head])
	panic("Instruction unknown")
L1:
	return s
}

func (p *pc) getBlock() string{
	s := ""
	for _,v := range p.stackdepth{
		s += ":"
		for i,v1 := range v{
			if i != 0{
				s += "."
			}
			s += strconv.Itoa(v1)
		}
	}
	return s
}

func checkerr(e error) {
	if e != nil {
		panic(e)
	}
}
