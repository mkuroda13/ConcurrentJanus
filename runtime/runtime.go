package main

import (
	"fmt"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"sync"

	"github.com/mkuroda13/ConcurrentJanus/util"
)

type runtime struct {
	labels
	symtab
	instset   []instentry
	file      *[]string
	pcs       []*pc
	dag       dag
	runonce   chan bool
	rundone   chan bool
	rundoner  chan bool
	runever   chan bool
	runclose  chan bool
	dagupdate chan bool
	newproc   chan int
	termproc  chan procchange
	exmap map[pidandpc]string
}

type procchange struct {
	term   int
	origin int
}

type instentry struct {
	re  *regexp.Regexp
	fwd func(*runtime, *pc, []string) int
	bwd func(*runtime, *pc, []string) int
}

func (r *runtime) addrunPC(pid int, head int, originpid int, stackdepth [][]int) {
	for pid >= len(r.pcs) {
		r.pcs = append(r.pcs, nil)
	}
	if r.pcs[pid] == nil {
		r.pcs[pid] = newPC()
		r.pcs[pid].pid = pid
		r.pcs[pid].head = head
		r.pcs[pid].originpid = originpid
		r.pcs[pid].stackdepth = make([][]int,0,len(stackdepth))
		for _,v := range(stackdepth){
			r.pcs[pid].stackdepth = append(r.pcs[pid].stackdepth,slices.Clone(v))
		}
	}
	//head/origin will not be overwritten if the proc already exists
	r.newproc <- pid
	go r.pcs[pid].execute(r)

}

// same as addrunPC but with deferred call to wg.Done() and send signal to suspended if its suspended midway
func (r *runtime) addRunPCCall(pid int, head int, originpid int, stackdepth [][]int, group *sync.WaitGroup, suspended chan bool) {
	for pid >= len(r.pcs) {
		r.pcs = append(r.pcs, nil)
	}
	if r.pcs[pid] == nil {
		r.pcs[pid] = newPC()
		r.pcs[pid].pid = pid
		r.pcs[pid].head = head
		r.pcs[pid].originpid = originpid
		r.pcs[pid].stackdepth = make([][]int,0,len(stackdepth))
		for _,v := range(stackdepth){
			r.pcs[pid].stackdepth = append(r.pcs[pid].stackdepth,slices.Clone(v))
		}
	}
	//head/origin will not be overwritten if the proc already exists
	r.newproc <- pid
	go func() {
		defer group.Done()
		a := r.pcs[pid].execute(r)
		if a == 0 {
			suspended <- true
		}
	}()
}

func (r *runtime) getPC(pid int) (p *pc, _ bool) {
	if len(r.pcs) <= pid || pid < 0 {
		return nil, false
	}
	p = r.pcs[pid]
	return p, p != nil
}

//Generic debug rule
//focus is a pid selected by debugger
//
//in backwards-step-by-step, non-focus process will be reversed as much as possible until the only thing that can be reversed is the focus proc
//in backwards normal execution, all process can be reversed in any order allowed by dag
//when node is removed on normal dag, it will be marked as inactive
//
//in forwards-step-by-step, non-focus process will be ran as much as possible until the only thing that can be run is the focus proc, excluding non-annotated region
//dag evaluation will be done such that if they were to be run, they will not create any outgoing edges for any other inactive nodes
//-> 1. check the node's incoming edges, if any of the connected node is inactive, it cannot run
//-> if node's pc is less than actual procs pc, then that node is active, otherwise inactive
//if focus process is outside of dag, non-focus process will halt
//in forwards normal execution, all process can be executed in any order allowed by dag, including those who is not annotated

//channels/sync stuff. all channels that broadcast will be queued to not block caller
//USED IN STEP BY STEP
//runonce (chan bool): broadcasted from debug, true=bwd direction, reciever will evaluate if they are both in dag & runnable, if yes then run, otherwise block until rundone.
//rundone (chan bool): send from successfully reversed proc, receiver(debug) will treat it as one step done and send rundoner
//rundoner (chan bool): broadcasted from debug, proc will return to halt
//USED IN NORMAL RUN
//runever (chan bool): broadcasted from debug, receiver will enter run mode where they evaluate if its in dag, if not, run normally until halt
//if in dag, evaluate if next is runnable, if yes then run, otherwise block until dagupdate
//needs unclog before runclose, otherwise procs will respawn
//dagupdate (chan bool): broadcasted from proc when dag is modified such that other procs have chance to run again
//(all bwd instruction & fwd instruction that is in dag (thus make inactive node active again, to help with "any of the connected node is inactive then no run" restriction))
//runclose (chan bool): broadcasted from debug when stopped, or from proc when EOF. will terminate all procs. however, it does not delete proc's info such as pid, pc, head
//needs unclog before runever, otherwise procs will immidiately shut off
//OTHER
//newproc (chan): pid of newly created pc. debug's focus will change to that if it matches with target focus, disgarded by debug otherwise
//termproc (chan): conbi of terminating pc's pid and it's origin. debug's focus will change to origin if pid matches with focus, disgarded by debug otherwise

func (r *runtime) debug(debugsym <-chan string, done <-chan bool) {
	//runmode
	//0 means stopped
	//1 means executing
	//2 means awaiting for step by step excution to end
	reg := regexp.MustCompile(`focus\s+(\d+)`)
	rev := false
	focus_tgt := 0
	focus_now := 0
	r.addrunPC(0, r.GetBegin("main"), 0, make([][]int, 0))
	running := 1
	r.runever <- false
	stepexret := make(chan int, 1)
	for {
		switch running {
		case 1:
			select {
			case <-done:
				return
			//set running to false and await further debugsym
			case <-r.runclose:
				//broadcast
				r.runclose <- true
				running = 0
				fmt.Print("Debug >> Execution finished\n")
			//stop the execution midway
			case s := <-debugsym:
				switch s {
				case "\n":
					util.Unclog(r.runclose)
					util.Unclog(r.runever)
					r.runclose <- true
					running = 0
					fmt.Print("Debug >> Execution suspended by user\n")
				default:
					fmt.Print("Debug >> Unknown command\n")
				}
			case pid := <-r.newproc:
				if pid == focus_tgt && pid != focus_now {
					focus_now = pid
					fmt.Printf("Debug >> Focus change -> %d\n", focus_now)
				}
			case c := <-r.termproc:
				if c.term == focus_now {
					focus_now = c.origin
					fmt.Printf("Debug >> Focus change %d -> %d\n", c.term, c.origin)
				}
			}
		case 2:
			//step by step
		L1:
			select {
			case <-done:
				return
			case <-stepexret:
				running = 0
			case <-r.rundone:
				//broadcast rundoner
				util.Unclog(r.rundoner)
				r.rundoner <- true
				tgtpc, _ := r.getPC(focus_now)
				if r.isRunnable(focus_now, rev) && !tgtpc.executing {
					//if reversible, do it
					p, ex := r.getPC(focus_now)
					util.Unclog(stepexret)
					if ex {
						go func() {
							stepexret <- p.executeBlock(r, rev)
						}()
					} else {
						panic("Focused PC doesnt exist")
					}
					select {
					case <-stepexret:
						running = 0
						break L1

					case pid := <-r.newproc:
						//if newproc is created first, its a call method, so another runonce is needed
						//maybe a dirty solution
						//resend pid change for later
						//no block
						go func() { r.newproc <- pid }()
					}
				}
				//otherwise run another ones once
				util.Unclog(r.runonce)
				r.runonce <- rev
			case pid := <-r.newproc:
				if pid == focus_tgt && pid != focus_now {
					focus_now = pid
					fmt.Printf("Debug >> Focus change -> %d\n", focus_now)
				}
			case c := <-r.termproc:
				if c.term == focus_now {
					focus_now = c.origin
					fmt.Printf("Debug >> Focus change %d -> %d\n", c.term, c.origin)
				}
			}
		case 0:
			//if not running
			select {
			case <-done:
				return
			case pid := <-r.newproc:
				if pid == focus_tgt {
					focus_now = pid
				}
			case c := <-r.termproc:
				if c.term == focus_now {
					focus_now = c.origin
				}
			case s := <-debugsym:
				switch s {
				case "\n":
					//run one step of focused proc
					util.Unclog(r.runclose)
					util.Unclog(r.runever)
					util.Unclog(r.rundone)
					running = 2
					//r.addrunPC(0,0,0) //only need to revive main pc cuz all its forks will be revived
					r.rundone <- true
				case "run\n":
					//enter run mode
					util.Unclog(r.runclose)
					util.Unclog(r.runever)
					r.runever <- rev
					running = 1
					r.addrunPC(0, 0, 0, nil) //only need to revive main pc cuz all its forks will be revived, given variables will not used anyways
					fmt.Print("Debug >> Running...\n")
				case "fwd\n":
					rev = false
					fmt.Print("Debug >> Forward mode set\n")
				case "bwd\n":
					rev = true
					fmt.Print("Debug >> Backward mode set\n")
				case "var\n":
					r.PrintSym()
				case "anim\n":
					r.PrintDag(true)
				case "dag\n":
					r.PrintDag(false)
				default:
					//set focus
					match := reg.FindStringSubmatch(s)
					if match != nil {
						i, er := strconv.ParseInt(match[1], 0, 0)
						checkerr(er)
						focus_tgt = int(i)
						fmt.Printf("Debug >> Focus changed to %d\n", i)
					} else {
						fmt.Print("Debug >> Unknown command\n")
					}
				}
			}
		}
	}
}

// DO NOT BLOCK
func newRuntime(file *[]string) *runtime {
	return &runtime{labels: *newLabels(),
		symtab:  *newSymtab(),
		instset: make([]instentry, 0),
		file:    file, dag: *newDag(),
		runonce:   make(chan bool, 1),
		rundone:   make(chan bool, 1),
		rundoner:  make(chan bool, 1),
		runever:   make(chan bool, 8),
		runclose:  make(chan bool, 8),
		dagupdate: make(chan bool, 8),
		newproc:   make(chan int, 8),
		termproc:  make(chan procchange, 8),
		exmap: make(map[pidandpc]string),
	}
}

func (r *runtime) addrun(re string, fwd func(*runtime, *pc, []string) int, bwd func(*runtime, *pc, []string) int) {
	reg, _ := regexp.Compile(re)
	r.instset = append(r.instset, instentry{reg, fwd, bwd})
}

func (r *runtime) evalexpr(p *pc, exp []string, rev bool) int {
	a, err := strconv.Atoi(exp[0])
	if err != nil {
		a = r.ReadSym(exp[0], p, rev)
	}
	if len(exp) >= 3 && len(exp[2]) != 0 {
		b, err := strconv.Atoi(exp[2])
		if err != nil {
			b = r.ReadSym(exp[2], p, rev)
		}
		switch exp[1] {
		case "+":
			return a + b
		case "-":
			return a - b
		case "^":
			return a ^ b
		case "*":
			return a * b
		case "/":
			return a / b
		case "%":
			return a % b
		case "<=":
			if a <= b {
				return 1
			}
			return 0
		case "<":
			if a < b {
				return 1
			}
			return 0
		case ">=":
			if a >= b {
				return 1
			}
			return 0
		case ">":
			if a > b {
				return 1
			}
			return 0
		case "==":
			if a == b {
				return 1
			}
			return 0
		case "!=":
			if a != b {
				return 1
			}
			return 0
		case "&&":
			if a != 0 && b != 0 {
				return 1
			}
			return 0
		case "||":
			if a != 0 || b != 0 {
				return 1
			}
			return 0
		}
	}
	return a
}

func (r *runtime) initInstset() {
	// x += a
	r.addrun(`^([\w\d$#.:\[\]]+)\s*([+\-^])=\s*([\w\d$#.:\[\]+\-*/!<=>&|%\(\) ]+)\s*$`, func(r *runtime, p *pc, arg []string) int {
		//fwd
		i := EvalExpr(arg[3],r,p,false)
		switch arg[2] {
		case "+":
			r.WriteSym(arg[1], r.ReadSym(arg[1], p, false)+i, p)
		case "-":
			r.WriteSym(arg[1], r.ReadSym(arg[1], p, false)-i, p)
		case "^":
			r.WriteSym(arg[1], r.ReadSym(arg[1], p, false)^i, p)
		}
		return 0
	},
		func(r *runtime, p *pc, arg []string) int {
			//bwd
			i := EvalExpr(arg[3], r,p,true)
			switch arg[2] {
			case "+":
				r.WriteSymRev(arg[1], r.ReadSym(arg[1], p, true)-i, p)
			case "-":
				r.WriteSymRev(arg[1], r.ReadSym(arg[1], p, true)+i, p)
			case "^":
				r.WriteSymRev(arg[1], r.ReadSym(arg[1], p, true)^i, p)
			}
			return 0
		})
	//print x
	r.addrun(`^print\s+([\w\d$#.:\[\]]+)$`, func(r *runtime, p *pc, arg []string) int {
		//fwd
		fmt.Printf(">>out: %s %d\n", arg[1], r.ReadSym(arg[1], p, false))
		return 0
	},
		func(r *runtime, p *pc, arg []string) int {
			//how do i undo print lol
			//use curses?
			fmt.Printf("<<out: %s %d\n", arg[1], r.ReadSym(arg[1], p, true))
			return 0
		})
	//skip
	r.addrun(`^skip`, func(r *runtime, p *pc, arg []string) int {
		//fwd
		return 0
	},
		func(r *runtime, p *pc, arg []string) int {
			//bwd
			return 0
		})
	//-> L
	r.addrun(`^->\s*([\w\d$#.:]+)$`, func(r *runtime, p *pc, arg []string) int {
		//fwd
		p.head = r.labels.GetComeFrom(arg[1])
		return 4
	},
		func(r *runtime, p *pc, arg []string) int {
			//bwd
			return 0
		})
	//L <-
	r.addrun(`^([\w\d$#.:]+)\s*<-$`, func(r *runtime, p *pc, arg []string) int {
		//fwd
		return 0
	},
		func(r *runtime, p *pc, arg []string) int {
			//bwd
			p.head = r.labels.GetGoto(arg[1])
			return 4
		})
	//a <=> b
	r.addrun(`^([\w\d$#.:\[\]]+)\s*<=>\s*([\w\d$#.:\[\]]+)$`, func(r *runtime, p *pc, arg []string) int {
		//fwd
		i := r.ReadSym(arg[1], p, false)
		r.WriteSym(arg[1], r.ReadSym(arg[2], p, false), p)
		r.WriteSym(arg[2], i, p)
		return 0
	},
		func(r *runtime, p *pc, arg []string) int {
			//bwd
			i := r.ReadSym(arg[1], p, true)
			r.WriteSymRev(arg[1], r.ReadSym(arg[2], p, true), p)
			r.WriteSymRev(arg[2], i, p)
			return 0
		})
	//a == b -> L1;L2
	r.addrun(`^([\w\d$#.:\[\]]+)\s*(?:([+\-*/!<=>&|%]+)\s*([\w\d$#.:\[\]]+))?\s*->\s*([\w\d$#.:]+)\s*;\s*([\w\d$#.:]+)\s*$`, func(r *runtime, p *pc, arg []string) int {
		//fwd
		var i int
		if len(arg) >= 5 {
			i = r.evalexpr(p, arg[1:4], false)
		} else {
			i = r.evalexpr(p, arg[1:2], false)
		}
		if i != 0 {
			p.head = r.labels.GetComeFrom(arg[4])
		} else {
			p.head = r.labels.GetComeFrom(arg[5])
		}

		return 4
	},
		func(r *runtime, p *pc, arg []string) int {
			//bwd
			if len(arg) >= 5 {
				_ = r.evalexpr(p, arg[1:4], true)
			} else {
				_ = r.evalexpr(p, arg[1:2], true)
			}
			return 0
		})
	r.addrun(`^([\w\d$#.:]+)\s*;\s*([\w\d$#.:]+)\s*<-\s*([\w\d$#.:\[\]]+)\s*(?:([+\-*/!<=>&|%]+)\s*([\w\d$#.:\[\]]+))?$`, func(r *runtime, p *pc, arg []string) int {
		//fwd
		_ = r.evalexpr(p, arg[3:], false)
		return 0
	},
		func(r *runtime, p *pc, arg []string) int {
			//bwd
			i := r.evalexpr(p, arg[3:], true)
			if i != 0 {
				p.head = r.labels.GetGoto(arg[1])
			} else {
				p.head = r.labels.GetGoto(arg[2])
			}

			return 4
		})
	r.addrun(`^begin\s+([\w\d$#.:]+)`, func(r *runtime, p *pc, arg []string) int {
		//fwd
		if !strings.HasPrefix(arg[1],"$"){
			p.stackdepth = append(p.stackdepth, make([]int, 0))
		}
		return 0
	}, func(r *runtime, p *pc, arg []string) int {
		//bwd
		if !strings.HasPrefix(arg[1],"$"){
			p.stackdepth = p.stackdepth[:len(p.stackdepth)-1]
		}
		if arg[1] == "main" {
			return 1
		}
		return 2
	})
	r.addrun(`^end\s+([\w\d$#.:]+)`, func(r *runtime, p *pc, arg []string) int {
		//fwd
		if !strings.HasPrefix(arg[1],"$"){
			p.stackdepth = p.stackdepth[:len(p.stackdepth)-1]
		}
		if arg[1] == "main" {
			return 1
		}
		return 2
	}, func(r *runtime, p *pc, arg []string) int {
		//bwd
		if !strings.HasPrefix(arg[1],"$"){
			p.stackdepth = append(p.stackdepth, make([]int, 0))
		}
		return 0
	})
	r.addrun(`^call\s+(.*)`, func(r *runtime, p *pc, arg []string) int {
		//arg[1] is l(,l)* and must be splited with "," and trim whitespace
		//pid is assigned in order written in source
		//fwd
		var wg sync.WaitGroup
		procnames := strings.Split(arg[1], ",")
		pids := r.addOrGetCallPid(p.pid, p.pc, len(procnames))
		suspendproc := make(chan bool, len(procnames)) //do not block
		for i, v := range procnames {
			wg.Add(1)
			v = strings.TrimSpace(v)
			head := r.GetBegin(v)
			//head will not be overwritten if the proc does exist
			r.addRunPCCall(pids[i], head, p.pid, p.stackdepth, &wg, suspendproc)
		}
		exmut.Unlock()
		//we do not need to consider getting proc reversed while waiting
		//upon getting reversed, proc of pid 0 will run execute() first, which will run this again if its forking for another procs, waking up other process
		wg.Wait()
		exmut.Lock()
		select {
		case <-suspendproc:
			//if proc is suspended, it needs to respawn hence this statement nedds to run again
			//giving value 3 so that executeOnce will not modify head
			return 3
		default:
			return 0
		}
	}, func(r *runtime, p *pc, arg []string) int {
		//bwd
		var wg sync.WaitGroup
		procnames := strings.Split(arg[1], ",")
		pids := r.addOrGetCallPid(p.pid, p.pc, len(procnames))
		suspendproc := make(chan bool, len(procnames))
		for i, v := range procnames {
			wg.Add(1)
			v = strings.TrimSpace(v)
			head := r.GetEnd(v)
			r.addRunPCCall(pids[i], head, p.pid, p.stackdepth, &wg, suspendproc)
		}
		exmut.Unlock()
		//we do not need to consider getting proc reversed while waiting
		wg.Wait()
		exmut.Lock()
		select {
		case <-suspendproc:
			//if proc is suspended, it needs to respawn hence this statement nedds to run again
			//giving value 3 so that executeOnce will not modify head
			return 3
		default:
			return 0
		}
	})
	r.addrun(`^indent (\d+)`, func(r *runtime, p *pc, arg []string) int {
		//fwd
		i,_ := strconv.Atoi(arg[1])
		if BLOCK_DEBUG{
			fmt.Print("bin"+p.getBlock()+"f\n")	
		}
		p.stackdepth[len(p.stackdepth)-1] = append(p.stackdepth[len(p.stackdepth)-1], i)
		if BLOCK_DEBUG{
			fmt.Print("bou"+p.getBlock()+"f\n")	
		}
		return 0
	}, func(r *runtime, p *pc, arg []string) int {
		//bwd
		i,_ := strconv.Atoi(arg[1])
		if BLOCK_DEBUG{
			fmt.Print("bin"+p.getBlock()+"f\n")	
		}
		s := p.stackdepth[len(p.stackdepth)-1]
		if i != s[len(s)-1]{
			panic("Indent conflict: P"+strconv.Itoa(p.pid)+", "+arg[1])
		}
		p.stackdepth[len(p.stackdepth)-1] = s[:len(s)-1]
		if BLOCK_DEBUG{
			fmt.Print("bou"+p.getBlock()+"f\n")	
		}
		return 0
	})
	r.addrun(`^unindent (\d+)`, func(r *runtime, p *pc, arg []string) int {
		//fwd
		i,_ := strconv.Atoi(arg[1])
		if BLOCK_DEBUG{
			fmt.Print("bin"+p.getBlock()+"f\n")	
		}
		s := p.stackdepth[len(p.stackdepth)-1]
		if i != s[len(s)-1]{
			panic("Unindent conflict: P"+strconv.Itoa(p.pid)+", "+arg[1])
		}
		p.stackdepth[len(p.stackdepth)-1] = s[:len(s)-1]
		if BLOCK_DEBUG{
			fmt.Print("bou"+p.getBlock()+"f\n")	
		}
		return 0
	}, func(r *runtime, p *pc, arg []string) int {
		//bwd
		i,_ := strconv.Atoi(arg[1])
		if BLOCK_DEBUG{
			fmt.Print("bin"+p.getBlock()+"f\n")	
		}
		p.stackdepth[len(p.stackdepth)-1] = append(p.stackdepth[len(p.stackdepth)-1], i)
		if BLOCK_DEBUG{
			fmt.Print("bou"+p.getBlock()+"f\n")	
		}
		return 0
	})
	r.addrun(`^set\s+([\w\d$#.:\[\]]+)\s+([\w\d$#.:\[\]]+)`, func(r *runtime, p *pc, arg []string) int {
		//fwd
		mloc := r.ReadSym("&"+arg[2],p,false)
		r.WriteSym("&"+arg[1],mloc,p)
		return 0
	}, func(r *runtime, p *pc, arg []string) int {
		//bwd
		r.ReadSym("&"+arg[2],p,true)
		r.WriteSymRev("&"+arg[1],0,p)
		return 0
	})
	r.addrun(`^unset\s+([\w\d$#.:\[\]]+)\s+([\w\d$#.:\[\]]+)`, func(r *runtime, p *pc, arg []string) int {
		//fwd
		r.ReadSym("&"+arg[2],p,false)
		r.WriteSym("&"+arg[1],0,p)
		return 0
	}, func(r *runtime, p *pc, arg []string) int {
		//bwd
		mloc := r.ReadSym("&"+arg[2],p,true)
		r.WriteSymRev("&"+arg[1],mloc,p)
		return 0
	})
	r.addrun(`^V\s*([\w\d$#.:\[\]]+)`, func(r *runtime, p *pc, arg []string) int {
		//fwd
		for r.ReadSym(arg[1],p,false) != 0{
			if SEM_DEBUG{
				fmt.Printf("sem:P%d,%d Waiting for %s=0\n",p.pid,p.pc,arg[1])
			}
			r.WaitSem(arg[1])
		}
		if SEM_DEBUG{
			fmt.Printf("sem:P%d,%d Gained %s=0->1\n",p.pid,p.pc,arg[1])
		}
		r.WriteSym(arg[1],1,p)
		r.NotifySem(arg[1])
		return 0
	}, func(r *runtime, p *pc, arg []string) int {
		//bwd
		for r.ReadSym(arg[1],p,true) != 1{
			if SEM_DEBUG{
				fmt.Printf("sem:P%d,%d Waiting for %s=1\n",p.pid,p.pc,arg[1])
			}
			r.WaitSem(arg[1])
		}
		if SEM_DEBUG{
			fmt.Printf("sem:P%d,%d Gained %s=1->0\n",p.pid,p.pc,arg[1])
		}
		r.WriteSymRev(arg[1],0,p)
		r.NotifySem(arg[1])
		return 0
	})
	r.addrun(`^P\s*([\w\d$#.:\[\]]+)`, func(r *runtime, p *pc, arg []string) int {
		//fwd
		for r.ReadSym(arg[1],p,false) != 1{
			if SEM_DEBUG{
				fmt.Printf("sem:P%d,%d Waiting for %s=1\n",p.pid,p.pc,arg[1])
			}
			r.WaitSem(arg[1])
		}
		if SEM_DEBUG{
			fmt.Printf("sem:P%d,%d Gained %s=1->0\n",p.pid,p.pc,arg[1])
		}
		r.WriteSym(arg[1],0,p)
		r.NotifySem(arg[1])
		return 0
	}, func(r *runtime, p *pc, arg []string) int {
		//bwd
		for r.ReadSym(arg[1],p,true) != 0{
			if SEM_DEBUG{
				fmt.Printf("sem:P%d,%d Waiting for %s=0\n",p.pid,p.pc,arg[1])
			}
			r.WaitSem(arg[1])
		}
		if SEM_DEBUG{
			fmt.Printf("sem:P%d,%d Gained %s=0->1\n",p.pid,p.pc,arg[1])
		}
		r.WriteSymRev(arg[1],1,p)
		r.NotifySem(arg[1])
		return 0
	})
}
