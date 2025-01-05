package main

import (
	"bytes"
	"context"
	"fmt"
	"image"
	"image/color/palette"
	"image/draw"
	"image/gif"
	"os"
	"strconv"
	"sync"

	"github.com/goccy/go-graphviz"
	"github.com/goccy/go-graphviz/cgraph"
)

type dagedge struct {
	pid     int
	pc      int
	wt      bool
	varname string
}

type dag struct {
	outedgectr  [][]int
	incedges    [][][]dagedge
	callpids    sync.Map //map[pidandpc][]int //stores called procs pid so that it can be reversed
	gviz        *graphviz.Graphviz
	gvcontext *context.Context
	exechistory []exhistory
}

type pidandpc struct {
	pid int
	pc  int
}
type exhistory struct {
	pid  int
	pc   int
	exec string
	rev  bool
}

func newDag() *dag {
	ctx := context.Background()
	gv,_ := graphviz.New(ctx)
	gv.SetLayout(graphviz.DOT)
	return &dag{outedgectr: make([][]int, 1), incedges: make([][][]dagedge, 1), callpids: sync.Map{}, gviz: gv, gvcontext: &ctx}
}

//Reminder: you don't have to create ptr to slices to avoid memcopy, since slice internally contains ptr to array

func (r *runtime) addEdge(pid int, pc int, varname string, wt bool, dstpid int, dstpc int) {
	if pid == dstpid && pc > dstpc {
		panic("It should not happen")
	}
	if pid == dstpid && pc == dstpc {
		//inheriting value from iteself result in no change
		return
	}
	for dstpid >= len(r.dag.incedges) {
		r.dag.incedges = append(r.dag.incedges, make([][]dagedge, 0, 1))
	}
	for dstpc >= len(r.dag.incedges[dstpid]) {
		r.dag.incedges[dstpid] = append(r.dag.incedges[dstpid], make([]dagedge, 0, 1))
	}
	for _, edge := range r.dag.incedges[dstpid][dstpc] {
		if edge.pid == pid && edge.pc == pc && edge.varname == varname && edge.wt == wt {
			return
		}
	}
	r.dag.incedges[dstpid][dstpc] = append(r.dag.incedges[dstpid][dstpc], dagedge{pid, pc, wt, varname})
	if DAG_DEBUG{
		fmt.Printf("    Dag added (%d,%d,%s,%s)->[%d,%d]\n", pid, pc, varname, func() string {
			if wt {
				return "wt"
			}
			return "rd"
		}(), dstpid, dstpc)
	}
	// L1:
	if pid == -1 && pc == -1 {
		return
	}
	for pid >= len(r.dag.outedgectr) {
		r.dag.outedgectr = append(r.dag.outedgectr, make([]int, 1))
	}
	for pc >= len(r.dag.outedgectr[pid]) {
		r.dag.outedgectr[pid] = append(r.dag.outedgectr[pid], 0)
	}
	r.dag.outedgectr[pid][pc]++
}

func (r *runtime) addOrGetCallPid(pid int, pc int, size int) []int {
	basesize := len(r.pcs)
	l := make([]int, 0, size)
	for i := range size {
		l = append(l, i+basesize)
	}
	v, _ := r.dag.callpids.LoadOrStore(pidandpc{pid, pc}, l)
	return v.([]int)
}

func (r *runtime) runModifyDagRev(pid int) {
	//decrement outedgectr of incoming nodes
	pc, _ := r.getPC(pid)
	if pid >= len(r.dag.incedges) {
		return
	}
	if pc.pc >= len(r.dag.incedges[pid]) {
		return
	}
	for _, v := range r.dag.incedges[pid][pc.pc] {
		if v.pid == -1 && v.pc == -1 {
			continue
		}
		if v.pid >= len(r.dag.outedgectr) {
			continue
		}
		if v.pc >= len(r.dag.outedgectr[v.pid]) {
			continue
		}
		r.dag.outedgectr[v.pid][v.pc]--
		if r.dag.outedgectr[v.pid][v.pc] < 0 {
			panic("BUG")
		}
	}

}

func (r *runtime) isRunnable(pid int, rev bool) bool {
	if rev {
		//no outgoing edges
		pc, _ := r.getPC(pid)
		//ITS REVERSE SO NEXT EXECUTED TARGET IS PC-1 NOT PC
		if pc.pc-1 < 0 {
			return false
		}
		if pid >= len(r.dag.outedgectr) {
			return true
		}
		if pc.pc-1 >= len(r.dag.outedgectr[pid]) {
			return true
		}
		return r.dag.outedgectr[pid][pc.pc-1] == 0
	} else {
		pc, _ := r.getPC(pid)
		//its obviously runnable if dag entry does not exist
		if pid >= len(r.dag.incedges) {
			return true
		}
		if pc.pc >= len(r.dag.incedges[pid]) {
			return true
		}
		//none of incoming nodes are inactive (will not create inactive nodes with outgoing edge violation)
		for _, e := range r.dag.incedges[pid][pc.pc] {
			tpc, ex := r.getPC(e.pid)
			if ex {
				//target procs pc being higher than nodes = its already executed thus active
				if e.pc >= tpc.pc {
					return false
				}
			}
			//if pc is nil, then it does not exist so no dag violation (i think it should never happen because we dont delete pc stuct but whatever)
		}
	}
	return true
}
func (r *runtime) PrintDag(animate bool) {
	fmt.Print("Constructing graph...\n")
	files := make([]*image.Paletted, 0, len(r.dag.exechistory))
	//construct fill dag image first
	graph, _ := r.dag.gviz.Graph()
	if SEQ_DAG {
		graph.SetRankSeparator(0.02)
	}
	subgraphs := make([]*cgraph.Graph, 0)
	bot, _ := graph.CreateNodeByName("BOT")
	if SEQ_DAG {
		for pid := range r.pcs {
			sg,_ := graph.CreateSubGraphByName("P"+strconv.Itoa(pid))
			sg.SetBackgroundColor("gray")
			sg.SetStyle(cgraph.SolidGraphStyle)
			subgraphs = append(subgraphs, sg)
		}
	}
	for pid, v := range r.dag.incedges {
		for pc, edges := range v {
			p, ex := r.getPC(pid)
			c := 0
			if pid < len(r.dag.outedgectr) {
				if pc < len(r.dag.outedgectr[pid]) {
					c = r.dag.outedgectr[pid][pc]
				}
			}
			if len(edges) != 0 || c != 0 {
				var gnode *cgraph.Node
				if SEQ_DAG {
					gnode, _ = subgraphs[pid].NodeByName("(" + strconv.Itoa(pid) + "," + strconv.Itoa(pc) + ")")
				} else {
					gnode, _ = graph.NodeByName("(" + strconv.Itoa(pid) + "," + strconv.Itoa(pc) + ")")
				}
				if gnode == nil {
					if SEQ_DAG {
						gnode, _ = subgraphs[pid].CreateNodeByName("(" + strconv.Itoa(pid) + "," + strconv.Itoa(pc) + ")")
					} else {
						gnode, _ = graph.CreateNodeByName("(" + strconv.Itoa(pid) + "," + strconv.Itoa(pc) + ")")
					}
				}
				act := true
				if animate {
					gnode.SetStyle("invis")
				} else {
					if !ex {
						act = false
					} else if p.pc <= pc {
						act = false
					}
					if !act {
						gnode.SetColor("gray")
					}
				}
				//render invis edges that connect to previous pc of same proc
				if SEQ_DAG {
					var pnode *cgraph.Node
					pnode, _ = subgraphs[pid].NodeByName("(" + strconv.Itoa(pid) + "," + strconv.Itoa(pc-1) + ")")
					if pnode != nil {
						pedge, _ := graph.CreateEdgeByName("", pnode, gnode)
						pedge.SetWeight(100000)
						pedge.SetStyle("invis")
					}
				}
				//render all other incoming edges
			L1:
				for _, e := range edges {
					if !e.wt {
						for _, ae := range edges {
							if ae.pid == e.pid && ae.pc == e.pc && ae.varname == e.varname && ae.wt {
								continue L1
							}
						}
					}
					var tnode *cgraph.Node
					if e.pid == -1 && e.pc == -1 {
						tnode = bot
					} else {
						if SEQ_DAG {
							tnode, _ = subgraphs[e.pid].NodeByName("(" + strconv.Itoa(e.pid) + "," + strconv.Itoa(e.pc) + ")")
						} else {
							tnode, _ = graph.NodeByName("(" + strconv.Itoa(e.pid) + "," + strconv.Itoa(e.pc) + ")")
						}
						if tnode == nil {
							if SEQ_DAG {
								tnode, _ = subgraphs[e.pid].CreateNodeByName("(" + strconv.Itoa(e.pid) + "," + strconv.Itoa(e.pc) + ")")
							} else {
								tnode, _ = graph.CreateNodeByName("(" + strconv.Itoa(e.pid) + "," + strconv.Itoa(e.pc) + ")")
							}
							gnode.SetGroup(strconv.Itoa(e.pid))
						}
					}
					if animate {
						if e.pid != -1 || e.pc != -1 {
							tnode.SetStyle("invis")
						}
					} else {
						tp, ex := r.getPC(e.pid)
						act := true
						if !ex {
							act = false
						} else if tp.pc <= e.pc {
							act = false
						}
						if e.pid == -1 && e.pc == -1 {
							act = true
						}
						if !act {
							tnode.SetColor("gray")
						}
					}
					gedge, _ := graph.CreateEdgeByName("(" + strconv.Itoa(e.pid) + "," + strconv.Itoa(e.pc) + ")->(" + strconv.Itoa(pid) + "," + strconv.Itoa(pc) + ")", tnode, gnode)
					gedge.SetLabel(e.varname)
					if !e.wt {
						gedge.SetStyle("dashed")
					}
					if animate {
						gedge.SetColor("white")
						gedge.SetFontColor("white")
					} else {
						if !act {
							gedge.SetColor("gray")
						}
					}
				}
			}
		}
	}
	if !animate {
		fmt.Print("Rendering...\n")
		var buf bytes.Buffer
		r.dag.gviz.Render(*r.dag.gvcontext, graph, "dot", &buf)
		fmt.Println(buf.String())
		e := r.dag.gviz.RenderFilename(*r.dag.gvcontext,graph, graphviz.PNG, "dag.png")
		if e != nil{
			fmt.Print(e)
		}
		
		fmt.Printf("Done!\n")
		return
	}
	pcmax := make(map[int]int)
	pccur := make(map[int]int)
	instnode, _ := graph.CreateNodeByName("inst")
	instnode.SetShape(cgraph.BoxShape)
	for imindex, p := range r.dag.exechistory {
		fmt.Printf("Drawing DAG... (%d/%d)\n", imindex+1, len(r.dag.exechistory))
		instnode.SetLabel("(" + strconv.Itoa(p.pid) + "," + strconv.Itoa(p.pc) + ")" + "\n" + p.exec)
		v, ex := pcmax[p.pid]
		if !ex {
			pcmax[p.pid] = p.pc
		} else if p.pc > v {
			pcmax[p.pid] = p.pc
		}
		pccur[p.pid] = p.pc
		for npid, mpc := range pcmax {
			for npc := range mpc + 1 {
				var gnode *cgraph.Node
				if SEQ_DAG {
					gnode, _ = subgraphs[npid].NodeByName("(" + strconv.Itoa(npid) + "," + strconv.Itoa(npc) + ")")
				} else {
					gnode, _ = graph.NodeByName("(" + strconv.Itoa(npid) + "," + strconv.Itoa(npc) + ")")
				}
				if gnode != nil {
					c, ex := pccur[npid]
					if !ex {
						c = 0
					}
					if (npc > c && !p.rev) || (npc >= c && p.rev) {
						gnode.SetStyle("")
						gnode.SetColor("gray")
						gnode.SetFontColor("gray")
					} else {
						gnode.SetStyle("")
						gnode.SetColor("")
						gnode.SetFontColor("")
					}
					e,_ := graph.FirstIn(gnode)
					for e != nil {
						if (npc > c && !p.rev) || (npc >= c && p.rev) {
							e.SetColor("gray")
							e.SetFontColor("gray")
						} else {
							e.SetColor("")
							e.SetFontColor("")
						}
						e,_ = graph.NextIn(e)
					}

				}
			}
		}
		im, _ := r.dag.gviz.RenderImage(*r.dag.gvcontext,graph)
		bounds := im.Bounds()
		pl := image.NewPaletted(bounds, palette.WebSafe)
		draw.Draw(pl, bounds, im, bounds.Min, draw.Src)
		files = append(files, pl)
	}
	delays := make([]int, 0, len(r.dag.exechistory))
	for _ = range len(r.dag.exechistory) {
		delays = append(delays, 50)
	}
	f, _ := os.Create("dag.gif")
	defer f.Close()
	gif.EncodeAll(f, &gif.GIF{
		Image: files,
		Delay: delays,
	})
	fmt.Print("Done!\n")
}
