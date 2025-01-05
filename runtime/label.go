package main

import "strconv"

type labels struct {
	gotomap  map[string]int
	comemap  map[string]int
	beginmap map[string]int
	endmap   map[string]int
	tmplabel int
}

func newLabels() *labels {
	l := labels{gotomap: make(map[string]int),
		comemap:  make(map[string]int),
		beginmap: make(map[string]int),
		endmap:   make(map[string]int)}
	return &l
}

func (labels *labels) GetGoto(labelname string) int {
	val, ex := labels.gotomap[labelname]
	if ex {
		return val
	}
	panic("Label not found")
}
func (labels *labels) GetComeFrom(labelname string) int {
	val, ex := labels.comemap[labelname]
	if ex {
		return val
	}
	panic("Label not found")
}
func (labels *labels) GetBegin(labelname string) int {
	val, ex := labels.beginmap[labelname]
	if ex {
		return val
	}
	panic("Label not found")
}
func (labels *labels) GetEnd(labelname string) int {
	val, ex := labels.endmap[labelname]
	if ex {
		return val
	}
	panic("Label not found")
}
func (labels *labels) AddGoto(labelname string, lineno int) {
	labels.gotomap[labelname] = lineno
}
func (labels *labels) AddComeFrom(labelname string, lineno int) {
	labels.comemap[labelname] = lineno
}
func (labels *labels) AddBegin(labelname string, lineno int) {
	labels.beginmap[labelname] = lineno
}
func (labels *labels) AddEnd(labelname string, lineno int) {
	labels.endmap[labelname] = lineno
}
func (labels *labels) RegisterNewLabel(lineno int) string {
	s := "_" + strconv.Itoa(labels.tmplabel)
	labels.AddGoto(s,lineno)
	labels.AddComeFrom(s,lineno+1)
	labels.tmplabel++
	return s
}
