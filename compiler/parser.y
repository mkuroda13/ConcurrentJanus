%{
package main

import (
	"bufio"
	"flag"
	"fmt"
	"os"
	"regexp"
	"strconv"
	"slices"
	"strings"
)
var cmp *compiler
var prep = true
%}

%union {
	num int
	ident string
	varid string
	varids []string
	ary aryentry
}
%token <num> NUM
%token <ident> IDENT
%token PLUS MINUS XOR MULT DIV MOD AND OR BITAND BITOR LEQ GEQ NEQ EQ LES GRT LSB RSB LCB RCB COMMA LPR RPR
%token PROCEDURE MAIN INT IF THEN ELSE FI FROM DO LOOP UNTIL LOCAL DELOCAL CALL UNCALL PAR RAP SKIP BEGIN END P V
%type <varid> variable expr expr2 expr3 expr4 expr5 expr6 lab reclab arrentry

%%
prog : pmain procs

procs : proc procs
|

pmain : PROCEDURE MAIN LPR RPR 
{	
	if prep{
		cmp.addProc("main")
	} else {
		cmp.beginProc("main")
		cmp.exec("begin main")
	}
}
mainblock
{
	if !prep{
		cmp.exec("end main")
	}
	cmp.endProc()
}

mainblock : LCB
{
	if !prep{
		cmp.exec("indent "+ cmp.getNextMod())
	}
	cmp.indent()
}
globvardecls statements RCB
{
	if !prep{
		cmp.exec("unindent "+cmp.getCurrentMod())
	}
	cmp.unindent()
}
globvardecls : globvardecl globvardecls
|

globvardecl : INT IDENT
{
	if !prep{
		cmp.exec("#"+$2 + " += 0")
	}
}
			| INT IDENT LSB variable RSB
{
	if !prep{
		cmp.exec("#"+$2 + "["+ $4 + "]"+ " += 0")
	}
}

proc : PROCEDURE IDENT 
{
	if prep{
		cmp.addProc($2)
	} else {
		cmp.beginProc($2)
		cmp.exec("begin "+$2)
	}
}
LPR argdecls RPR pblock
{
	if !prep{
		cmp.exec("end "+$2)
	}
	cmp.endProc()
}

pblock : LCB
{
	if !prep{
		cmp.exec("indent "+ cmp.getNextMod())
	}
	cmp.indent()
}
statements
{
	if !prep{
		cmp.exec("unindent "+cmp.getCurrentMod())
	}
	cmp.unindent()
}
RCB

argdecls: argdecl argdeclmore
		  |
		  

argdeclmore: COMMA argdecl argdeclmore
		   |

argdecl: INT IDENT
{
	if prep{
		cmp.addProcArg($2)
	}
}
		| INT IDENT LSB RSB
{
	if prep{
		cmp.addProcArg($2)
	}
}

block : LCB
{
	if !prep{
		cmp.exec("indent "+ cmp.getNextMod())
	}
	cmp.indent()
}
statements
{
	if !prep{
		cmp.exec("unindent "+cmp.getCurrentMod())
	}
	cmp.unindent()
}
RCB
| local_block

statements : statement statements
|

statement : assign_statement
			| arrassign_statement
			| if_statement
			| loop_statement
			| call_statement
			| par_statement
			| SKIP
			| block
			| v_statement
			| p_statement

assign_statement : IDENT PLUS EQ
{
	if !prep {
		cmp.recordToken()
	}
}
	expr
{
	if !prep{
		cmp.exec($1+" += " + cmp.getRecordedToken())
	}

}
	| IDENT MINUS EQ
{
	if !prep {
		cmp.recordToken()
	}
}
	expr
{
	if !prep{
		cmp.exec($1+" -= " + cmp.getRecordedToken())
	}

}
	| IDENT XOR EQ
{
	if !prep {
		cmp.recordToken()
	}
}
		expr
{
	if !prep{
		cmp.exec($1+" ^= " + cmp.getRecordedToken())
	}

}
arrentry : IDENT LSB reclab
{
	if !prep {
		cmp.beginRecord($3)
	}
}
expr RSB
{
	if !prep {
		cmp.endRecord($3)
		$$ = $1+"["+$5+"]"
	}
}
arrassign_statement : arrentry PLUS EQ
{
	if !prep {
		cmp.recordToken()
	}
}
expr
{
	if !prep{
		cmp.exec($1+" += " + cmp.getRecordedToken())
	}

}
| arrentry MINUS EQ
{
	if !prep {
		cmp.recordToken()
	}
}
expr
{
	if !prep{
		cmp.exec($1+" -= " + cmp.getRecordedToken())
	}

}
| arrentry XOR EQ
{
	if !prep {
		cmp.recordToken()
	}
}
expr
{
	if !prep{
		cmp.exec($1+" ^= " + cmp.getRecordedToken())
	}

}

if_statement : IF lab lab lab lab reclab reclab
{
	if !prep {
		cmp.beginRecord($6)
	}
}
expr
{
	if !prep{
		cmp.endRecord($6)
		cmp.execEarlyRecord($6)
		cmp.exec($9 + " -> " + $2 + ";" +$3)
		cmp.exec($2 + " <-")
		cmp.execLateRecord($6)
	}
}
THEN statements
{
	if !prep{
		cmp.execEarlyRecord($7)
		cmp.exec("-> " + $4)
		cmp.exec($3 + " <-")
		cmp.execLateRecord($6)
	}
}
ELSE statements
{
	if !prep{
		cmp.execEarlyRecord($7)
		cmp.exec("-> " + $5)
		cmp.beginRecord($7)
	}
}
FI expr
{
	if !prep{
		cmp.endRecord($7)
		cmp.exec($4 + ";" + $5 + " <- " + $18)
		cmp.execLateRecord($7)
	}
}

lab : 
{
	if !prep{
		$$ = cmp.getLabel()
	}
}

loop_statement : FROM lab lab lab lab lab reclab reclab
{
	if !prep {
		cmp.beginRecord($7)
	}
}
expr
{
	if !prep{
		cmp.endRecord($7)
		cmp.execEarlyRecord($7)
		cmp.exec("-> " + $2)
		cmp.exec($2 + ";" +$6 + " <- "+$10)
		cmp.execLateRecord($7)
	}
}
DO block 
{
	if !prep{
		cmp.exec("-> " + $3)
		cmp.exec($5 +" <-")
		cmp.execLateRecord($8)
	}
}
LOOP block UNTIL 
{
	if !prep{
		cmp.execEarlyRecord($7)
		cmp.exec("-> " + $6)
		cmp.exec($3 + " <-")
		cmp.beginRecord($8)
	}
}
expr
{
	if !prep{
		cmp.endRecord($8)
		cmp.execEarlyRecord($8)
		cmp.exec($19 + " -> "+$4 + ";" + $5 )
		cmp.exec($4 + " <-")
		cmp.execLateRecord($8)
	}
}

local_block: LCB
{
	if !prep{
		cmp.exec("indent "+ cmp.getNextMod())
	}
	cmp.indent()
}
LOCAL INT IDENT EQ reclab reclab
{
	if !prep{
		cmp.beginRecord($7)
	}
}
expr
{
	if !prep{
		cmp.endRecord($7)
		cmp.execEarlyRecord($7)
		cmp.exec("$"+$5+" += "+$10)
		cmp.execLateRecord($7)
	}
}
statements DELOCAL INT IDENT EQ 
{
	if !prep{
		cmp.beginRecord($8)
	}
}
expr
{
	if !prep {
		cmp.endRecord($8)
		cmp.execEarlyRecord($8)
		cmp.exec("$"+$15+" -= " + $18)
		cmp.execLateRecord($8)
		cmp.exec("unindent "+cmp.getCurrentMod())
	}
	cmp.unindent()
}
RCB

call_statement: CALL IDENT reclab
{
	if !prep{
		cmp.setCallingProc($2)
		cmp.beginRecord($3)
		cmp.argindex = 0	
	}
}
LPR args RPR
{
	if !prep {
		cmp.endRecord($3)
		cmp.argindex = 0
		cmp.execEarlyRecord($3)
		cmp.exec("call " + $2)
		cmp.execLateRecord($3)
	}
}

par_statement: PAR par_block par_more RAP
{
	if !prep{
		s := ""
		for i := range cmp.getParCount()+1{
			if i != 0{
				s += ","
			}
			s += " "
			s += "$"+cmp.getBlockId()+"."+strconv.Itoa(i)
		}
		cmp.exec("call"+s)
	}
}
par_more: COMMA par_block par_more
		|
		

par_block :
{
	if prep{
		cmp.addProc("$"+cmp.getBlockId()+"."+cmp.getNextMod())
	}
	if !prep{
		cmp.beginProc("$"+cmp.getBlockId()+"."+cmp.getNextMod())
		cmp.exec("begin $"+cmp.getBlockId()+"."+cmp.getNextMod())
	}
}
block
{
	if !prep{
		cmp.exec("end $"+cmp.getBlockId()+"."+cmp.getPrevNextMod())
	}
	cmp.endProc()
}

args: arg argmore
	|
	

argmore: COMMA arg argmore
		|

arg: IDENT
{
	if !prep {
		i := cmp.getProcArg()
		cmp.exec("set $"+i + ":" + cmp.getCallingProcId() + " " + $1)
		cmp.unexec("unset $"+i + ":" + cmp.getCallingProcId() + " " + $1)
	}
}

v_statement : V IDENT
{
	if !prep {
		cmp.exec("V "+$2)
	}
}
p_statement : P IDENT
{
	if !prep {
		cmp.exec("P "+$2)
	}
}

reclab :
{
	 $$ = cmp.getRec()
}

expr : expr2
{
	$$ = $1
}
		| expr OR expr2
		{
			if !prep {
				tmp := cmp.getTmp()
				cmp.exec(tmp + " += " + $1 + " ||" + $3)
				cmp.exec(tmp + " -= " + $1 + " ||" + $3)
				$$ = tmp
			}
		}
expr2 : expr3
{
	$$ = $1
}
		| expr2 AND expr3
		{
			if !prep{
				tmp := cmp.getTmp()
				cmp.exec(tmp + " += " + $1 + " && " + $3)
				cmp.unexec(tmp + " -= " + $1 + " && " + $3)
				$$ = tmp
			}
		}

expr3 : expr4
{
	$$ = $1
}
		| expr3 LEQ expr4
		{
			if !prep{
				tmp := cmp.getTmp()
				cmp.exec(tmp + " += " + $1 + " <= " + $3)
				cmp.unexec(tmp + " -= " + $1 + " <= " + $3)
				$$ = tmp
			}
		}
		| expr3 GEQ expr4
		{
			if !prep{
				tmp := cmp.getTmp()
				cmp.exec(tmp + " += " + $1 + " >= " + $3)
				cmp.unexec(tmp + " -= " + $1 + " >= " + $3)
				$$ = tmp
			}
		}
		| expr3 EQ expr4
		{
			if !prep{
				tmp := cmp.getTmp()
				cmp.exec(tmp + " += " + $1 + " == " + $3)
				cmp.unexec(tmp + " -= " + $1 + " == " + $3)
				$$ = tmp
			}
		}
		| expr3 NEQ expr4
		{
			if !prep{
				tmp := cmp.getTmp()
				cmp.exec(tmp + " += " + $1 + " != " + $3)
				cmp.unexec(tmp + " -= " + $1 + " != " + $3)
				$$ = tmp
			}
		}
		| expr3 LES expr4
		{
			if !prep{
				tmp := cmp.getTmp()
				cmp.exec(tmp + " += " + $1 + " < " + $3)
				cmp.unexec(tmp + " -= " + $1 + " < " + $3)
				$$ = tmp
			}
		}
		| expr3 GRT expr4
		{
			if !prep{
				tmp := cmp.getTmp()
				cmp.exec(tmp + " += " + $1 + " > " + $3)
				cmp.unexec(tmp + " -= " + $1 + " > " + $3)
				$$ = tmp
			}
		}
expr4 : expr5
{
	$$ = $1
}
		| expr4 PLUS expr5
		{
			if !prep{
				tmp := cmp.getTmp()
				cmp.exec(tmp + " += " + $1 + " + " + $3)
				cmp.unexec(tmp + " -= " + $1 + " + " + $3)
				$$ = tmp
			}
		}
		| expr4 MINUS expr5
		{
			if !prep{
				tmp := cmp.getTmp()
				cmp.exec(tmp + " += " + $1 + " - " + $3)
				cmp.unexec(tmp + " -= " + $1 + " - " + $3)
				$$ = tmp
			}
		}
		| expr4 BITOR expr5
		| expr4 XOR expr5
		{
			if !prep{
				tmp := cmp.getTmp()
				cmp.exec(tmp + " += " + $1 + " ^ " + $3)
				cmp.unexec(tmp + " -= " + $1 + " ^ " + $3)
				$$ = tmp
			}
		}
expr5 : expr6
{
	$$ = $1
}
		| expr5 MULT expr6
		{
			if !prep{
				tmp := cmp.getTmp()
				cmp.exec(tmp + " += " + $1 + " * " + $3)
				cmp.unexec(tmp + " -= " + $1 + " * " + $3)
				$$ = tmp
			}
		}
		| expr5 DIV expr6
		{
			if !prep{
				tmp := cmp.getTmp()
				cmp.exec(tmp + " += " + $1 + " / " + $3)
				cmp.unexec(tmp + " -= " + $1 + " / " + $3)
				$$ = tmp
			}
		}
		| expr5 MOD expr6
		{
			if !prep{
				tmp := cmp.getTmp()
				cmp.exec(tmp + " += " + $1 + " % " + $3)
				cmp.unexec(tmp + " -= " + $1 + " % " + $3)
				$$ = tmp
			}
		}
		| expr5 BITAND expr6

expr6 : variable
{
	$$ = $1
}
		| LPR expr RPR
{
	$$ = $2
}

variable : NUM
{
	if !prep{
		$$ = strconv.Itoa($1)
	}
}
		 | IDENT
{
	if !prep{
		$$ = $1
	}	
}
		| IDENT LSB expr RSB
{
	if !prep{
		$$ = $1 + "[" + $3 + "]"
	}	
}


%%

type aryentry struct {
	val string
	lab string
}

//yylval of type parserSymType provides
//yylval.<tokenname>

//Extremely dirty lexer
type token struct{
	reg *regexp.Regexp
	process func(match string, yylval *parserSymType) int
}


type compiler struct{
	stackdepth []int
	tmpindex int
	labelindex int
	output map[string]string
	currentproc []string
	callingproc string
	procid map[string]int //fib -> 1 (its block id)
	procargs map[string][]string // fib.0.0 -> [n,r]
	argindex int
	recindex int
	tokenrec string
	dorectoken bool
	prevtoken string
	currentrecord string
	earlyexec map[string]string
	lateexec map[string]string
}

func newCompiler() *compiler{
	s := make([]int,1,1)
	s[0] = -1
	return &compiler{s,0,0,make(map[string]string),make([]string,0),"",make(map[string]int),make(map[string][]string),0,0,"",false,"","",make(map[string]string),make(map[string]string)}
}

func (c *compiler) getLabel() string{
	t := c.labelindex
	c.labelindex++
	return "l"+strconv.Itoa(t)
}

func (c *compiler) getTmp() string{
	t := c.tmpindex
	c.tmpindex++
	return "$tmp"+strconv.Itoa(t)
}
func (c *compiler) getBlockId() string{
	name := ""
	for i := range len(c.stackdepth)-1{
		if i != 0 {
			name += "."
		}
		name += strconv.Itoa(c.stackdepth[i])
	}
	return name
}
func (c *compiler) getIdMod() string{
	name := ""
	for i := range len(c.stackdepth)-1{
		name += "."
		name += strconv.Itoa(c.stackdepth[i])
	}
	return name
}
func (c *compiler) getRec() string {
	t := c.recindex
	c.recindex++
	return "rec"+strconv.Itoa(t)
}
func (c *compiler) indent(){
	//increment last(used to be shadow) & append new shadow as -1
	c.stackdepth[len(c.stackdepth)-1]++
	c.stackdepth = append(c.stackdepth,-1)
}
func (c *compiler) unindent(){
	//delete one shadow (thus making it one shorter) 
	c.stackdepth = c.stackdepth[:len(c.stackdepth)-1]
}
func (c *compiler) exec(s string){
	if c.currentrecord != "" {
		c.earlyexec[c.currentrecord] += s
		c.earlyexec[c.currentrecord] += "\n"
	} else if !c.dorectoken{
		c.output[c.currentproc[len(c.currentproc)-1]] += s
		c.output[c.currentproc[len(c.currentproc)-1]] += "\n"
	}
}
//same as exec but recorded on lateexec rather than earlyexec
func (c *compiler) unexec(s string){
	if c.currentrecord != ""{
		c.lateexec[c.currentrecord] += s
		c.lateexec[c.currentrecord] += "\n"
	} else if !c.dorectoken{
		c.output[c.currentproc[len(c.currentproc)-1]] += s
		c.output[c.currentproc[len(c.currentproc)-1]] += "\n"
	}
}

func (c *compiler) addProc(name string){
	s := name+c.getIdMod()
	c.procid[s] = c.stackdepth[len(c.stackdepth)-1]+1 //nextmod
	c.procargs[s] = make([]string,0)
	c.output[s] = ""
	c.beginProc(name)
}
func (c *compiler) addProcArg(arg string){
	c.procargs[c.currentproc[len(c.currentproc)-1]] = append(c.procargs[c.currentproc[len(c.currentproc)-1]],arg)
}
func (c *compiler) beginProc(name string){
	c.currentproc = append(c.currentproc,name+c.getIdMod())
}
func (c *compiler) endProc(){
	c.currentproc = c.currentproc[:len(c.currentproc)-1]
}
func (c *compiler) setCallingProc(name string){
	c.callingproc = name
}
func (c *compiler) getProcArg() string {
	s := c.procargs[c.callingproc][c.argindex]
	c.argindex++
	return s
}
func (c *compiler) getCallingProcId() string {
	return strconv.Itoa(c.procid[c.callingproc])
}
func (c *compiler) resetArgIndex(){
	c.argindex = 0
}
func (c *compiler) getNextMod()string{
	return strconv.Itoa(c.stackdepth[len(c.stackdepth)-1]+1)
}
func (c *compiler) getPrevNextMod()string{
	return strconv.Itoa(c.stackdepth[len(c.stackdepth)-1])
}
func (c *compiler) getCurrentMod()string{
	return strconv.Itoa(c.stackdepth[len(c.stackdepth)-2])
}
func (c *compiler) getCurrentProc() string{
	return c.currentproc[len(c.currentproc)-1]
}
func (c *compiler) getParCount() int{
	return c.stackdepth[len(c.stackdepth)-1]
}
func (c *compiler) beginRecord(key string){
	c.earlyexec[key] = ""
	c.lateexec[key] = ""
	c.currentrecord = key
}

func (c *compiler) execEarlyRecord(key string){
	outd := c.currentproc[len(c.currentproc)-1]
	c.output[outd] += "{{"+key+",early}}"
}


func (c *compiler) execLateRecord(key string){
	outd := c.currentproc[len(c.currentproc)-1]
	c.output[outd] += "{{"+key+",late}}"
}

func (c *compiler) endRecord(key string){
	c.currentrecord = ""
}
func (c *compiler) recordToken(){
	c.dorectoken = true
	c.tokenrec = ""
	c.prevtoken = ""
}
func (c *compiler) getRecordedToken() string{
	c.dorectoken = false
	return c.tokenrec
}

func (c *compiler) reset(){
	c.currentproc = make([]string,0)
	c.callingproc = ""
	c.stackdepth = make([]int,1,1)
	c.stackdepth[0] = -1
}
func (c *compiler) export() string{
	s := ""
	for _,v := range c.output{
		for k,v1 := range c.earlyexec{
			v = strings.ReplaceAll(v,"{{"+k+",early}}",v1)
		}
		for k,v1 := range c.lateexec{
			sl := strings.Split(v1,"\n")
			ns := ""
			slices.Reverse(sl)
			for _,v2 := range sl{
				if v2 != ""{
					ns += v2
					ns += "\n"
				}
			}
			v = strings.ReplaceAll(v,"{{"+k+",late}}",ns)
		}
		s += v
		s += "\n"
	}
	return s
}


type progLex struct {
	input string
	tokens []token
}

func newLexer(filename string) *progLex{
	file, _ := os.ReadFile(filename)
	tokens := make([]token,0,30)
	//add token stuff
	//special chars
	tokens = append(tokens, token{regexp.MustCompile(`^\+`),
	func(match string, yylval *parserSymType) int {
		return PLUS
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^-`),
	func(match string, yylval *parserSymType) int {
		return MINUS
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^\^`),
	func(match string, yylval *parserSymType) int {
		return XOR
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^\*`),
	func(match string, yylval *parserSymType) int {
		return MULT
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^/`),
	func(match string, yylval *parserSymType) int {
		return DIV
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^%`),
	func(match string, yylval *parserSymType) int {
		return MOD
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^&&`),
	func(match string, yylval *parserSymType) int {
		return AND
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^||`),
	func(match string, yylval *parserSymType) int {
		return OR
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^&`),
	func(match string, yylval *parserSymType) int {
		return BITAND
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^|`),
	func(match string, yylval *parserSymType) int {
		return BITOR
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^<=`),
	func(match string, yylval *parserSymType) int {
		return LEQ
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^>=`),
	func(match string, yylval *parserSymType) int {
		return GEQ
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^!=`),
	func(match string, yylval *parserSymType) int {
		return NEQ
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^=`),
	func(match string, yylval *parserSymType) int {
		return EQ
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^<`),
	func(match string, yylval *parserSymType) int {
		return LES
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^>`),
	func(match string, yylval *parserSymType) int {
		return GRT
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^\(`),
	func(match string, yylval *parserSymType) int {
		return LPR
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^\)`),
	func(match string, yylval *parserSymType) int {
		return RPR
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^\[`),
	func(match string, yylval *parserSymType) int {
		return LSB
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^\]`),
	func(match string, yylval *parserSymType) int {
		return RSB
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^{`),
	func(match string, yylval *parserSymType) int {
		return LCB
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^}`),
	func(match string, yylval *parserSymType) int {
		return RCB
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^,`),
	func(match string, yylval *parserSymType) int {
		return COMMA
	}})
	//keywords
	//word boundary come in handy
	tokens = append(tokens, token{regexp.MustCompile(`^V\b`),
	func(match string, yylval *parserSymType) int {
		return V
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^P\b`),
	func(match string, yylval *parserSymType) int {
		return P
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^procedure\b`),
	func(match string, yylval *parserSymType) int {
		return PROCEDURE
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^main\b`),
	func(match string, yylval *parserSymType) int {
		return MAIN
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^int\b`),
	func(match string, yylval *parserSymType) int {
		return INT
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^if\b`),
	func(match string, yylval *parserSymType) int {
		return IF
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^then\b`),
	func(match string, yylval *parserSymType) int {
		return THEN
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^else\b`),
	func(match string, yylval *parserSymType) int {
		return ELSE
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^fi\b`),
	func(match string, yylval *parserSymType) int {
		return FI
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^from\b`),
	func(match string, yylval *parserSymType) int {
		return FROM
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^do\b`),
	func(match string, yylval *parserSymType) int {
		return DO
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^loop\b`),
	func(match string, yylval *parserSymType) int {
		return LOOP
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^until\b`),
	func(match string, yylval *parserSymType) int {
		return UNTIL
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^local\b`),
	func(match string, yylval *parserSymType) int {
		return LOCAL
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^delocal\b`),
	func(match string, yylval *parserSymType) int {
		return DELOCAL
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^call\b`),
	func(match string, yylval *parserSymType) int {
		return CALL
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^uncall\b`),
	func(match string, yylval *parserSymType) int {
		return UNCALL
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^par\b`),
	func(match string, yylval *parserSymType) int {
		return PAR
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^rap\b`),
	func(match string, yylval *parserSymType) int {
		return RAP
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^begin\b`),
	func(match string, yylval *parserSymType) int {
		return BEGIN
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^end\b`),
	func(match string, yylval *parserSymType) int {
		return END
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^skip\b`),
	func(match string, yylval *parserSymType) int {
		return SKIP
	}})
	//integer constants
	tokens = append(tokens, token{regexp.MustCompile(`^-?\d+`),
	func(match string, yylval *parserSymType) int {
		n,_ := strconv.Atoi(match)
		yylval.num = n
		return NUM
	}})
	//identifier (variable / func / whatever)
	tokens = append(tokens, token{regexp.MustCompile(`^\w+`),
	func(match string, yylval *parserSymType) int {
		yylval.ident = match
		return IDENT
	}})
	return &progLex{string(file),tokens}
}

func (x *progLex) Lex(yylval *parserSymType) int{
	x.input = strings.TrimLeft(x.input,"\r\n\t\f\v ")//remove whitespaces
	if len(x.input) == 0{
		return 0
	}
	for _, v := range x.tokens {
		s := v.reg.FindString(x.input)
		if s != ""{
			x.input = strings.TrimPrefix(x.input,s)
			if cmp.dorectoken{
				cmp.tokenrec += cmp.prevtoken
				cmp.prevtoken = s
			}
			return v.process(s,yylval)
		}
	}
	panic("Token not found")
}

func (x *progLex) Error(s string){
	panic(s)
}

func main(){
	flag.Usage = func(){
		fmt.Fprintf(flag.CommandLine.Output(), "usage: %s [args] file\n", os.Args[0])
		flag.PrintDefaults()
	}
	outfname := flag.String("o","a.crl","Specifies output `file`. Default is a.crl")
	flag.Parse()
	infname := flag.Arg(0)
	lexer := newLexer(infname)
	cmp = newCompiler()
	parserParse(lexer)
	prep = false
	lexer = newLexer(infname)
	cmp.reset()
	parserParse(lexer)
	outf,_ := os.Create(*outfname)
	defer outf.Close()
	outwriter := bufio.NewWriter(outf)
	outwriter.WriteString(cmp.export())
	outwriter.Flush()
}