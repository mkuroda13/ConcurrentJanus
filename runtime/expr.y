%{
package main
import (
	"strconv"
	"regexp"
	"strings"
)
var retval int
%}

%union {
	num int
	ident string
}

%token <num> NUM
%token <ident> IDENT
%token PLUS MINUS XOR MULT DIV MOD AND OR BITAND BITOR LEQ GEQ NEQ EQ LES GRT LPR RPR LSB RSB
%type <num> variable expr1 expr2 expr3 expr4 expr5 expr6

%%
expr : expr1
{
	retval = $1
}
expr1 : expr2
{
	$$ = $1
}
		| expr1 OR expr2
		{
			if $1 != 0 || $3 != 0{
				$$ = 1
			} else {
				$$ = 0
			}
		}
expr2 : expr3
{
	$$ = $1
}
		| expr2 AND expr3
		{
			if $1 != 0 && $3 != 0{
				$$ = 1
			} else {
				$$ = 0
			}
		}

expr3 : expr4
{
	$$ = $1
}
		| expr3 LEQ expr4
		{
			if $1 <= $3{
				$$ = 1
			} else {
				$$ = 0
			}
		}
		| expr3 GEQ expr4
		{
			if $1 >= $3{
				$$ = 1
			} else {
				$$ = 0
			}
		}
		| expr3 EQ expr4
		{
			if $1 == $3{
				$$ = 1
			} else {
				$$ = 0
			}
		}
		| expr3 EQ EQ expr4
		{
			if $1 == $4{
				$$ = 1
			} else {
				$$ = 0
			}
		}
		| expr3 NEQ expr4
		{
			if $1 != $3{
				$$ = 1
			} else {
				$$ = 0
			}
		}
		| expr3 LES expr4
		{
			if $1 < $3{
				$$ = 1
			} else {
				$$ = 0
			}
		}
		| expr3 GRT expr4
		{
			if $1 > $3{
				$$ = 1
			} else {
				$$ = 0
			}
		}
expr4 : expr5
{
	$$ = $1
}
		| expr4 PLUS expr5
		{
			$$ = $1 + $3
		}
		| expr4 MINUS expr5
		{
			$$ = $1 - $3
		}
		| expr4 BITOR expr5
		| expr4 XOR expr5
		{
			$$ = $1 ^ $3
		}
expr5 : expr6
{
	$$ = $1
}
		| expr5 MULT expr6
		{
			$$ = $1 * $3
		}
		| expr5 DIV expr6
		{
			$$ = $1 / $3
		}
		| expr5 MOD expr6
		{
			$$ = $1 % $3
		}
		| expr5 BITAND expr6

expr6 : variable
{
	$$ = $1
}
		| LPR expr1 RPR
{
	$$ = $2
}
		| MINUS variable
{
	$$ = -1 * $2
}

variable : NUM
{
	$$ = $1
}
		 | IDENT
{
	$$ = r.ReadSym($1,p,rev)
}
		 | IDENT LSB expr1 RSB
{
	$$ = r.ReadSym($1+"["+strconv.Itoa($3)+"]",p,rev)
	
}
%%
var lexer *exprLex = newLexer()
var r *runtime
var p *pc
var rev bool
type exprLex struct {
	input string
	tokens []token
}
type token struct{
	reg *regexp.Regexp
	process func(match string, yylval *exprSymType) int
}
func newLexer() *exprLex{
	tokens := make([]token,0,30)
	//add token stuff
	//special chars
	tokens = append(tokens, token{regexp.MustCompile(`^\+`),
	func(match string, yylval *exprSymType) int {
		return PLUS
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^-`),
	func(match string, yylval *exprSymType) int {
		return MINUS
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^\^`),
	func(match string, yylval *exprSymType) int {
		return XOR
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^\*`),
	func(match string, yylval *exprSymType) int {
		return MULT
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^/`),
	func(match string, yylval *exprSymType) int {
		return DIV
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^%`),
	func(match string, yylval *exprSymType) int {
		return MOD
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^&&`),
	func(match string, yylval *exprSymType) int {
		return AND
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^\|\|`),
	func(match string, yylval *exprSymType) int {
		return OR
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^&`),
	func(match string, yylval *exprSymType) int {
		return BITAND
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^\|`),
	func(match string, yylval *exprSymType) int {
		return BITOR
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^<=`),
	func(match string, yylval *exprSymType) int {
		return LEQ
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^>=`),
	func(match string, yylval *exprSymType) int {
		return GEQ
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^!=`),
	func(match string, yylval *exprSymType) int {
		return NEQ
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^=`),
	func(match string, yylval *exprSymType) int {
		return EQ
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^<`),
	func(match string, yylval *exprSymType) int {
		return LES
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^>`),
	func(match string, yylval *exprSymType) int {
		return GRT
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^\(`),
	func(match string, yylval *exprSymType) int {
		return LPR
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^\)`),
	func(match string, yylval *exprSymType) int {
		return RPR
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^\[`),
	func(match string, yylval *exprSymType) int {
		return LSB
	}})
	tokens = append(tokens, token{regexp.MustCompile(`^\]`),
	func(match string, yylval *exprSymType) int {
		return RSB
	}})
	//integer constants
	tokens = append(tokens, token{regexp.MustCompile(`^-?\d+`),
	func(match string, yylval *exprSymType) int {
		n,_ := strconv.Atoi(match)
		yylval.num = n
		return NUM
	}})
	//identifier (variable / func / whatever)
	tokens = append(tokens, token{regexp.MustCompile(`^[\w\d\[\]\$\#]+`),
	func(match string, yylval *exprSymType) int {
		yylval.ident = match
		return IDENT
	}})
	return &exprLex{"",tokens}
}
func (x *exprLex) Lex(yylval *exprSymType) int{
	x.input = strings.TrimLeft(x.input,"\r\n\t\f\v ")//remove whitespaces
	if len(x.input) == 0{
		return 0
	}
	for _, v := range x.tokens {
		s := v.reg.FindString(x.input)
		if s != ""{
			x.input = strings.TrimPrefix(x.input,s)
			return v.process(s,yylval)
		}
	}
	panic("Token not found")
}

func (x *exprLex) Error(s string){
	panic("Syntax Error: " + s)
}

func EvalExpr(s string, rt *runtime, pt *pc, revt bool) int {
	retval = 0
	lexer.input = s
	r = rt
	p = pt
	rev = revt
	exprParse(lexer)
	return retval
}