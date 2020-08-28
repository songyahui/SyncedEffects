%{ open Ast %}
%{ open List %}


%token <string> VAR
%token <int> INTE
%token NOTHING PAUSE PAR  LOOP SIGNAL LPAR RPAR EMIT PRESENT TRAP EXIT SIMI

%token EOF ENTIL EMPTY DISJ LBrackets  RBrackets COMMA CONCAT POWER KLEENE

%left CONCAT DISJ
%token FUTURE GLOBAL IMPLY LTLNOT NEXT UNTIL LILAND LILOR 
%token LSPEC RSPEC ENSURE REQUIRE MODULE COLON INPUT OUTPUT


%start specProg pRog ee ltl_p
%type <Ast.spec_prog> specProg
%type <Ast.prog> pRog
%type <(Ast.inclusion) list > ee
%type <(Ast.ltl) list > ltl_p


%%

ee: 
| EOF {[]}
| a = entailment SIMI r = ee { append [a] r }

ltl_p: 
| EOF {[]}
| a = ltl SIMI r = ltl_p { append [a] r }

ltl : 
| s = VAR {Lable s} 
| LPAR r = ltl RPAR { r }
| NEXT p = ltl  {Next p}
| LPAR p1= ltl UNTIL p2= ltl RPAR {Until (p1, p2)}
| GLOBAL p = ltl {Global p}
| FUTURE p = ltl {Future p}
| LTLNOT p = ltl {NotLTL p}
| LPAR p1= ltl IMPLY p2= ltl RPAR {Imply (p1, p2)}
| LPAR p1= ltl LILAND p2= ltl RPAR {AndLTL (p1, p2)}  
| LPAR p1= ltl LILOR p2= ltl RPAR {OrLTL (p1, p2)}  

singleVAR: var = VAR {[var]}

existVar:
| {[]}
| p = singleVAR {p}
| p1 = singleVAR  COMMA  p2 = existVar {append p1 p2 }


es:
| EMPTY { Emp }
| LBrackets signals = existVar RBrackets 
{
  let temp = List.map (fun a -> (a, One)) signals in 
  Instance ([], temp) }
| LPAR r = es RPAR { r }
| a = es CONCAT b = es { Con(a, b) } 
| a = es  DISJ  b=es  {Disj (a, b)}
| LPAR a = es POWER KLEENE RPAR{Kleene a}
| LPAR r = es POWER n = INTE RPAR{ Ntimed (r, n) }



(*
| str = EVENT p=parm { Event ( str, p) }
| a = es CHOICE b = es { ESOr(a, b) }
| a = es CONJ b = es { ESAnd(a, b) }
| LPAR r = es POWER t = term RPAR { Ttimes(r, t )}
*)

entailment:
| lhs = es   ENTIL   rhs = es {INC (lhs, rhs)}


pRog:
| NOTHING { Nothing }
| PAUSE   { Pause } 
| LPAR p1 = pRog SIMI p2 = pRog RPAR { Seq (p1, p2)}
| LPAR  p1 = pRog PAR p2 = pRog RPAR { Par (p1, p2)}
| LPAR LOOP p = pRog  RPAR { Loop p}
| LPAR SIGNAL s = VAR p = pRog RPAR { Declear (s, p)}
| EMIT s = VAR  {Emit s}
| LPAR PRESENT s = VAR p1 = pRog p2 = pRog RPAR { Present (s, p1, p2)}
| LPAR TRAP mn = VAR p1 = pRog RPAR {Trap (mn, p1)}
| LPAR EXIT mn = VAR d = INTE RPAR {Exit (mn, d)}


specProg: 
| MODULE nm = VAR COLON 
  INPUT ins = existVar SIMI
  OUTPUT outs = existVar SIMI
  LSPEC REQUIRE pre = es ENSURE post = es RSPEC p = pRog 
  {(nm, ins, outs, pre, post, p)}
| MODULE nm = VAR COLON 
  INPUT ins = existVar SIMI
  OUTPUT outs = existVar SIMI
   p = pRog 
  {(nm, ins, outs, Emp, Emp, p)}

