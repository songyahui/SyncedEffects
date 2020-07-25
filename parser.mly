%{ open Ast %}
%{ open List %}


%token <string> VAR
%token <int> INTE
%token NOTHING PAUSE PAR  LOOP SIGNAL LPAR RPAR EMIT PRESENT TRAP EXIT SIMI

%token EOF ENTIL EMPTY UNDERLINE DISJ LBrackets  RBrackets COMMA CONCAT POWER KLEENE OMEGA

%left CONCAT DISJ
%token FUTURE GLOBAL IMPLY LTLNOT NEXT UNTIL LILAND LILOR LSPEC RSPEC ENSURE



(*CHOICE LPAR RPAR CONCAT   PLUS MINUS TRUE FALSE  CONJ    INTT BOOLT VOIDT 
%token LBRACK RBRACK  SIMI  IF ELSE REQUIRE ENSURE LSPEC RSPEC RETURN 
%token  GT LT EQ GTEQ LTEQ INCLUDE SHARP EQEQ UNDERLINE  NEGATION DEADLINE RESET TASSERTKEY TRIPLE DELAY
%token <string> EVENT

%left CHOICE

%
%left CONJ
%token <string> STRING

*)

(*%token FUTURE GLOBAL IMPLY LTLNOT NEXT UNTIL LILAND LILOR*)



%start full_prog  ee ltl_p
%type <Ast.spec_prog> full_prog
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
| UNDERLINE { Any }
| LBrackets signals = existVar RBrackets 
{
  let temp = List.map (fun a -> (a, One)) signals in 
  Instance ([], temp) }
| LPAR r = es RPAR { r }
| a = es CONCAT b = es { Con(a, b) } 
| LPAR a = es POWER KLEENE RPAR{Kleene a}
| LPAR r = es POWER OMEGA RPAR{ Omega r }
| LPAR r = es POWER n = INTE RPAR{ Ntimed (r, n) }
| LPAR LTLNOT r = es RPAR { Not r }

(*
| str = EVENT p=parm { Event ( str, p) }
| a = es CHOICE b = es { ESOr(a, b) }
| a = es CONJ b = es { ESAnd(a, b) }
| LPAR r = es POWER t = term RPAR { Ttimes(r, t )}
*)

effect:
|  r = es  { [r] }
| a = effect  DISJ  b=effect  {List.append a b}


entailment:
| lhs = effect   ENTIL   rhs = effect {INC (lhs, rhs)}


prog:
| NOTHING { Nothing }
| PAUSE   { Pause } 
| LPAR p1 = prog SIMI p2 = prog RPAR { Seq (p1, p2)}
| LPAR  p1 = prog PAR p2 = prog RPAR { Par (p1, p2)}
| LPAR LOOP p = prog  RPAR { Loop p}
| LPAR SIGNAL s = VAR p = prog RPAR { Declear (s, p)}
| EMIT s = VAR  {Emit s}
| LPAR PRESENT s = VAR p1 = prog p2 = prog RPAR { Present (s, p1, p2)}
| LPAR TRAP mn = VAR p1 = prog RPAR {Trap (mn, p1)}
| LPAR EXIT mn = VAR d = INTE RPAR {Exit (mn, d)}


full_prog: 
| LSPEC ENSURE eL = effect RSPEC p = prog {(eL, p)}
| p = prog {([], p)}

