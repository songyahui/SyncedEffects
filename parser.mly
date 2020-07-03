%{ open Ast %}
%{ open List %}


%token <string> VAR
%token <int> INTE
%token NOTHING PAUSE PAR  LOOP SIGNAL LPAR RPAR EMIT PRESENT TRAP EXIT SIMI

(*CHOICE LPAR RPAR CONCAT OMEGA POWER PLUS MINUS TRUE FALSE DISJ CONJ   ENTIL INTT BOOLT VOIDT 
%token LBRACK RBRACK  SIMI  IF ELSE REQUIRE ENSURE LSPEC RSPEC RETURN LBrackets  RBrackets
%token  GT LT EQ GTEQ LTEQ INCLUDE SHARP EQEQ UNDERLINE KLEENE NEGATION DEADLINE RESET TASSERTKEY TRIPLE DELAY
%token <string> EVENT

%left CHOICE
%left CONCAT
%left DISJ
%left CONJ
%token <string> STRING
EOF
*)

(*%token FUTURE GLOBAL IMPLY LTLNOT NEXT UNTIL LILAND LILOR*)



%start prog 
%type <Ast.prog> prog



%%

prog:
| NOTHING { Nothing }
| PAUSE   { Pause } 
| LPAR p1 = prog SIMI p2 = prog RPAR { Seq (p1, p2)}
| LPAR  p1 = prog PAR p2 = prog RPAR { Par (p1, p2)}
| LPAR LOOP p = prog  RPAR { Loop p}
| LPAR SIGNAL s = VAR p = prog RPAR { Declear (s, p)}
| EMIT s = VAR  {Emit s}
| LPAR PRESENT s = VAR p1 = prog p2 = prog RPAR { Present (s, p1, p2)}
| LPAR TRAP p1 = prog RPAR {Trap p1}
| LPAR EXIT d = INTE RPAR {Exit d}



