type var = string  (*name of the signal e.g., A B C*)
type name = string


type state = One | Zero
type mapping = (var * state) 


(*signal set*)
type instance = mapping list * mapping list 
           (*前面的是constrain,  后面的是signal assignment*)

type fst = Negation of name list
           | Normal of name list
;;

(*type event  = Instance of instance   | Not of instance *)


type es = Bot 
        | Emp 
        | Instance of instance 
        | Con of es * es
        | Kleene of es
        | Any
        | Omega of es
        | Ntimed of es * int
        | Not of es

type history = es 

type current = instance

type trace = history * current * int 

type precondition = var list * (history * current) 


type postcondition  = trace list 

type inclusion = INC of es list * es list;;


type prog = Nothing 
          | Pause 
          | Seq of prog * prog 
          | Par of prog * prog
          | Loop of prog
          | Declear of var * prog
          | Emit of var
          | Present of var * prog * prog
          | Trap of name * prog
          | Exit of name * int


type ltl = Lable of string 
        | Next of ltl
        | Until of ltl * ltl
        | Global of ltl
        | Future of ltl
        | NotLTL of ltl
        | Imply of ltl * ltl
        | AndLTL of ltl * ltl
        | OrLTL of ltl * ltl


type spec_prog = es list * prog