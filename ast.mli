type var = string  (*name of the signal e.g., A B C*)
type name = string


type signal = One of var | Zero of var

(*signal set*)
type instance = signal list ;;

(*type event  = Instance of instance   | Not of instance *)

type es = Bot 
        | Emp 
        | Instance of instance 
        | Con of es * es
        | Disj of es * es
        | Kleene of es
        | Ntimed of es * int

type history = es 

type current = instance

type trace = history * current 

type inclusion = INC of es * es;;

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
          | Run of name 

type ltl = Lable of string 
        | Next of ltl
        | Until of ltl * ltl
        | Global of ltl
        | Future of ltl
        | NotLTL of ltl
        | Imply of ltl * ltl
        | AndLTL of ltl * ltl
        | OrLTL of ltl * ltl

type prog_states = (es * instance) list

type spec_prog = name * var list * var list * es * es * prog
            (* name , input, output, precon, postcon, body*)