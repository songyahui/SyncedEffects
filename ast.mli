type var = string  (*name of the signal e.g., A B C*)
type name = string


type signal = One of var | Zero of var

(*signal set*)
type instance = signal list ;;

type p_instance = signal list * signal list ;;

type p_es = PBot 
        | PEmp 
        | PInstance of p_instance 
        | PCon of p_es * p_es
        | PDisj of p_es * p_es
        | PKleene of p_es
        | POmega of p_es
        | PNtimed of p_es * int

type es = Bot 
        | Emp 
        | Instance of instance 
        | Con of es * es
        | Disj of es * es
        | Kleene of es
        | Omega of es
        | Ntimed of es * int

type history = p_es 

type current = p_instance

type trace = history *  current option * name option (*exiting from a trap*) 

type inclusion = es * es;;

type prog = Nothing 
          | Pause 
          | Seq of prog * prog 
          | Par of prog * prog
          | Loop of prog
          | Declear of var * prog
          | Emit of var
          | Present of var * prog * prog
          | Trap of name * prog
          | Exit of name
          | Run of name
          | Suspend of prog * name 

type ltl = Lable of string 
        | Next of ltl
        | Until of ltl * ltl
        | Global of ltl
        | Future of ltl
        | NotLTL of ltl
        | Imply of ltl * ltl
        | AndLTL of ltl * ltl
        | OrLTL of ltl * ltl

type prog_states = trace list

type spec_prog = name * var list * var list * es * es * prog
            (* name , input, output, precon, postcon, body*)