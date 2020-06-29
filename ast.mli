type var = string  (*name of the signal e.g., A B C*)
type name = string


type state = One | Zero
type mapping = (var * state)

(*signal set*)
type instance = mapping list * mapping list 
           (*前面的是constrain,  后面的是signal assignment*)


type es = Bot 
        | Emp 
        | Instance of instance 
        | Con of es * es
        | Kleene of es

type history = es 

type current = mapping list 

type trace = history * current 

type precondition = var list * trace 


type postcondition  = trace list


(*
let name_ (lhs: es) (rhs : es list ) : bool = 


        ;;

let inclusion (lhs: es list) (rhs : es list ) : bool = 
        let es_1 = forall es from lhs
        name_ es_1 rhs = true 

        ;;

*)

        (*
  yes:      A |- C /\ B |- C
        --------------------
         A \/ B |- C

yes:     A |- C /\ A |- B
        --------------------
         A  |- C /\  B


  no:

        A |- C /\ A |- B
        --------------------
         A  |- C \/  B

         a > 0 |- a = 1 /\ a > 0 |- a > 1   -> false 
         -----------------
         a >0 |- a = 1 \/ a > 1     -> true 



        a = 1 |- a > 0  /\ a=2 |- a > 0 
        ----------------
        a = 1 \/ a= 2 |- a >0 

        a = 1 |\- a > 1  /!\ a=2 |- a > 1
        ----------------
        a = 1 \/ a= 2 |- a >1
        
        
        *)


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