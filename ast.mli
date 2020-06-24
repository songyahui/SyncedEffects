
type signal = string
type var = string
type name = string

(*signal set*)
type ss = signal list

type es = Bot 
        | Emp 
        | Instance of ss 
        | Or of es * es 
        | Con of es * es
        | Kleene of es
        | Time of es * var (*[A]^n*)

type terms = Var of var   
           | Number of int 
           | Plus of terms * terms (*n+1*)
           | Minus of terms * terms     

type pure = TRUE
          | FALSE
          | Gt of terms * terms
          | Lt of terms * terms
          | GtEq of terms * terms
          | LtEq of terms * terms
          | Eq of terms * terms
          | PureOr of pure * pure
          | PureAnd of pure * pure
          | Neg of pure


type effect = (pure * es) list  

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