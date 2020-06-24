
type signal = string
type var = string

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


type effect = (pure * es) list  (* n +m > 0 /\ m>3 /\  > 0  /\ [A]^n*)


(*
let name (lhs:effect) (rhs:effect) .(env)... : bool = 
*)

        (*(TRUE, [A])*)



