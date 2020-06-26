#require "core";;
open Base;;
open Core;;

type signal = string;;
type var = string;;

type ss = signal list;;

type es = Bot 
        | Emp 
        | Instance of ss 
        | Or of es * es 
        | Con of es * es
        | Kleene of es
        | Time of es * var
;;

type terms = Var of var   
           | Number of int 
           | Plus of terms * terms
           | Minus of terms * terms     
;;
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
;;

type effect = (pure * es) list;; 

type inclusion =
  INC of es * es
;;

let rec nullable e =
  match e with
    |Instance(_) -> false
    |Emp -> true
    |Or(a, b) -> nullable a || nullable b
    |Con(a, b) -> nullable a && nullable b
    |Kleene(_) -> true
    |Bot -> false
    |Time(a, b) -> nullable a
;;

let rec join list1 list2 =
  let rec check_repeated t list =
    match list with
      |hd::tl -> if hd = t then true else check_repeated t tl
      |[] -> false
  in 
  match list1 with
  |hd::tl -> if check_repeated hd list2 then join tl list2 else hd::join tl list2
  |[] -> list2
;;

let rec find_first_element e =
  match e with
    |Instance(e) -> e::[]
    |Con(a, b) -> if nullable a then join (find_first_element a) (find_first_element b) 
      else find_first_element a
    |Kleene(e) -> find_first_element e
    |Or(a, b) -> join (find_first_element a) (find_first_element b)
    |_ -> []
;;

let rec contains ss1 ss2 =
  let rec contain_single s ss =
    match ss with 
      |hd::tl -> if s = hd then true else contain_single s tl
      |[] -> false
  in match ss2 with
    |hd::tl -> if contain_single hd ss1 then contains ss1 tl else false
    |[] -> true
;;

let rec unfold element expr =
  match expr with
    |Instance(s) -> if contains element s then Emp else Bot
    |Con(a,b) -> if nullable a then Or(Con(unfold element a, b), unfold element b)
      else Con(unfold element a, b)
    |Or(a,b) -> Or(unfold element a, unfold element b)
    |Emp -> Bot
    |Bot -> Bot
    |Kleene(s) -> Con(unfold element s, expr)
    |_ -> expr
;;

let rec is_repeated_term plus term =
  match plus with
    |Or(a,b) -> if a = term || b = term then true else is_repeated_term a term || is_repeated_term b term
    |_ -> false
;;

let rec normalize e =
  match e with
    |Con(a, b) -> if a = Emp || normalize a = Emp then normalize b
      else if b = Emp || normalize b = Emp then normalize a
      else if a = Bot || normalize a = Bot || b = Bot || normalize b = Bot then Bot
      else Con(normalize a, normalize b)
    |Or(a,b) -> if a = Bot || normalize a = Bot then normalize b
      else if b = Bot || normalize b = Bot then normalize a
      else if is_repeated_term a b then normalize a
      else if is_repeated_term b a then normalize b
      else if a = b then normalize a
      else Or(normalize a, normalize b)
    |_ -> e
;;

let rec check_include i memory =
  match memory with
    |hd::tl -> if hd = i then true else check_include i tl
    |[] -> false
;;

let rec evaluate elements memory lhs rhs =
  match elements with
    |hd::tl -> let dev_lhs = normalize (unfold hd lhs) and dev_rhs = normalize (unfold hd rhs) in
      let null_lhs = nullable dev_lhs and null_rhs = nullable dev_rhs and i = INC(dev_lhs, dev_rhs) in
      if null_lhs && not null_rhs then false
      else if check_include i memory then evaluate tl memory lhs rhs
      else let m = i::memory in
        evaluate tl memory lhs rhs && evaluate (find_first_element dev_lhs) m dev_lhs dev_rhs
    |[] -> if nullable lhs && not (nullable rhs) then false else true
;;

let check_containment lhs rhs =
  if nullable lhs && not (nullable rhs) then false
  else let elements = find_first_element lhs in
      evaluate elements [INC(lhs, rhs)] (normalize lhs) (normalize rhs)
;;