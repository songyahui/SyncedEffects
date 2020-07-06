#require "core";;
open Base;;
open Core;;

type var = string;;
type name = string;;

type state = One | Zero;;
type mapping = (var * state);;

type instance = mapping list * mapping list;; 

type es = Bot 
        | Emp 
        | Instance of instance 
        | Con of es * es
        | Kleene of es
        | Any
        | Omega of es
;;
type history = es;;
type current = mapping list;;
type trace = history * current;;
type precondition = var list *  trace;;
type postcondition  = trace list;;

type inclusion =
  INC of es list * es list
;;

let rec nullable_single (i:es) : bool =
  match i with
    |Instance(_) -> false
    |Emp -> true
    |Con(a, b) -> nullable_single a && nullable_single b
    |Kleene(_) -> true
    |Bot -> false
    |Any -> false
    |Omega(_) -> false
;;

let rec nullable (e:es list) : bool=
  match e with
    |hd::tl -> nullable_single hd || nullable tl
    |[] -> false
;;

let rec join (list1:name list list) (list2:name list list) : name list list=
  let rec check_repeated (t:name list) (list: name list list) : bool =
    match list with
      |hd::tl -> if hd = t then true else check_repeated t tl
      |[] -> false
  in 
  match list1 with
  |hd::tl -> if check_repeated hd list2 then join tl list2 else hd::join tl list2
  |[] -> list2
;;

let rec join_single (list1:es list) (list2:es list) : es list=
  let rec check_repeated (t:es) (list:es list) : bool =
    match list with
      |hd::tl -> if hd = t then true else check_repeated t tl
      |[] -> false
  in 
  match list1 with
  |hd::tl -> if check_repeated hd list2 then join_single tl list2 else hd::join_single tl list2
  |[] -> list2
;;

let rec rewrite (i:mapping list) : name list=
  match i with
    |hd::tl -> let rewrite_single (e:mapping) : name =
      match e with (a,b) -> if b = One then a else "None"
    in let result = rewrite_single hd in
      if result = "None" then rewrite tl else result::rewrite tl
    |[] -> []
;;

let rec find_first_element (e:es list) : name list list =
  let rec find_first_element_single (i:es) : name list list =
    match i with
      |Instance(a,b) -> [rewrite b]
      |Con(a, b) -> if nullable_single a then join (find_first_element_single a) (find_first_element_single b)
        else find_first_element_single a
      |Kleene(a) -> find_first_element_single a
      |Omega(a) -> find_first_element_single a
      |Any -> [["_"]]
      |_ -> []
  in match e with
    |hd::tl -> let rec remove_empty (i:name list list) : name list list = 
      match i with 
        |hd::tl -> if hd = [] then tl else hd::remove_empty tl
        |[] -> [] 
    in remove_empty (join (find_first_element_single hd) (find_first_element tl))
    |[] -> []
;;

let rec contains (ss1:name list) (ss2:name list) : bool =
  let rec contain_single (s:name) (ss:name list) : bool =
    match ss with 
      |hd::tl -> if s = hd then true else contain_single s tl
      |[] -> false
  in match ss2 with
    |hd::tl -> if contain_single hd ss1 then contains ss1 tl 
      else false
    |[] -> true
;;

let rec unfold (element:name list) (expr:es list) : es list =
  let rec flatten (a:es list) (b:es) : es list =
    match a with
      |hd::tl -> Con(hd, b)::(flatten tl b)
      |[] -> []
  in let rec unfold_single (element:name list) (e:es) : es list =
    match e with
      |Instance(a, b) -> let result = rewrite b in 
        if result = [] then [Bot]
        else if element = ["_"] then [Emp]
        else if contains element (rewrite b) then [Emp] 
        else [Bot]
      |Con(a,b) -> if nullable_single a then join_single (flatten (unfold_single element a) b) (unfold_single element b)
        else flatten (unfold_single element a) b
      |Emp -> [Bot]
      |Any -> [Emp]
      |Bot -> [Bot]
      |Omega(s) -> flatten (unfold_single element s) e
      |Kleene(s) -> flatten (unfold_single element s) e
  in match expr with
    |hd::tl -> join_single (unfold_single element hd) (unfold element tl)
    |[] ->[]
;;

let rec normalize (e:es list) : es list =
  let rec normalize_single (i:es) : es =
    match i with
      |Con(a, b) -> if a = Emp || normalize_single a = Emp then normalize_single b
        else if b = Emp || normalize_single b = Emp then normalize_single a
        else if a = Bot || normalize_single a = Bot || b = Bot || normalize_single b = Bot then Bot
        else Con(normalize_single a, normalize_single b)
      |_ -> i
  in match e with 
    |hd::tl -> (normalize_single hd)::(normalize tl)
    |[] -> []
;;

let rec check_include (i:inclusion) (memory:inclusion list) : bool =
  match memory with
    |hd::tl -> if hd = i then true else check_include i tl
    |[] -> false
;;

let rec evaluate elements memory (lhs:es list) (rhs:es list) : bool =
  match elements with
    |hd::tl -> let dev_lhs = normalize (unfold hd lhs) and dev_rhs = normalize (unfold hd rhs) in
      let null_lhs = nullable dev_lhs and null_rhs = nullable dev_rhs and i = INC(dev_lhs, dev_rhs) in
      if dev_rhs = [Bot] then false
      else if null_lhs && not null_rhs then false
      else if check_include i memory then evaluate tl memory lhs rhs
      else let m = i::memory in
        evaluate tl memory lhs rhs && evaluate (find_first_element dev_lhs) m dev_lhs dev_rhs
    |[] -> if nullable lhs && not (nullable rhs) then false else true
;;

let rec check_containment (lhs:es list) (rhs:es list) : bool =
  let l = normalize lhs and r = normalize rhs in 
    if nullable l && not (nullable r) then false
    else let elements = find_first_element l in
      evaluate elements [INC(l, r)] l r
;;