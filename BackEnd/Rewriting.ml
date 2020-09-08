open String
open List
open Ast
open Printf
open Parser
open Lexer
open Pretty
open Sys

(*
let expand_ntime (e:es) : es =
  let rec expand_single (i:es) n : es =
    if n > 1 then Con(i, expand_single i (n-1))
    else if n = 1 then i
    else Emp
  in match e with
    |Ntimed(a, b) -> expand_single a b
    |_ -> e
;;

let rec nullable_single (i:es) : bool =
  match i with
    |Instance(_) -> false
    |Emp -> true
    |Con(a, b) -> nullable_single a && nullable_single b
    |Kleene(_) -> true
    |Bot -> false
    |Ntimed(a, b) -> nullable_single (expand_ntime i)
    |Disj (es1, es2) -> nullable_single es1 || nullable_single es2
;;

let rec nullable (e:es list) : bool=
  match e with
    |hd::tl -> nullable_single hd || nullable tl
    |[] -> false
;;

let rec join (list1:fst list) (list2:fst list) : fst list=
  let rec check_repeated (t:fst) (list: fst list) : bool =
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

let rec find_first_element (e:es list) : fst list =
  let rec find_first_element_single (i:es) : fst list =
    match i with
      |Instance(a,b) -> [Normal(rewrite b)]
      |Con(a, b) -> if nullable_single a then join (find_first_element_single a) (find_first_element_single b)
        else find_first_element_single a
      |Kleene(a) -> find_first_element_single a
      |Ntimed(_, _) -> find_first_element_single (expand_ntime i)
      |_ -> []
  in match e with
    |hd::tl -> let rec remove_empty (i:fst list) : fst list = 
      match i with 
        |hd::tl -> if hd = Normal([]) then tl else hd::remove_empty tl
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

let rec contains_fst (f:fst) (ss:name list) : bool =
  match f with
    |Normal(a) -> contains a ss
    |Negation(a) -> not (contains a ss)
;;

let rec unfold (element:fst) (expr:es list) : es list =
  let rec flatten (a:es list) (b:es) : es list =
    match a with
      |hd::tl -> Con(hd, b)::(flatten tl b)
      |[] -> []
  in let rec unfold_single (element:fst) (e:es) : es list =
    match e with
      |Instance(a, b) -> let result = rewrite b in 
        if result = [] then [Bot]
        else if element = Normal(["_"]) then [Emp]
        else if contains_fst element (rewrite b) then [Emp] 
        else [Bot]
      |Con(a,b) -> if nullable_single a then join_single (flatten (unfold_single element a) b) (unfold_single element b)
        else flatten (unfold_single element a) b
      |Emp -> [Bot]
      |Bot -> [Bot]
      |Kleene(s) -> flatten (unfold_single element s) e
      |Ntimed(_, _) -> unfold_single element (expand_ntime e)
  in match expr with
    |hd::tl -> join_single (unfold_single element hd) (unfold element tl)
    |[] ->[]
;;

let rec normalize (e:es list) : es list =
  let rec normalize_single (i:es) : es =
    match i with
      |Con(a, b) -> let is_Omega s = match s with 
      | _ -> false in
        if a = Emp || normalize_single a = Emp then normalize_single b
        else if b = Emp || normalize_single b = Emp then normalize_single a
        else if a = Bot || normalize_single a = Bot || b = Bot || normalize_single b = Bot then Bot
        else if is_Omega a then normalize_single a
        else Con(normalize_single a, normalize_single b)
      |Kleene(s) -> if s = Emp then Emp
        else if s = Bot then Bot
        else i
      |Ntimed(_, _) -> normalize_single (expand_ntime i)
      |_ -> i
  in match e with 
    |hd::tl -> if tl = [Bot] then [normalize_single hd]
      else if List.length e <> 1 && hd = Bot then normalize tl else (normalize_single hd)::(normalize tl)
    |[] -> []
;;

let rec check_include (i:inclusion) (memory:inclusion list) : bool =
  match memory with
    |hd::tl -> if hd = i then true else check_include i tl
    |[] -> false
;;

let rec iter (l: string list) =
    match l with
      |hd::tl -> if tl = [] then hd else hd ^ ";" ^ iter tl 
      |[] -> ""
;;

let print_derivative (f:fst) =
  match f with
    |Normal(a) -> "(-[" ^ (iter a) ^ "])"
    |Negation(a) -> "(-![" ^ (iter a) ^ "])"
;;

let rec translate (e: es list) : string =
  let rec translate_single (i: es) : string =
    match i with
      |Instance(a, b) -> "[" ^ iter (rewrite b) ^ "]"
      |Con(a, b) -> translate_single a ^ "." ^ translate_single b
      |Emp -> "Emp"
      |Bot -> "_|_"
      |Kleene(s) -> "(" ^ translate_single s ^ ")" ^ "^*"
      |Ntimed (s, n) -> "(" ^ translate_single s ^ ")" ^ "^" ^ string_of_int n
  in match e with 
    |hd::tl -> if tl = [] then translate_single hd else translate_single hd ^ " + " ^ translate tl
    |[] -> ""
;;

let get_tree e =
  match e with 
    |(a, _) -> a
;;

let get_bool e = 
  match e with 
    |(_, b) -> b
;;

let rec evaluate (elements:fst list) (memory:inclusion list) (lhs:es list) (rhs:es list) : (binary_tree * bool) =
  let entailment = (translate (normalize lhs)) ^ " |- " ^ (translate (normalize rhs)) and i = INC(lhs, rhs) in
  match elements with
    |hd::tl ->
      if rhs = [Bot] then (Node(entailment ^ "   [DISPROVE]", []), false)
      else if nullable lhs && not (nullable rhs) then (Node(entailment ^ "   [DISPROVE]", []), false)
      else if check_include i memory then (Node(entailment ^ "   [PROVE]", []), true)
      else let m = i::memory and dev_lhs = normalize (unfold hd lhs) and dev_rhs = normalize (unfold hd rhs) in
        let result1 = evaluate tl memory lhs rhs and result2 = evaluate (find_first_element dev_lhs) m dev_lhs dev_rhs in
          (Node(print_derivative hd ^ entailment ^ "   [UNFOLD]", (get_tree result1)::(get_tree result2)::[]), (get_bool result1) && (get_bool result2))
    |[] -> if nullable lhs && not (nullable rhs) then (Node(entailment ^ "   [DISPROVE]", []), false) 
           else if lhs = [Emp] then (Node(entailment ^ "   [PROVE]", []), true)
           else (Leaf, true) 
;;

let rec check_containment (lhs:es list) (rhs:es list) =
  let l = normalize lhs and r = normalize rhs in 
  let elements = find_first_element l in
  let result = evaluate elements [] l r in
  (get_bool result,  (Node((translate (normalize lhs)) ^ " |- " ^ (translate (normalize rhs)), [get_tree (result)])))
;;

let a = Instance([], [("A", One); ("B", One); ("C", Zero)]) and b = Instance([], [("A", Zero); ("B", Zero); ("C", One)]) and c = Instance([], [("A", One); ("B", Zero); ("C", Zero)]) and d = Instance([], [("D", One); ("B", Zero); ("C", Zero)]);;


let lhs = [Con(a, Kleene(a)); Con(b, Kleene(a))] and rhs = [Con(Kleene(a), Kleene(b))];;
*)

let rec nallable (es:es):bool = 
  match es with 
    Bot -> false 
  | Emp -> true
  | Instance _  -> false 
  | Con (es1, es2) -> nallable es1 && nallable es2
  | Disj (es1, es2) -> nallable es1 || nallable es2
  | Kleene _ -> false 
  | Ntimed (_, n) -> n==0 
  ;;
let isBot (es:es):bool = 
  match es with 
    Bot -> true 
    |_ -> false 
    ;; 
  
let rec getFst (es:es) :instance list= 
  match es with 
    Bot -> raise (Foo "getFst has a Bot as argument") 
  | Emp -> raise (Foo "getFst has a Emp as argument") 
  | Instance ins  -> [ins] 
  | Con (es1, es2) -> if nallable es1 then append (getFst es1) (getFst es2) else getFst es1
  | Disj (es1, es2) -> append (getFst es1) (getFst es2)
  | Kleene esIn -> (getFst esIn) 
  | Ntimed (esIn, n) -> (getFst esIn) 
  ;;

let superSetOf (bigger:instance) (smaller:instance) :bool = 
  true;;

let reoccur (evn: inclusion list) (lhs:es) (rhs:es) :bool = 
  true;;


let rec derivative (ins_given: instance) (es:es) : es = 
  match es with 
    Bot -> Bot
  | Emp -> Bot
  | Instance ins  -> if superSetOf ins_given ins then Emp else Bot
  | Con (es1, es2) -> Con (derivative ins_given es1, es2)
  | Disj (es1, es2) -> Disj (derivative ins_given es1, derivative ins_given es2)
  | Kleene esIn -> Con (derivative ins_given esIn, es)
  | Ntimed (esIn, n) -> Con (derivative ins_given esIn, Ntimed (esIn, n-1))
  ;;



let rec containment (evn: inclusion list) (lhs:es) (rhs:es) : (bool * binary_tree ) = 
  let lhs = normalES lhs in 
  let rhs = normalES rhs in 
  let entail = string_of_inclusion lhs rhs in 
  if nallable lhs == true && nallable rhs==false then (false, Node (entail, []))
  else if isBot rhs then (false, Node (entail, []))
  else if reoccur evn lhs rhs then (true, Node (entail, []))
  else 
    let (fst:instance list) = getFst lhs in 
    let newEvn = append [(lhs, rhs)] evn in 
    let rec helper (acc:binary_tree list) (fst_list:instance list): (bool * binary_tree list) = 
      (match fst_list with 
        [] -> (true , acc) 
      | a::xs -> 
        let (result, (tree:binary_tree)) =  containment newEvn (derivative a lhs) (derivative a lhs) in 
        if result == false then (false, acc)
        else helper (tree:: acc) xs 
      )
    in 
    let (result, trees) =  helper [] fst in 
    (result, Node (entail, trees))  
    
  ;;




let check_containment lhs rhs : (bool * binary_tree ) = 
  containment [] lhs rhs
  ;;

let printReport (lhs:es) (rhs:es) :string =

  let (res, tree) = check_containment lhs rhs in 
  printTree ~line_prefix:"* " ~get_name ~get_children tree
  (*
  let entailment = (translate (normalize lhs)) ^ " |- " ^ (translate (normalize rhs)) (*and i = INC(lhs, rhs)*) in

  let startTimeStamp = Sys.time() in
  let (re, tree) =  printReportHelper lhs rhs in
  let verification_time = "[Verification Time: " ^ string_of_float (Sys.time() -. startTimeStamp) ^ " s]\n" in
  let result = printTree ~line_prefix:"* " ~get_name ~get_children tree in
  let buffur = ( "===================================="^"\n" ^(entailment)^"\n[Result] " ^(if re then "Succeed\n" else "Fail\n")  ^verification_time^" \n\n"^ result)
  in buffur
  *)
  ;;

(*
let main = 
  let (re, temp) = in 
  let tree = printTree ~line_prefix:"* " ~get_name ~get_children temp in 

  print_string (tree);
  *)

let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"

