open String
open List
open Ast
open Printf
open Parser
open Lexer
open Pretty
open Sys



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
    Bot -> []
  | Emp -> []
  | Instance ins  -> [ins] 
  | Con (es1, es2) -> if nallable es1 then append (getFst es1) (getFst es2) else getFst es1
  | Disj (es1, es2) -> append (getFst es1) (getFst es2)
  | Kleene esIn -> (getFst esIn) 
  | Ntimed (esIn, n) -> (getFst esIn) 
  ;;

let superSetOf (bigger:instance) (smaller:instance) :bool = 
  let rec helper li cur = 
    match li with 
      [] -> false 
    | x::xs -> if compareSignal x cur then true else helper xs cur
  in List.fold_left (fun acc a -> acc && helper bigger a ) true smaller ;;

let rec superESOf (bigger:es) (smaller:es) : bool = 
  match (bigger, smaller) with 
  | (Instance ins1, Instance ins2) -> superSetOf ins1 ins2
  | (Con (es1, es2), Con(es3, es4)) -> superESOf es1 es3 && superESOf es2 es4
  | (Disj (es1, es2), Disj(es3, es4))-> (superESOf es1 es3 && superESOf es2 es4) || (superESOf es1 es4 && superESOf es2 es3)
  | (Kleene es1, Kleene es2) -> superESOf es1 es2
  | (Ntimed (es1, n1), Ntimed(es2, n2)) -> superESOf es1 es2 && n1 == n2
  | (Disj (es1, es2), Con _)-> (superESOf es1 smaller ) || (superESOf es2 smaller)
  | _ -> false 
  ;; 

let rec reoccur (evn: inclusion list) (lhs:es) (rhs:es) :bool = 
    match evn with
      [] -> false 
    | (lhs', rhs')::xs -> 
      if superESOf rhs' rhs && superESOf lhs lhs' 
      then true 
      else reoccur xs lhs rhs
;;

 
 
 (* foldable 

  Coq
*)


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
  else if isBot lhs then (true, Node (entail, []))
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


  let entailment = (string_of_es (normalES lhs)) ^ " |- " ^ (string_of_es (normalES rhs)) (*and i = INC(lhs, rhs)*) in

  let startTimeStamp = Sys.time() in
  let (re, tree) =  check_containment lhs rhs in
  let verification_time = "[Verification Time: " ^ string_of_float (Sys.time() -. startTimeStamp) ^ " s]\n" in
  let result = printTree ~line_prefix:"* " ~get_name ~get_children tree in
  let buffur = ( "----------------------------------------"^"\n" ^(entailment)^"\n[Result] " ^(if re then "Succeed\n" else "Fail\n")  ^verification_time^" \n\n"^ result)
  in buffur
  
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

