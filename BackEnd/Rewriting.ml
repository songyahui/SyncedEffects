open String
open List
open Ast
open Printf
open Parser
open Lexer
open Pretty
open Sys






let rec reoccur (evn: inclusion list) (lhs:es) (rhs:es) :bool = 
    match evn with
      [] -> false 
    | (lhs', rhs')::xs -> 
      if superESOf rhs' rhs && superESOf lhs lhs' 
      then true 
      else reoccur xs lhs rhs
;;






let rec containment (evn: inclusion list) (lhs:es) (rhs:es) : (bool * binary_tree ) = 
  let lhs = normalES lhs in 
  let rhs = normalES rhs in 
  let entail = string_of_inclusion lhs rhs in 
  if nullable lhs == true && nullable rhs==false then (false, Node (entail^ "   [DISPROVE]", []))
  else if isBot lhs then (true, Node (entail^ "   [Bot-LHS]", []))
  else if isBot rhs then (false, Node (entail^ "   [Bot-RHS]", []))
  else if reoccur evn lhs rhs then (true, Node (entail^ "   [Reoccur]", []))
  else 
  (*match lhs with 
    Disj (lhs1, lhs2) -> 
      let (re1, tree1) = containment evn lhs1 rhs in 
      let (re2, tree2) = containment evn lhs2 rhs in 
      (re1 && re2, Node (entail^ "   [LHS-DISJ]", [tree1; tree2]))
  | _ -> *)
    let (fst:instance list) = getFst lhs in 
    let newEvn = append [(lhs, rhs)] evn in 
    let rec helper (acc:binary_tree list) (fst_list:instance list): (bool * binary_tree list) = 
      (match fst_list with 
        [] -> (true , acc) 
      | a::xs -> 
        let (result, (tree:binary_tree)) =  containment newEvn (derivative a lhs) (derivative a rhs) in 
        if result == false then (false, (tree:: acc))
        else helper (tree:: acc) xs 
      )
    in 
    let (result, trees) =  helper [] fst in 
    (result, Node (entail^ "   [UNFOLD]", trees))  
    
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

