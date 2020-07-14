
open Ast
open List
open Sys
open Unix
open Pretty
open Printf


let rec translateLTL (ltl:ltl) : es list =
  match ltl with 
    Lable str -> [Instance ([], [(str, One)]) ]
  | Next l -> List.map (fun a -> Con (Any, a)) (translateLTL l)
  | Global l -> List.map (fun a -> (Kleene a)) (translateLTL l)
  | OrLTL (l1, l2) -> 
    let temp1 =  translateLTL l1 in 
    let temp2 =  translateLTL l2 in 
    List.append temp1 temp2
  | Until (l1, l2) -> 
    let temp1 =  translateLTL l1 in 
    let temp2 =  translateLTL l2 in 
    List.flatten (List.map (fun a -> List.map (fun b -> Con (Kleene (a), b) ) temp2) temp1 )
  | Future l -> 
    let temp =  translateLTL l in 
    List.map (fun a-> Con(Kleene Any, a)) temp
  
  | NotLTL l -> 
    let temp =  translateLTL l in 
    List.map (fun a-> Not a) temp
  | Imply (l1, l2) -> 
    let temp1 =  translateLTL l1 in 
    let temp2 =  translateLTL l2 in 
    List.flatten (List.flatten (List.map (fun a -> List.map (fun b -> List.append [(Not a)] [b] ) temp2) temp1 ))


  | _ -> raise (Foo "translateLTL")
    (*
  

  
  | AndLTL (l1, l2) -> 
      let (pi1, ess1, varList1) =  translateLTL pi l1 varList in 
      let (pi2, ess2, varList2) =  translateLTL pi1 l2 varList1 in 
      (pi2, ESAnd (ess1, ess2), varList2)
*)
  ;;




let main = 
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in 
  
  let ic = open_in inputfile in
  try 
    let specs:(string list) =  (input_lines ic) in 
    let lines = List.fold_right (fun x acc -> acc ^ "\n" ^ x) ( specs) "" in 
    let ltlList:(ltl list) = Parser.ltl_p Lexer.token (Lexing.from_string  lines)  in

   
    let esList = List.map (fun ltl -> 
      translateLTL ltl ) ltlList in
    (*
    print_string (showLTLList ^ "\n==============\n");
    *)
    
    let producte = List.combine ltlList esList in

    let result = List.fold_right (fun (l,e) acc -> 
      let temp = List.fold_left (fun acc a -> acc ^"\n"^ string_of_es a) "" e in 
        let buffur = ( "===================================="^"\n" ^(showLTL l)^"\n\n[Translated to Effects] ===>\n " ^temp  ^" \n\n") in 

        acc ^  buffur) 
      (producte)  "" in 
    
    print_string (result^"\n");
    
    
    close_in ic                  (* 关闭输入通道 *) 

  with e ->                      (* 一些不可预见的异常发生 *)
    close_in_noerr ic;           (* 紧急关闭 *)
    raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

 ;;

  