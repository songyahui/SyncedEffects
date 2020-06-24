open String
open List
open Ast
open Printf
open Parser
open Lexer
open Pretty
open Sys


let rec append_history_now (history:es) (now: signal list) :es = 
  match history with 
    Bot -> Bot
  | Emp -> Instance now 
  | Instance ss  ->  Con (history, Instance now)
  | Or (es1, es2) ->  Or (append_history_now es1 now, append_history_now es2 now)
  | Con (es1, es2) -> Con (es1, append_history_now es2 now)
  | Kleene esIn -> Con (history , Instance now)
;;


let rec append_es_es (es1) (es2) :es = 
  match es1 with
    Bot -> Bot
  | Emp -> es2
  | Instance ss1  ->  
        (match es2 with 
          Bot -> Bot 
        | Emp -> es1
        | Instance ss2 -> Instance (List.append ss1 ss2)
        | Con (es21, es22) -> Con (append_es_es es1 es21, es22)
        | Or (es21, es22) -> Or (append_es_es es1 es21, append_es_es es1 es22)
        | Kleene esIn2 -> Or (es1, Con (append_es_es es1 esIn2, es2))
        )
  | Or (es11, es12) ->  Or (append_es_es es11 es2, append_es_es es12 es2)
  | Con (es11, es12) -> Con (es11, append_es_es es12 es2)
  | Kleene esIn1 -> Or (es2, Con (es1 , append_es_es esIn1 es2))

  ;;

let rec zip_es_es (es_1) (es_2) :es = 

  let rec helper acc es1 es2: es = 
    match es1 with 
      Bot -> Con (acc,  es2)
    | Emp -> Con (acc, es2)
    | Instance ss1 -> 
        (match es2 with 
          Bot -> Con (acc, es1)
        | Emp -> Con (acc, es1)
        | Instance ss2 -> Con (acc, Instance (List.append ss1 ss2))
        | Or (es21, es22) ->Or (helper acc es1 es21, helper acc es1 es22)
        | Con (es21, es22) -> Con  (helper acc es1 es21, es22)
        | Kleene es2In -> Or (Con (acc, es1), helper acc es1 (Con (es2In, es2)))
        )
    | Or (es11, es12) -> Or (helper acc es11 es2, helper acc es12 es2)
    | Con(es11, es12) -> Con  (helper acc es11 es2, es12)
    | Kleene es1In -> Or (Con (acc, es2), helper acc es2 (Con (es1In, es1)) )


  in helper Emp es_1 es_2
  ;;

let rec checkExit name ss : bool = 
  match ss with 
    [] -> false
  | (str, state)::xs -> if String.compare name str == 0 then true else checkExit name xs

  ;;

let rec disjunES (esList) : es =
  let rec helper acc esL : es = 
    match esL  with 
      [] -> acc
    | x ::xs  -> helper (Or (acc, x)) xs
  in helper Emp esList

  ;;


let make_nothing (evn: string list) : signal list = 
  List.map (fun a -> (a, Zero) ) evn 
  ;;

let rec splitESfromLast es: (es * ss) list =
  match es with 
    Instance ss -> [(Emp, ss)]
  | Or (es1, es2) -> List.append (splitESfromLast es1) (splitESfromLast es2)
  | Con (es1, es2) -> 
    let listOfFL = splitESfromLast es2 in 
    List.fold_left (fun acc (f, l) -> List.append acc [(Con(es1, f), l)]) [] listOfFL
  | _ -> raise (Foo "splitESfromLast _")
  ;;

let rec forward (prog:prog) (evn: string list) ((history, now):(es* signal list)) : es =
  match prog with 
    Nothing -> append_history_now history (List.append now (make_nothing evn))
  | Pause -> (append_history_now (append_history_now history now) [])
  | Seq (p1, p2) ->  
    let temp1 = forward p1 evn (Emp, now) in 
    let temp2 = forward p2 evn (Emp, now) in 
    Con (history,  append_es_es temp1 temp2)
  | Par (p1, p2) ->  
    let temp1 = forward p1 evn (Emp, now) in 
    let temp2 = forward p2 evn (Emp, now) in 
    Con (history, zip_es_es temp1 temp2)
  | Loop pIn -> 
    let temp = forward pIn evn (Emp, now) in 
    Con (history, Kleene temp)
  | Declear (s, progIn ) -> forward progIn (List.append evn [s]) (history, now)
  | Emit s -> append_history_now history (List.append now [(s, One)])
  | Present (s, p1, p2) -> 
    let temp1 = forward p1 evn (Emp, List.append now [(s, One)]) in 
    let temp2 = forward p2 evn (Emp, List.append now [(s, Zero)]) in 
    Or (temp1, temp2)
  | Trap (name, pIn) -> 
    let temp = forward pIn evn (Emp, now) in 
    let listOfFL = splitESfromLast temp in 
    let allRes = List.map (fun (f, l) -> 
      if checkExit ("Exit_"^name) l then f else Kleene f
    ) listOfFL
    in 
    disjunES allRes
    
  | Exit name -> Con (history, Instance (List.append now [("Exit_"^name, One )]))
  ;;

let fowward_inter prog : es = 
  forward prog [] (Emp, []) ;;


let () =
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
(*    let outputfile = (Sys.getcwd ()^ "/" ^ Sys.argv.(2)) in
print_string (inputfile ^ "\n" ^ outputfile^"\n");*)
  let ic = open_in inputfile in
  try
      let lines =  (input_lines ic ) in
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in
      let prog = Parser.prog Lexer.token (Lexing.from_string line) in

      
      print_string (string_of_es (fowward_inter prog) ^"\n");
      
      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;
