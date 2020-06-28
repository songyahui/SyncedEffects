open String
open List
open Ast
open Printf
open Parser
open Lexer
open Pretty
open Sys


let rec append_history_now (history:es) ((cons, now) : ss) :es = 
  match history with 
    Bot -> Bot
  | Emp -> Instance (cons, now) 
  | Instance _  ->  Con(history, Instance (cons, now))
  | Or (es1, es2) ->  Or (append_history_now es1 (cons, now), append_history_now es2 (cons, now))
  | Con (es1, es2) -> Con (es1, append_history_now es2 (cons, now))
  | Kleene esIn -> Con (history , Instance (cons, now))
;;


let rec append_es_es (es1) (es2) :es = 
  match es1 with
    Bot -> Bot
  | Emp -> es2
  | Instance (con1, ss1)  ->  
        (match es2 with 
          Bot -> Bot 
        | Emp -> es1
        | Instance (con2, ss2) -> Instance (List.append con1 con2, List.append ss1 ss2)
        | Con (es21, es22) -> Con (append_es_es es1 es21, es22)
        | Or (es21, es22) -> Or (append_es_es es1 es21, append_es_es es1 es22)
        | Kleene esIn2 -> Or (es1, Con (append_es_es es1 esIn2, es2))
        )
  | Or (es11, es12) ->  Or (append_es_es es11 es2, append_es_es es12 es2)
  | Con (es11, es12) -> Con (es11, append_es_es es12 es2)
  | Kleene esIn1 -> Or (es2, Con (es1 , append_es_es esIn1 es2))

  ;;



let rec checkExit name (con, ss) : bool = 
  match ss with 
    [] -> false
  | (str, state)::xs -> if String.compare name str == 0 then true else checkExit name (con, xs)

  ;;

let rec disjunES (esList) : es =
  let rec helper acc esL : es = 
    match esL  with 
      [] -> acc
    | x ::xs  -> helper (Or (acc, x)) xs
  in 
    match esList with 
      [] -> Emp
    | x::xs -> helper x xs

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



let compareState s1 s2 : bool =
  match (s1, s2) with 
    (One, One) -> true 
  | (Zero, Zero) -> true 
  | _ -> false 
  ;;

let rec oneOf (var, state) ss : bool =
  match ss with 
    [] -> false 
  | (var1, state1):: xs -> if String.compare var var1 ==0 && compareState state1 state then true else oneOf (var, state) xs
;;

let rec deleteRedundent sl : signal list = 
  match sl with 
    [] -> sl 
  | x::xs -> if oneOf x xs then deleteRedundent xs else List.append [x] (deleteRedundent xs)

  ;;

let rec oneOfFalse (var, state) ss : bool =
  match ss with 
    [] -> false 
  | (var1, state1):: xs -> if String.compare var var1 ==0 && compareState state1 state == false then true else oneOfFalse (var, state) xs
;;

let rec checkHasFalse ss : bool = 
  match ss with 
  [] -> false 
| x::xs -> if oneOfFalse x xs then true else checkHasFalse xs 
;;


  
let rec normalES es: es =
  match es with 
    Con (es1, es2) -> 
      let norES1 = normalES es1 in 
      let norES2 = normalES es2 in 
      (match (norES1, norES2) with 
        (Emp, _) -> norES2 
      | (Bot, _) -> Bot 
      | (_ , Bot) -> Bot 
      | _ -> Con (norES1, norES2)
      )
  | Or (es1, es2) -> 
    let norES1 = normalES es1 in 
    let norES2 = normalES es2 in 
    (match (norES1, norES2) with 
      (Bot, Bot) -> Bot 
    | (Bot, _) -> norES2
    | (_, Bot) -> norES1
    | _ -> Or (norES1, norES2)
    )
  | Instance (con, ss) -> 
    let con1 = deleteRedundent con in 
    let ss1 = deleteRedundent ss in 
    if checkHasFalse (ss1) then  Bot else (Instance (con1, ss1))
  | Kleene esIn -> Kleene (normalES esIn)
  | _ -> es 
  ;;

let rec unionTwoList (sl1) (sl2) : signal list = 
  let app = deleteRedundent (List.append sl1 sl2) in 
  let rec helper acc sl : signal list =  
    match sl with
      [] -> acc 
    | (nm, sta)::xs -> if oneOfFalse (nm, sta) app then helper (List.append acc [(nm, One)]) xs else helper (List.append acc [(nm, sta)]) xs
  in helper [] app
  ;;

let rec zip_es_es (es_1) (es_2) :es = 

  let rec helper acc es1 es2: es = 
    match es1 with 
      Bot -> Con (acc,  es2)
    | Emp -> Con (acc, es2)
    | Instance (con1, ss1) -> 
        (match es2 with 
          Bot -> Con (acc, es1)
        | Emp -> Con (acc, es1)
        | Instance (con2, ss2) -> 
        (*
          print_string ("\n----------\n inportant \n" ^ string_of_es es1 ^ " ::: " ^ string_of_es es2^"\n");
          print_string ("\n kkkkk \n" ^ string_of_es (normalES (Instance (con1, ss2))) ^ " ::: " ^ string_of_es (normalES (Instance (con2, ss1) ))^"\n");

          print_string (string_of_sl (unionTwoList ss1 ss2));
          *)
          (match (normalES (Instance (con1, ss2)), normalES (Instance (con2, ss1) )) with 
            (Bot, _) -> Bot
          | (_, Bot) -> Bot
          | _ -> Con (acc, Instance (List.append con1 con2, unionTwoList ss1 ss2))
          )


        | Or (es21, es22) -> Or (helper acc es1 es21, helper acc es1 es22)
        | Con (es21, es22) -> Con  (helper acc es1 es21, es22)
        | Kleene es2In -> Or (Con (acc, es1), helper acc es1 (Con (es2In, es2)))
        )
    | Or (es11, es12) -> Or (helper acc es11 es2, helper acc es12 es2)
    | Con(es11, es12) -> Con  (helper acc es11 es2, es12)
    | Kleene es1In -> Or (Con (acc, es2), helper acc es2 (Con (es1In, es1)) )


  in helper Emp (normalES es_1) (normalES es_2)
  ;;

let rec setTrue ((con, ss):ss) (name) : ss= 
  let rec helper (inn:signal list ):signal list  = 
    (match inn with 
    [] -> raise  (Foo (name^" is not decleared"))
  | (x, state)::xs -> 
    if String.compare x name == 0 then List.append [(x, One)] xs else  List.append [(x, state)] (helper xs)
    )
  in (con, helper ss)
  ;;

let add_Constain ((con, ss):ss) ((name, nowstate)) : ss= 
  (*if compareState nowstate One then 
  let (con', ss') = setTrue (con, ss) name in 
  (List.append con' [(name, nowstate)], ss')
  else
  *) (List.append con [(name, nowstate)], ss)
  ;;

let rec can_fun (s:var) (prog:prog) :bool = 
  match prog with 
    Nothing -> false 
  | Pause -> false 
  | Seq (p1, p2) -> can_fun s p1 || can_fun s p2
  | Par (p1, p2) -> can_fun s p1 || can_fun s p2
  | Loop p -> can_fun s p
  | Declear (v, p) -> can_fun s p 
  | Emit str -> if String.compare str s == 0 then true else false 
  | Present (v, p1, p2) -> can_fun s p1 || can_fun s p2
  | Trap (n, p) -> can_fun s p 
  | Exit _ -> false 
  ;;

let rec forward origin (prog:prog) (evn: string list) ((history, now):(es*ss)) : es =
  match prog with 
    Nothing -> normalES (append_history_now history now)
    (*normalES (append_history_now history (List.append now (make_nothing evn)))*)
  | Pause -> normalES (Con ((append_history_now history now),  Instance ([], make_nothing evn)))
  | Seq (p1, p2) ->  
    let temp1 =  normalES (forward origin p1 evn (Emp, now)) in 
    (*print_string (string_of_es temp1^"\n");*)
    let listOfFL = splitESfromLast temp1 in 
    let temp2 = List.map (fun (a) -> normalES (forward origin p2 evn a)) listOfFL in 
    (*print_string (string_of_es (disjunES temp2) ^"\n");*)

    Con (history,  disjunES temp2)
  | Par (p1, p2) ->  
    let temp1 = normalES (forward origin p1 evn (Emp, now)) in 
    (*print_string (string_of_es temp1^"\n");*)
    let temp2 =  (forward origin p2 evn (Emp, now)) in 
    (*print_string (string_of_es temp2^"\n");*)

    Con (history, zip_es_es temp1 temp2)
  | Loop pIn -> 
    let temp = normalES (forward origin pIn evn (Emp, now)) in 
    Con (history, Kleene temp)

  | Declear (s, progIn ) -> 
    (match now with 
      (con, ss) ->
    normalES (forward origin progIn (List.append evn [s]) (history,  (con, List.append ss [(s, Zero)])))
    )
  | Emit s -> append_history_now history (setTrue now s)
  | Present (s, p1, p2) -> 
    
    let temp1 = normalES (forward origin p1 evn (Emp, add_Constain now (s, One))) in 
    (*print_string (string_of_es temp1^"\n");*)
    let temp2 = normalES (forward origin p2 evn (Emp, add_Constain now (s, Zero))) in 
    (*print_string (string_of_es temp2^"\n");*)
    if can_fun s origin == false then temp2 else 
    Or (temp1, temp2)
  | Trap (name, pIn) -> 
    let temp = normalES (forward origin pIn evn (Emp, now)) in 
    let listOfFL = splitESfromLast temp in 
    let allRes = List.map (fun (f, l) -> 
      if checkExit ("Exit_"^name) l then f else Kleene f
    ) listOfFL
    in 
    disjunES allRes
    
  | Exit name -> 
    match now with 
      (con, ss) -> Con (history, Instance (con, List.append ss [("Exit_"^name, One )]))
  ;;

(*
let rec getAllTheSIgnals (prog) acc: string list = 
  match prog with 
    Declear (s, progIn ) -> getAllTheSIgnals progIn (List.append acc [s])
  | _ -> acc 
  ;;
  *)

let fowward_inter prog : es = 
  (*let evn = getAllTheSIgnals prog [] in *)
  (*let now = make_nothing evn in *)
  normalES (forward prog prog [] (Emp, ([], []))) ;;

let rec logical_check es :es = 
  match es with 
  Con (es1, es2) -> 
    let norES1 = logical_check es1 in 
    let norES2 = logical_check es2 in 
    (match (norES1, norES2) with 
      (Emp, _) -> norES2 
    | (Bot, _) -> Bot 
    | (_ , Bot) -> Bot 
    | _ -> Con (norES1, norES2)
    )
| Or (es1, es2) -> 
  let norES1 = logical_check es1 in 
  let norES2 = logical_check es2 in 
  (match (norES1, norES2) with 
    (Bot, Bot) -> Bot 
  | (Bot, _) -> norES2
  | (_, Bot) -> norES1
  | _ -> Or (norES1, norES2)
  )
| Instance (con, ss) -> 
  let con1 = deleteRedundent con in 
  let ss1 = deleteRedundent ss in 
  if checkHasFalse (List.append con1 ss1) then  Bot else (Instance (con1, ss1))
| Kleene esIn -> Kleene (logical_check esIn)
| _ -> es 
;;


let analyse prog : string = 
  let forward = fowward_inter prog in  
  let logical_res = logical_check forward in 
  let info = "\n================\nForward res = " ^ string_of_es  forward ^ "\n" ^string_of_es logical_res ^ "\n" in 
   (info)


let () =
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
(*    let outputfile = (Sys.getcwd ()^ "/" ^ Sys.argv.(2)) in
print_string (inputfile ^ "\n" ^ outputfile^"\n");*)
  let ic = open_in inputfile in
  try
      let lines =  (input_lines ic ) in
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in
      let prog = Parser.prog Lexer.token (Lexing.from_string line) in

      (*print_string (string_of_prog prog^"\n");*)
      print_string ( (analyse prog) ^"\n");
      
      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;
