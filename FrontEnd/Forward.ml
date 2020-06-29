open String
open List
open Ast
open Printf
open Parser
open Lexer
open Pretty
open Sys


let rec append_history_now (history:es) ((cons, now) : instance) :es = 
  match history with 
    Bot -> Bot
  | Emp -> Instance (cons, now) 
  | Instance _  ->  Con(history, Instance (cons, now))
  | Con (es1, es2) -> Con (es1, append_history_now es2 (cons, now))
  | Kleene esIn -> Con (history , Instance (cons, now))
;;


let rec append_es_es (es1) (es2) : es = 
  match es1 with
    Bot -> Bot
  | Emp -> es2
  | Instance (con1, ss1)  ->  
        (match es2 with 
          Bot -> Bot 
        | Emp -> es1
        | Instance (con2, ss2) -> Instance (List.append con1 con2, List.append ss1 ss2)
        | Con (es21, es22) -> Con (append_es_es es1 es21, es22)
        | Kleene esIn2 -> Con (append_es_es es1 esIn2, es2)
        )
  | Con (es11, es12) -> Con (es11, append_es_es es12 es2)
  | Kleene esIn1 -> Con (es1 , append_es_es esIn1 es2)

  ;;



let rec checkExit name (con, ss) : bool = 
  match ss with 
    [] -> false
  | (str, state)::xs -> if String.compare name str == 0 then true else checkExit name (con, xs)

  ;;

  (*
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
*)

let make_nothing (evn: string list) : mapping list = 
  List.map (fun a -> (a, Zero) ) evn 
  ;;

  
let rec splitESfromLast es: (es * instance) =
  match es with 
    Instance ss -> (Emp, ss)
  | Con (es1, es2) -> 
    let (his, cu) = splitESfromLast es2 in 
    (Con (es1, his), cu)
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

let rec deleteRedundent sl : mapping list = 
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

  | Instance (con, ss) -> 
    let con1 = deleteRedundent con in 
    let ss1 = deleteRedundent ss in 
    if checkHasFalse (ss1) then  Bot else (Instance (con1, ss1))
  | Kleene esIn -> Kleene (normalES esIn)
  | _ -> es 
  ;;

let rec unionTwoList (sl1) (sl2) : mapping list = 
  let app = deleteRedundent (List.append sl1 sl2) in 
  let rec helper acc sl : mapping list =  
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


        | Con (es21, es22) -> Con  (helper acc es1 es21, es22)
        | Kleene es2In -> raise (Foo "zip_es_es in ");
        )
    | Con(es11, es12) -> Con  (helper acc es11 es2, es12)
    | Kleene es1In -> raise (Foo "zip_es_es out ");


  in helper Emp (normalES es_1) (normalES es_2)
  ;;

let rec setTrue ((con, ss):instance) (name) : instance= 
  let rec helper (inn:mapping list ):mapping list  = 
    (match inn with 
    [] -> raise  (Foo (name^" is not decleared"))
  | (x, state)::xs -> 
    if String.compare x name == 0 then List.append [(x, One)] xs else  List.append [(x, state)] (helper xs)
    )
  in (con, helper ss)
  ;;

let add_Constain ((con, ss):instance) ((name, nowstate)) : instance= 
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

let rec forward (precondition:precondition) (prog:prog) (toCheck:prog) :postcondition =
  let (evn, (history, curr)) = precondition in 
  match prog with 

    Nothing -> [(history, curr)]
  | Emit s -> 
    let newCurr = setTrue curr s in 
    [(history, newCurr)]
  | Pause -> 
    let newHis = Con (history, Instance curr) in 
    let newCurr = ([], make_nothing evn) in 
    [(newHis, newCurr)]
  | Present (s, p1, p2) -> 
    let eff1 = forward (evn, (history, add_Constain curr (s, One) )) p1 toCheck in 
    let eff2 = forward (evn, (history, add_Constain curr (s, Zero) )) p2 toCheck in 
    List.append eff1 eff2
(*    if can_fun s origin == false then temp2 else 
    Or (temp1, temp2)
*)
  | Seq (p1, p2) ->  
    let eff1 = forward (evn, (history, curr )) p1 toCheck in 
    List.flatten (List.map (fun a -> 
      let (newHis, newCurr) = a in 
      forward (evn, (newHis, newCurr)) p2 toCheck
    ) eff1)
  | Par (p1, p2) ->  
    let eff1 = forward (evn, (history, curr )) p1 toCheck in 
    (*print_string (string_of_es temp1^"\n");*)
    let eff2 = forward (evn, (history, curr )) p2 toCheck in 
    (*print_string (string_of_es temp2^"\n");*)
    List.flatten (List.map (fun (his_a, cur_a) -> 
      List.map (fun (his_b, cur_b) -> 
        let temp = zip_es_es (Con(his_a,  Instance cur_a )) (Con (his_b, Instance cur_b ))
        in splitESfromLast temp
        ) eff2) eff1 )

    (*normalES (append_history_now history (List.append now (make_nothing evn)))*)
  | Declear (s, progIn ) -> 
    let (con, ss) = curr in 
    forward ((List.append evn [s]), (history, (con, List.append ss [(s, Zero)]) )) progIn toCheck

  | Exit (name, d)-> 
    let (con, ss) = curr in 
    forward (evn, (history, (List.append con [("Exit_"^name, One )] ,  ss ) )) Nothing toCheck



   (*

  | Loop pIn -> 
    let eff = forward (evn, (history, curr )) pIn toCheck in 
    let eff = forward (evn, (history, curr )) pIn toCheck in 

    Con (history, Kleene temp)

  | Trap (name, pIn) -> 
    let temp = normalES (forward origin pIn evn (Emp, now)) in 
    let listOfFL = splitESfromLast temp in 
    let allRes = List.map (fun (f, l) -> 
      if checkExit ("Exit_"^name) l then f else Kleene f
    ) listOfFL
    in 
    disjunES allRes
    

      *)
  | _ -> [(history, curr)]
  ;;

(*
let rec getAllTheSIgnals (prog) acc: string list = 
  match prog with 
    Declear (s, progIn ) -> getAllTheSIgnals progIn (List.append acc [s])
  | _ -> acc 
  ;;
  *)

let fowward_inter prog : postcondition = 
  (*let evn = getAllTheSIgnals prog [] in *)
  (*let now = make_nothing evn in *)
  let precondition = ([], (Emp, ([], []))) in 
  (forward precondition prog prog)
  
  ;;

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
(*| Or (es1, es2) -> 
  let norES1 = logical_check es1 in 
  let norES2 = logical_check es2 in 
  (match (norES1, norES2) with 
    (Bot, Bot) -> Bot 
  | (Bot, _) -> norES2
  | (_, Bot) -> norES1
  | _ -> Or (norES1, norES2)
  )
  *)
| Instance (con, ss) -> 
  let con1 = deleteRedundent con in 
  let ss1 = deleteRedundent ss in 
  if checkHasFalse (List.append con1 ss1) then  Bot else (Instance (con1, ss1))
| Kleene esIn -> Kleene (logical_check esIn)
| _ -> es 
;;


let analyse prog : string = 
  let forward = fowward_inter prog in  
  (*let logical_res = logical_check forward in *)
  let info = "\n================\nForward res = " ^ string_of_postcondition  forward  in 
   (info)

   ;;


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
