open String
open List
open Ast
open Printf
open Parser
open Lexer
open Pretty
open Rewriting
open Sys



let rec can_fun (s:var) (prog:prog) (full:spec_prog list) :bool = 
  match prog with 
    Nothing -> false 
  | Pause -> false 
  | Seq (p1, p2) -> can_fun s p1 full || can_fun s p2 full
  | Par (p1, p2) -> can_fun s p1 full || can_fun s p2 full
  | Loop p -> can_fun s p full
  | Declear (v, p) -> can_fun s p full
  | Emit str -> if String.compare str s == 0 then true else false 
  | Present (v, p1, p2) -> can_fun s p1 full || can_fun s p2 full
  | Trap (mn, p) -> can_fun s p full
  | Exit _ -> false 
  | Run proIn -> 
    let rec helper modules = 
        match modules with 
          [] -> raise (Foo ("module "^proIn ^"undefined"))
        | x::xs -> 
        let (name, _, _, _, _, _) = x in
        if String.compare name proIn == 0 then x else helper xs 
      in 
      let (_, in_callee, out_callee, pre_callee, post_callee, body_calles) = helper full in 
      can_fun s body_calles full
  ;;

  
let compareSignal s1 s2 : bool =
  match (s1, s2) with 
    (One n1, One n2) -> String.compare n1 n2 == 0
  | (Zero n1 , Zero n2 ) -> String.compare n1 n2 == 0 
  | _ -> false 
  ;;

let rec oneOfFalse (sig_:signal) ss : bool =
  match ss with 
    [] -> false 
  | head_sig:: xs -> if compareSignal sig_ head_sig == false then true else oneOfFalse sig_ xs
;;
(*true return has controdiction, false means no controdiction *)
let rec checkHasFalse ss : bool = 
  match ss with 
  [] -> false 
| x::xs -> if oneOfFalse x xs then true else checkHasFalse xs 
;;



let rec oneOf (sig_:signal) ss : bool =
  match ss with 
    [] -> false 
  | sig_head:: xs -> 

  if compareSignal sig_ sig_head then true else oneOf sig_ xs
;;

let rec deleteRedundent sl : signal list = 
  match sl with 
    [] -> sl 
  | x::xs -> if oneOf x xs then deleteRedundent xs else List.append [x] (deleteRedundent xs)

  ;;
 
let rec normalES es: es =
  match es with 
  | Disj (Bot, es1) -> normalES es1
  | Disj (es1, Bot) -> normalES es1
  | Disj (es1, es2) -> Disj (normalES es1, normalES es2)
  | Con (Con(es1, es2), es3) -> normalES (Con (normalES es1, normalES (Con(es2, es3)) ))
  | Con (es1, es2) -> 
      let norES1 = normalES es1 in 
      let norES2 = normalES es2 in 
      (*print_string (string_of_es norES1);*)
      (match (norES1, norES2) with 
        (Emp, _) -> norES2 
      | (_, Emp) -> norES1
      | (Bot, _) -> Bot 
      | (_ , Bot) -> Bot 
      | _ -> Con (norES1, norES2)
      )

  | Instance ss -> 
    let ss1 = deleteRedundent ss in 
    if checkHasFalse (ss1) then  Bot else 
    (Instance ss1)
  | _ -> es 
  ;;

  (*
let add_Constain ((con, ss):instance) ((name, nowstate)) : instance= 
  (*if compareState nowstate One then 
  let (con', ss') = setTrue (con, ss) name in 
  (List.append con' [(name, nowstate)], ss')
  else
  *) 
  (List.append con [(name, nowstate)], ss)
  ;;
  *)

let rec es_To_state (es:es) :prog_states = 
  match es with 
  | Instance ins -> [(Emp, ins)]
  | Con (es1, es2) -> 
    let his_cur_list = es_To_state es2 in 
    List.map (fun (his,cur) -> (Con (es1, his),cur)) his_cur_list
    
  | Disj (es1, es2) -> List.append (es_To_state es1) (es_To_state es2)
  | Kleene esIn -> 
    let his_cur_list = es_To_state esIn in 
    List.map (fun (his,cur) -> (Con (es, his), cur)) his_cur_list
  | Ntimed (esIn, n) ->
    assert (n>1);
    let his_cur_list = es_To_state esIn in 
    List.map (fun (his,cur) -> (Con (Ntimed (esIn, n-1), his), cur)) his_cur_list

  | _ -> raise (Foo "there is a EMP OR BOT HERE")
  ;;


let rec state_To_es (state:prog_states):es = 
  List.fold_left (fun acc (a, b) -> Disj (acc, (Con (a, Instance b)))) Bot state;;
  
let rec setTrue (sig_list:instance) (name) : instance= 
  let rec helper (inn:signal list ):signal list  = 
    (match inn with 
    [] -> raise  (Foo (name^" is not decleared"))
  | sig_head::xs -> 
    if compareSignal sig_head (One name) == true then List.append [(One name)] xs else  List.append [sig_head] (helper xs)
    )
  in helper sig_list
  ;;

let make_nothing (evn: string list) : signal list = 
  List.map (fun a -> (Zero a) ) evn 
  ;;

let rec forward (evn: string list ) (current:prog_states) (prog:prog) (original:prog) (full: spec_prog list): prog_states =
  match prog with 
    Nothing -> current
  | Emit s -> 
    List.map (fun (his, curr) -> (his, setTrue curr s)) current
  | Pause -> 
    let helper (his, curr) = 
      let newHis = Con (his, Instance curr) in 
      let newCurr = (make_nothing evn) in 
      (newHis, newCurr)
    in List.map (helper) current
  | Seq (p1, p2) ->  
    let states1 = forward evn current p1 original full in 
    forward evn states1 p2 original full
  | Declear (s, progIn ) -> 
    forward (List.append evn [s]) (List.map (fun (his, (curr)) -> (his, (List.append curr [(Zero s)]))) current) progIn original full




  | Present (s, p1, p2) -> 
  
    let eff1 = forward evn (List.map (fun (his, cur)-> (his, List.append [(One s)] cur ) ) current) p1 original full in 
    let eff2 = forward evn (List.map (fun (his, cur)-> (his, List.append [(Zero s)] cur ) ) current) p2 original full in 
    (*if can_fun s original full == false then eff2 else *)
    List.append eff1 eff2
  
  | Run mn -> 
      let rec helper modules = 
        match modules with 
          [] -> raise (Foo ("module "^mn ^"undefined"))
        | x::xs -> 
        let (name, _, _, _, _, _) = x in
        if String.compare name mn == 0 then x else helper xs 
      in 
      let (_, in_callee, out_callee, pre_callee, post_callee, body_calles) = helper full in 
      let (res, tree) = check_containment (normalES (state_To_es current) ) pre_callee in 
      if res == false then raise (Foo ("error when calling "^mn^"\n"))
      else 
      List.flatten (List.map (fun (his, curr) -> es_To_state (Con (his, post_callee))) current)

    
  | _ -> raise (Foo "not there forward")
  (*
  
  

  | Present (s, p1, p2) -> 
    let eff1 = forward (evn, (history, add_Constain curr (s, One) )) p1 toCheck in 
    let eff2 = forward (evn, (history, add_Constain curr (s, Zero) )) p2 toCheck in 
    if can_fun s toCheck == false then eff2 else 
    List.append eff1 eff2
*)
  ;;

let verifier (spec_prog:spec_prog) (full: spec_prog list):string = 
  let (nm, inp_sig, oup_sig, pre,  post, prog) = spec_prog in 
  let final_states = forward (append inp_sig oup_sig) (es_To_state pre) prog prog full in 
  let final_effects = normalES (state_To_es final_states)  in 
  string_of_inclusion final_effects post ^ "\n" ^
  printReport final_effects post;;

let forward_verification (progs:spec_prog list):string = 
  List.fold_left (fun acc a -> acc ^ "\n\n" ^ verifier a progs) "" progs ;; 

let () =
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
(*    let outputfile = (Sys.getcwd ()^ "/" ^ Sys.argv.(2)) in
print_string (inputfile ^ "\n" ^ outputfile^"\n");*)
  let ic = open_in inputfile in
  try
      let lines =  (input_lines ic ) in
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in
      let progs = Parser.full_prog Lexer.token (Lexing.from_string line) in

      (*print_string (string_of_full_prog progs^"\n");*)
      print_string ( (forward_verification progs) ^"\n");
      
      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;
