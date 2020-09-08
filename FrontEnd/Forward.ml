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
  

let make_nothing (evn: string list) : signal list = 
  List.map (fun a -> (Zero a) ) evn 
  ;;

let rec forward (evn: string list ) (current:prog_states) (prog:prog) (original:prog) (full: spec_prog list): prog_states =
  match prog with 
    Nothing -> 
  
    List.map (fun (his, curr) -> 
    (his, List.append (make_nothing evn) curr )) current
  | Emit s -> 
    List.map (fun (his, curr) -> (his, List.append [(One s)] curr )) current
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
    forward (List.append evn [s]) ( current) progIn original full




  | Present (s, p1, p2) -> 
  
    let eff1 = forward evn (List.map (fun (his, cur)-> (his, List.append [(One s)] cur ) ) current) p1 original full in 
    let eff2 = forward evn (List.map (fun (his, cur)-> (his, List.append [(Zero s)] cur ) ) current) p2 original full in 
    
    (*
    print_string(string_of_prg_state eff1);

    print_string(string_of_prg_state eff2);
    *)

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
  ;;

let verifier (spec_prog:spec_prog) (full: spec_prog list):string = 
  let (nm, inp_sig, oup_sig, pre,  post, prog) = spec_prog in 
  let final_states = forward ((*append inp_sig*) oup_sig) (es_To_state pre) prog prog full in 
  let final_effects =  normalES (state_To_es final_states)  in 
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
