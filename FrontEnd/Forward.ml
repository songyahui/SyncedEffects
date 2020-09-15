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
  | Suspend (p, s) -> can_fun s p full
  ;;

  

let rec es_To_state (es:es) :prog_states = 
  match es with 
  | Emp -> [(Emp, None)]
  | Instance ins -> [(Emp, Some ins)]
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
  List.fold_left (fun acc (a, b) -> 
  match b with 
    None -> Disj (acc, a)
  | Some b -> 
  Disj (acc, (Con (a, Instance b)))) Bot state;;
  
let rec addToHead (ins: instance) (es:es) :es = 
  match es with
  | Instance ins1 ->  Instance (List.append ins1 ins )
  | Con (es1, es2) -> Con (addToHead ins es1, es2) 
  | Disj (es1, es2) -> Disj (addToHead  ins es1, addToHead ins es2)
  | Kleene esIn -> Con (addToHead ins esIn, es)
  | Ntimed (esIn, n) -> Con (addToHead ins esIn, Ntimed (esIn, n-1))
  | _ -> es 
  ;;

let make_nothing (evn: string list) : signal list = 
  List.map (fun a -> (Zero a) ) evn 
  ;;


let rec split_es_head_tail (es:es) :(instance * es) list = 
  match es with 
  | Instance ins -> [(ins, Emp)]
  | Con (es1, es2) -> 
    let head_tail_list = split_es_head_tail es1 in 
    List.map (fun (head,tail) -> (head, Con (tail, es2))) head_tail_list
    
  | Disj (es1, es2) -> List.append (split_es_head_tail es1) (split_es_head_tail es2)
  | Kleene esIn -> 
    let head_tail_list = split_es_head_tail esIn in 
    List.map (fun (head,tail) -> (head, Con (tail, es))) head_tail_list
  | Ntimed (esIn, n) ->
    assert (n>1);
    let head_tail_list = split_es_head_tail esIn in 
    List.map (fun (head,tail) -> (head, Con (tail, Ntimed (esIn, n-1)))) head_tail_list

  | _ -> raise (Foo "there is a EMP OR BOT HERE in split_es_head_tail")
  ;;

let isEmp xs : bool = 
  match xs with 
    [] -> true 
  | _ -> false 
;;

let equla_List_of_State left right : bool= 
  true
  ;;

let rec forward (evn: string list ) (current:prog_states) (prog:prog) (original:prog) (full: spec_prog list): prog_states =
  match prog with 
    Nothing -> 
    List.map (fun (his, curr) -> 
    (his,  curr )) current
  | Emit s -> 
    List.map (fun (his, curr) -> 
    (match curr with 
      None -> raise (Foo "Emit doesn't work...")
     | Some curr -> (his, Some (List.append [(One s)] curr) ))) current
  | Pause -> 
    let helper (his, curr) = 
      let newCurr = Some [] in 
      (match curr with 
        None -> (his, newCurr)
      | Some curr -> let newHis = Con (his, Instance curr) in 
      (newHis, newCurr)
      )
    in List.map (helper) current
  | Seq (p1, p2) ->  
    let states1 = forward evn current p1 original full in 
    forward evn states1 p2 original full
  | Declear (s, progIn ) -> 
    forward (List.append evn [s]) ( current) progIn original full

  | Loop prog ->
     (*forward evn current prog original full 
     *)
     List.flatten (List.map (fun (his, curr) -> 
      match curr with 
        None -> raise (Foo "something wrong before entering loop")
      | Some curr1 ->
        (*(*fixpoint computing*)

        let rec helper curent_states previous_states: prog_states list= 
          if equla_List_of_State curent_states (hd previous_states) then previous_states
          else 
            let next_state = List.flatten (List.map (fun (new_his, new_cur) -> 
              forward evn [(Emp, new_cur )] prog original full
            )curent_states)
            in helper next_state (curent_states::previous_states)
        in 
        let newState_list = forward evn [(Emp, curr )] prog original full in
        let final_effect = helper newState_list [] in 
        List.map ()
        
        final_effect
        *)
      
       (* by cases *)
        let newState_list = forward evn [(Emp, Some [] )] prog original full in
        List.flatten (
          List.map (fun (new_his, new_curr) ->
          let new_his = normalES new_his in 
          match new_curr with 
            None -> raise (Foo "something wrong inside loop")
          | Some new_curr1 -> 
            let head_tail_list = split_es_head_tail (normalES new_his) in 
            List.map (fun (head, tail) ->
            match (isEmp (head), isEmp new_curr1) with
              (*两头都有pause, his.curr.(tail.head)^* *)
              (true, true) -> (Con (his, Con (Instance curr1, Kleene (Con (tail, Instance head)))), None)
              (*右边有pause, his.(curr+head).(tail.head)^* *)
            | (false, true) ->(Con (his, Con (Instance (append curr1 head), Kleene (Con (tail, Instance head)))), None)
              (*左边有pause, his.curr.(tail.new_curr)^* *)
            | (true, false) ->(Con (his, Con (Instance curr1, Kleene (Con (tail, Instance new_curr1)))), None)
              (*两边都没有pause, his.(curr+head).(tail开头加上结尾的signals)^* *)
            | (false, false) ->(Con (his, Con (Instance (append curr1 head), Kleene (addToHead new_curr1 new_his))), None)
            ) head_tail_list
          ) newState_list
        )
        
        
      
      )
      
      
      current
      )



  | Present (s, p1, p2) -> 
  
    let eff1 = forward evn (List.map (fun (his, cur)-> 
    match cur with 
      None -> (his, None)
    | Some cur ->
    (his, Some (List.append [(One s)] cur )) ) current) p1 original full in 
    let eff2 = forward evn (List.map (fun (his, cur)-> 
    match cur with 
      None -> (his, None)
    | Some cur ->
    (his, Some (List.append [(Zero s)] cur )) ) current) p2 original full in 
    
    (*
    print_string(string_of_es (normalES (state_To_es eff1)));
    print_string ("\n");
    print_string(string_of_es (normalES (state_To_es eff2)));
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
      (print_string ("[T.r.s: Verification when calling "^mn ^"]\n" ^ 
      printReport (normalES (state_To_es current) ) pre_callee));
      
      if res == false then raise (Foo ("Error when calling "^mn^"\n"))
      else 
      List.flatten (List.map (fun (his, curr) -> 
      match curr with 
        None -> [(his, curr)]
      | Some curr -> es_To_state (Con (his, (addToHead curr post_callee)))) current)

    

  | Trap _ -> raise (Foo "not there forward")
  | Exit _ -> raise (Foo "not there forward")
  | Par _  -> raise (Foo "not there forward")
  | _ -> raise (Foo "not there forward")
  ;;

let verifier (spec_prog:spec_prog) (full: spec_prog list):string = 
  let (nm, inp_sig, oup_sig, pre,  post, prog) = spec_prog in 
  (*print_string (string_of_prg_state (es_To_state pre));*)
  let final_states = forward ((*append inp_sig*) oup_sig) (es_To_state pre) prog prog full in 
  let final_effects =  normalES (state_To_es final_states)  in 
  "\n========== Module: "^ nm ^" ==========\n" ^
  "[Pre  Condition] " ^ string_of_es pre ^"\n"^
  "[Post Condition] " ^ string_of_es post ^"\n"^
  "[Final  Effects] " ^ string_of_es final_effects ^"\n\n"^
  (*(string_of_inclusion final_effects post) ^ "\n" ^*)
  "[T.r.s: Verification for Post Condition]\n" ^ 
  printReport final_effects post
  
  ;;

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
