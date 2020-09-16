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
  | Emp -> [(Emp, None, None)]
  | Instance ins -> [(Emp, Some ins, None)]
  | Con (es1, es2) -> 
    let his_cur_list = es_To_state es2 in 
    List.map (fun (his,cur,trap) -> (Con (es1, his),cur, trap)) his_cur_list
    
  | Disj (es1, es2) -> List.append (es_To_state es1) (es_To_state es2)
  | Kleene esIn -> 
    let his_cur_list = es_To_state esIn in 
    List.map (fun (his,cur, trap) -> (Con (es, his), cur, trap)) his_cur_list
  | Ntimed (esIn, n) ->
    assert (n>1);
    let his_cur_list = es_To_state esIn in 
    List.map (fun (his,cur, trap) -> (Con (Ntimed (esIn, n-1), his), cur, trap)) his_cur_list

  | _ -> raise (Foo "there is a EMP OR BOT HERE")
  ;;


let rec state_To_es (state:prog_states):es = 
  List.fold_left (fun acc (a, b, trap) -> 
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
    List.map (fun (his, curr, trap) -> 
    (his,  curr, trap )) current
  | Emit s -> 
    List.map (fun (his, curr, trap) -> 
      (match trap with 
      | Some name  -> (his, curr, trap)
      | None -> 
          (match curr with 
            None -> raise (Foo "Emit doesn't work...")
          | Some curr -> (his, Some (List.append [(One s)] curr), trap )
          )
      )) current
  | Pause -> 
    let helper (his, curr, trap) = 
      match trap with
      | Some name -> (his, curr, trap)
      | None -> 
      let newCurr = Some [] in 
      (match curr with 
        None -> (his, newCurr, trap)
      | Some curr -> let newHis = Con (his, Instance curr) in 
      (newHis, newCurr, trap)
      )
    in List.map (helper) current
  | Seq (p1, p2) ->  
    List.flatten (
      List.map (fun (his, cur, trap) ->
    match trap with 
      Some _ ->[(his, cur, trap)]
    | None -> let states1 = forward evn current p1 original full in 
              List.flatten (List.map (fun (his1, cur1, trap1)->
              match trap1 with 
                Some _ -> [(his1, cur1, trap1)]
              | None -> forward evn [(his1, cur1, trap1)] p2 original full

              )states1)
    
    ) current 
    )
    
    
  | Declear (s, progIn ) -> 
    forward (List.append evn [s]) ( current) progIn original full

  | Loop prog ->
     (*forward evn current prog original full 
     *)
     List.flatten (List.map (fun (his, curr, trap) -> 
      match trap with 
      | Some name  -> [(his, curr, trap)]
      | None ->
      match curr with 
        None -> raise (Foo "something wrong before entering loop")
      | Some curr1 ->
        
       (* by cases *)
        let newState_list = forward evn [(Emp, Some [], trap )] prog original full in
        List.flatten (
          List.map (fun (new_his, new_curr, new_trap) ->
          match new_trap with 
          | Some name -> [(Con (his, addToHead curr1 new_his), new_curr, new_trap)]
          | None -> 
          let new_his = normalES new_his in 
          match new_curr with 
            None -> raise (Foo "something wrong inside loop")
          | Some new_curr1 -> 
            let head_tail_list = split_es_head_tail (normalES new_his) in 
            List.map (fun (head, tail) ->
            match (isEmp (head), isEmp new_curr1) with
              (*两头都有pause, his.curr.(tail.head)^* *)
              (true, true) -> (Con (his, Con (Instance curr1, Kleene (Con (tail, Instance head)))), None, None)
              (*右边有pause, his.(curr+head).(tail.head)^* *)
            | (false, true) ->(Con (his, Con (Instance (append curr1 head), Kleene (Con (tail, Instance head)))), None, None)
              (*左边有pause, his.curr.(tail.new_curr)^* *)
            | (true, false) ->(Con (his, Con (Instance curr1, Kleene (Con (tail, Instance new_curr1)))), None, None)
              (*两边都没有pause, his.(curr+head).(tail开头加上结尾的signals)^* *)
            | (false, false) ->(Con (his, Con (Instance (append curr1 head), Kleene (addToHead new_curr1 new_his))), None, None)
            ) head_tail_list
          ) newState_list
        )
        
        
      
      )
      
      
      current
      )



  | Present (s, p1, p2) -> 
    List.flatten (List.map (fun (his, curr, trap) -> 
      (match trap with 
      | Some name  -> [(his, curr, trap)]
      | None -> 
          match curr with 
          | None -> [(his, None, trap)]
          | Some cur -> 
            (
            let eff1 = forward evn [(his, Some (List.append [(One s)] cur ), trap)] p1 original full in 
            let eff2 = forward evn [(his, Some (List.append [(Zero s)] cur ), trap)] p2 original full in 
            List.append eff1 eff2
            )
      )
    ) current)
    
  
    
        (*
      print_string(string_of_es (normalES (state_To_es eff1)));
      print_string ("\n");
      print_string(string_of_es (normalES (state_To_es eff2)));
      *)
  | Run mn -> 
      List.flatten (List.map (
        fun (his, cur, trap) ->
          match trap with
            Some name -> [(his, cur, trap)]
          | None -> 
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
          List.flatten (List.map (fun (his, curr, trap) -> 
          match curr with 
            None -> [(his, curr, trap)]
          | Some curr -> es_To_state (Con (his, (addToHead curr post_callee)))) current)
  
      ) current )

      

  | Trap (mn, prog) -> 
      List.flatten (List.map (fun (his, cur, trap)-> 
      match trap with 
        Some _ -> [(his, cur, trap)]
      | None -> 
          let eff = forward evn [(his, cur, trap)] prog original full in 
          List.map (fun (hisIn, curIn, trapIn)->
          match trapIn with 
            Some name -> if String.compare mn name == 0 then (hisIn, curIn, None)
                         else (hisIn, curIn, trapIn)
          | None -> (hisIn, curIn, trapIn)
          )
          eff
      )current)
  | Exit name -> 
      List.map (fun (his, cur, trap)-> 
      match trap with 
        Some _ -> (his, cur, trap)
      | None -> (his, cur, Some name)
      )current
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
