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

  

let rec p_es_To_state (es:p_es) :prog_states = 
  match es with 
  | PEmp -> [(PEmp, None, None)]
  | PInstance ins -> [(PEmp, Some ins, None)]
  | PCon (es1, es2) -> 
    let his_cur_list = p_es_To_state es2 in 
    List.map (fun (his,cur,trap) -> (PCon (es1, his),cur, trap)) his_cur_list
    
  | PDisj (es1, es2) -> List.append (p_es_To_state es1) (p_es_To_state es2)
  | PKleene esIn -> 
    let his_cur_list = p_es_To_state esIn in 
    List.map (fun (his,cur, trap) -> (PCon (es, his), cur, trap)) his_cur_list
  | PNtimed (esIn, n) ->
    assert (n>1);
    let his_cur_list = p_es_To_state esIn in 
    List.map (fun (his,cur, trap) -> (PCon (PNtimed (esIn, n-1), his), cur, trap)) his_cur_list

  | _ -> raise (Foo "there is a EMP OR BOT HERE")
  ;;


let rec state_To_p_es (state:prog_states):p_es = 
  normalPES (
  List.fold_left (fun acc (a, b, trap) -> 
  match b with 
    None -> PDisj (acc, a)
  | Some b -> 
  PDisj (acc, (PCon (a, PInstance b)))) PBot state
  )
  ;;

let appendSL ((a, b):p_instance) ((aa, bb):p_instance) :p_instance = 
  (List.append a aa,  List.append b bb);;
  
let rec addToHead (ins: p_instance) (es:p_es) :p_es = 
  match es with
  | PInstance ins1 ->  PInstance (appendSL ins ins1)
  | PCon (es1, es2) -> PCon (addToHead ins es1, es2) 
  | PDisj (es1, es2) -> PDisj (addToHead  ins es1, addToHead ins es2)
  | PKleene esIn -> PCon (addToHead ins esIn, es)
  | PNtimed (esIn, n) -> PCon (addToHead ins esIn, PNtimed (esIn, n-1))
  | _ -> es 
  ;;

let make_nothing (evn: string list) : signal list = 
  List.map (fun a -> (Zero a) ) evn 
  ;;

let rec zip a b =
  match (a,b) with
    ([],[]) -> []
    | ([],n::ns)-> []
    | (n::ns,[]) -> []
    | (k::ks, h::hs) -> (k,h)::zip ks hs ;;


let rec split_p_es_head_tail (es:p_es) :(p_instance * p_es) list = 
  match es with 
  | PInstance ins -> [(ins, PEmp)]
  | PCon (es1, es2) -> 
    let head_tail_list = split_p_es_head_tail es1 in 
    List.map (fun (head,tail) -> (head, PCon (tail, es2))) head_tail_list
    
  | PDisj (es1, es2) -> List.append (split_p_es_head_tail es1) (split_p_es_head_tail es2)
  | PKleene esIn -> 
    let head_tail_list = split_p_es_head_tail esIn in 
    List.map (fun (head,tail) -> (head, PCon (tail, es))) head_tail_list
  | PNtimed (esIn, n) ->
    assert (n>1);
    let head_tail_list = split_p_es_head_tail esIn in 
    List.map (fun (head,tail) -> (head, PCon (tail, PNtimed (esIn, n-1)))) head_tail_list

  | _ -> raise (Foo "there is a EMP OR BOT HERE in split_p_es_head_tail")
  ;;

let isEmp xs : bool = 
  match xs with 
    [] -> true 
  | _ -> false 
;;

let rec paralleEffLong es1 es2 : p_es = 
  let norES1 = normalPES es1 in 
  let norES2 = normalPES es2 in 
  let fst1 = getFstPes norES1 in
  let fst2 = getFstPes norES2 in 
  let headcom = zip fst1 fst2 in 

  let listPES =  List.map (fun (f1, f2) -> 
  let der1 = derivativePes f1 norES1 in 
  let der2 = derivativePes f2 norES2 in 
  match (der1, der2) with 
    (PEmp, _) -> der2
  | (_, PEmp) -> der1
  | _ -> PCon (PInstance (appendSL f1 f2), paralleEffLong der1 der2)) headcom
  in
  normalPES (
  List.fold_left (fun acc a -> PDisj (acc, a)) PBot listPES
  )

   ;;

let rec paralleEffShort es1 es2 : p_es = 
  let norES1 = normalPES es1 in 
  let norES2 = normalPES es2 in 
  let fst1 = getFstPes norES1 in
  let fst2 = getFstPes norES2 in 
  let headcom = zip fst1 fst2 in 


  let listES =  List.map (
  fun (f1, f2) -> 
    let der1 = normalPES (derivativePes f1 norES1) in 
    let der2 = normalPES (derivativePes f2 norES2) in 


    (match (der1, der2) with 
    | (PEmp, _) -> PInstance (appendSL f1 f2)
    | (_, PEmp) -> PInstance (appendSL f1 f2)
    | (der1, der2) -> 
      PCon (PInstance (appendSL f1 f2), paralleEffShort der1 der2))
  ) headcom
  
  in
  normalPES (
  List.fold_left (fun acc a -> PDisj (acc, a)) PBot listES
  )
 ;;

let rec lengthPES es : int =
  match es with  
| PEmp -> 0
| PInstance _ -> 1 
| PCon (es1, es2) -> lengthPES es1 + lengthPES es2

| PNtimed (es1, n) -> (lengthPES es1) * n
| _ -> raise (Foo "getlength error ")
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
          | Some (path, curr) -> (his, Some (path, (List.append [(One s)] curr)), trap )
          )
      )) current
  | Pause -> 
    let helper (his, curr, trap) = 
      match trap with
      | Some name -> (his, curr, trap)
      | None -> 
      let newCurr = Some ([], []) in 
      (match curr with 
        None -> (his, newCurr, trap)
      | Some (path, curr) -> let newHis = PCon (his, PInstance (path, curr)) in 
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
     List.flatten (List.map (fun ((his:p_es), curr, trap) -> 
      match trap with 
      | Some name  -> [(his, curr, trap)]
      | None ->
      match curr with 
        None -> raise (Foo "something wrong before entering loop")
      | Some curr1 ->
        
       (* by cases *)
        let newState_list = forward evn [(PEmp, Some ([], []), trap )] prog original full in
        List.flatten (
          List.map (fun (new_his, new_curr, new_trap) ->
          match new_trap with 
          | Some name -> [(PCon (his, addToHead curr1 new_his), new_curr, new_trap)]
          | None -> 
          let new_his = normalPES new_his in 
          match new_curr with 
            None -> raise (Foo "something wrong inside loop")
          | Some (new_p, new_curr1) -> 
            let head_tail_list = split_p_es_head_tail (normalPES new_his) in 
            List.map (fun (((p, head):p_instance), (tail:p_es)) ->
            match (isEmp (head), isEmp new_curr1) with
              (*两头都有pause, his.curr.(tail.head)^* *)
              (true, true) -> (PCon (his, PCon (PInstance curr1, PKleene (PCon (tail, PInstance (p, head))))), None, None)
              (*右边有pause, his.(curr+head).(tail.head)^* *)
            | (false, true) ->(PCon (his, PCon (PInstance (appendSL curr1 (p, head)), PKleene (PCon (tail, PInstance (p, head))))), None, None)
              (*左边有pause, his.curr.(tail.new_curr)^* *)
            | (true, false) ->(PCon (his, PCon (PInstance curr1, PKleene (PCon (tail, PInstance (new_p, new_curr1))))), None, None)
              (*两边都没有pause, his.(curr+head).(tail开头加上结尾的signals)^* *)
            | (false, false) ->(PCon (his, PCon (PInstance (appendSL curr1 (p, head)), PKleene (addToHead (new_p, new_curr1) new_his))), None, None)
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
          | Some (path, cur) -> 
            (
            let eff1 = forward evn [(his, Some (List.append [(One s)] path,  cur ), trap)] p1 original full in 
            let eff2 = forward evn [(his, Some (List.append [(Zero s)] path, cur ), trap)] p2 original full in 
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
          let temp = (pesToEs (normalPES (state_To_p_es current) )) in 
          let (res, tree) = check_containment temp  pre_callee in 
          (print_string ("[T.r.s: Verification when calling "^mn ^"]\n" ^ 
          printReport temp pre_callee));
          
          if res == false then raise (Foo ("Error when calling "^mn^"\n"))
          else 
          List.flatten (List.map (fun (his, curr, trap) -> 
          match curr with 
            None -> [(his, curr, trap)]
          | Some curr -> p_es_To_state (PCon (his, (addToHead curr (esToPes post_callee))))) current)
  
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
  | Par (p1, p2)  -> 
      List.flatten (List.map (fun (his, cur, trap)-> 
      match trap with 
        Some _ -> [(his, cur, trap)]
      | None -> 
          let eff1 = forward evn [(his, cur, trap)] p1 original full in 
          let eff2 = forward evn [(his, cur, trap)] p2 original full in 
          let combinations = zip eff1 eff2 in           

          List.flatten (List.map (fun (trace1 , trace2) -> 
          let (his1, cur1, trap1) = trace1 in 
          let (his2, cur2, trap2) = trace2 in 
          match (trap1, trap2) with 
            (None, None) -> let (combine:p_es) = paralleEffLong  (state_To_p_es [trace1]) (state_To_p_es [trace2])  in 
            p_es_To_state combine
          | (Some t1, None) -> let (combine:p_es) = paralleEffShort  (state_To_p_es [trace1]) (state_To_p_es [trace2]) in
                               List.map (fun (a, b, c) -> (a, b, Some t1)) (p_es_To_state combine)
          | (None, Some t2) -> let (combine:p_es) = paralleEffShort  (state_To_p_es [trace1]) (state_To_p_es [trace2]) in
                               List.map (fun (a, b, c) -> (a, b, Some t2)) (p_es_To_state combine)
          | (Some t1, Some t2) -> let (combine:p_es) = paralleEffShort  (state_To_p_es [trace1]) (state_To_p_es [trace2]) in
              let lengthhis1 = lengthPES his1  in
              let lengthhis2 = lengthPES his2  in
              if lengthhis1 >  lengthhis2 then List.map (fun (a, b, c) -> (a, b, Some t1)) (p_es_To_state combine)
              else if lengthhis1 < lengthhis2 then List.map (fun (a, b, c) -> (a, b, Some t2)) (p_es_To_state combine)
              else List.map (fun (a, b, c) -> (a, b, Some t1)) (p_es_To_state combine)
          ) combinations)
      )current)
  | _ -> raise (Foo "not there forward")
  ;;

let verifier (spec_prog:spec_prog) (full: spec_prog list):string = 
  let (nm, inp_sig, oup_sig, pre,  post, prog) = spec_prog in 
  (*print_string (string_of_prg_state (es_To_state pre));*)
  let final_states = forward ((*append inp_sig*) oup_sig) (p_es_To_state (esToPes pre)) prog prog full in 
  let final_effects =  pesToEs (normalPES (state_To_p_es final_states))  in 
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
