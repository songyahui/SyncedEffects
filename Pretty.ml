(*----------------------------------------------------
----------------------PRINTING------------------------
----------------------------------------------------*)

open String
open List
open Ast
open Printf
open Int32


exception Foo of string


(*used to generate the free veriables, for subsititution*)
let freeVar = ["t1"; "t2"; "t3"; "t4";"t5";"t6";"t7";"t8";"t9";"t10"
              ;"t11"; "t12"; "t13"; "t14";"t15";"t16";"t17";"t18";"t19";"t20"
              ;"t21"; "t22"; "t23"; "t24";"t25";"t26";"t27";"t28";"t29";"t30"];;



let rec getAfreeVar (varList:string list):string  =
  let rec findOne li = 
    match li with 
        [] -> raise ( Foo "freeVar list too small exception!")
      | x :: xs -> if (exists (fun a -> String.compare a x == 0) varList) == true then findOne xs else x
  in
  findOne freeVar
;;




let rec iter f = function
  | [] -> ()
  | [x] ->
      f true x
  | x :: tl ->
      f false x;
      iter f tl

let to_buffer ?(line_prefix = "") ~get_name ~get_children buf x =
  let rec print_root indent x =
    bprintf buf "%s\n" (get_name x);
    let children = get_children x in
    iter (print_child indent) children
  and print_child indent is_last x =
    let line =
      if is_last then
        "└── "
      else
        "├── "
    in
    bprintf buf "%s%s" indent line;
    let extra_indent =
      if is_last then
        "    "
      else
        "│   "
    in
    print_root (indent ^ extra_indent) x
  in
  Buffer.add_string buf line_prefix;
  print_root line_prefix x

let printTree ?line_prefix ~get_name ~get_children x =
  let buf = Buffer.create 1000 in
  to_buffer ?line_prefix ~get_name ~get_children buf x;
  Buffer.contents buf

type binary_tree =
  | Node of string * (binary_tree  list )
  | Leaf

let get_name = function
    | Leaf -> "."
    | Node (name, li) -> name;;

let get_children = function
    | Leaf -> []
    | Node (_, li) -> List.filter ((<>) Leaf) li;;

let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"

  ;;

let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"
;;

let rec string_of_prog (p : prog) : string =
  match p with
    Nothing -> "nothing"
  | Pause -> "pause"
  | Seq (p1, p2) ->  string_of_prog p1 ^ ";\n" ^ string_of_prog p2 
  | Par (p1, p2) ->  "(" ^ string_of_prog p1 ^ ")\n||\n (" ^ string_of_prog p2 ^" )"
  | Loop pIn -> "loop\n " ^ string_of_prog pIn ^ "\nend loop"
  | Declear (s, prog) -> "signal " ^ s ^ " in \n" ^ string_of_prog prog ^ "\nend signal"
  | Emit s -> "emit " ^ s 
  | Present (s, p1, p2) -> "present " ^ s ^ "\nthen " ^ string_of_prog p1 ^"\nelse " ^ string_of_prog p2 ^"\nend present"
  | Trap (mn, prog) -> "trap "  ^ mn ^" in\n" ^ string_of_prog prog ^" )"^ "\nend trap"
  | Exit  mn -> "exit " ^ mn 
  | Run mn -> "run " ^ mn
  | Suspend (prog, s) -> "abort \n" ^ string_of_prog prog ^ "\nwhen "^s
  ;;

let rec showLTL (ltl:ltl):string =
  match ltl with 
    Lable str -> str
  | Next l -> "(" ^"X" ^showLTL l ^")"
  | Until (l1, l2) -> "(" ^showLTL l1 ^ " U " ^showLTL l2 ^")"
  | Global l -> "(" ^"[] " ^showLTL l ^")"
  | Future l -> "(" ^"<> " ^showLTL l ^")"
  | NotLTL l -> "(" ^"! " ^showLTL l ^")"
  | Imply (l1, l2) -> "(" ^showLTL l1 ^ " -> " ^showLTL l2 ^")"
  | AndLTL (l1, l2) -> "(" ^showLTL l1 ^ " && " ^showLTL l2 ^")"
  | OrLTL (l1, l2) -> "(" ^showLTL l1 ^ " || " ^showLTL l2 ^")"
  ;;

let string_of_state (state :signal):string = 
  match state with 
    One name -> name ^","
  | Zero name -> "" (*"!"^name*);; 


let string_of_sl (sl):string = 
  List.fold_left (fun acc sig_ -> 
  acc ^ "" ^ 
  string_of_state sig_
  ) "" sl
;;

let string_of_instance (mapping:instance) :string = 
  let temp1 = "{" ^ string_of_sl mapping ^ "}" in 
  temp1
  ;;



let rec string_of_es (es:es) :string = 
  match es with 
    Bot -> "_|_"  
  | Emp -> "emp"
  | Instance ins  -> string_of_instance ins
  | Con (es1, es2) ->  "("^string_of_es es1 ^ " . " ^ string_of_es es2^")"
  | Kleene esIn -> "(" ^ string_of_es esIn ^ ")*" 
  | Omega esIn -> "(" ^ string_of_es esIn ^ ")w" 
  | Ntimed (esIn, n) ->"(" ^ string_of_es esIn ^ ")" ^ string_of_int n 
  | Disj (es1, es2) -> string_of_es es1 ^ " \\/ " ^ string_of_es es2
  ;;

let string_of_p_instance ((a, b):p_instance) :string = 
  let temp1 = "{" ^ string_of_sl a ^ " /\\ " in 
  let temp2 = "" ^ string_of_sl b ^ "}" in 
  temp1 ^ temp2
  ;;

let rec string_of_p_es (es:p_es) :string = 
  match es with 
    PBot -> "_|_"  
  | PEmp -> "emp"
  | PInstance ins  -> string_of_p_instance ins
  | PCon (es1, es2) ->  "("^string_of_p_es es1 ^ " . " ^ string_of_p_es es2^")"
  | PKleene esIn -> "(" ^ string_of_p_es esIn ^ ")*" 
  | POmega esIn -> "(" ^ string_of_p_es esIn ^ ")w" 
  | PNtimed (esIn, n) ->"(" ^ string_of_p_es esIn ^ ")" ^ string_of_int n 
  | PDisj (es1, es2) -> string_of_p_es es1 ^ " \\/ " ^ string_of_p_es es2
  ;;

let string_of_spec_prog (inp:spec_prog):string = 
  let  (nm, ins, outs, pre, post, p) = inp in 
  let body = string_of_prog p in 
  let spec = "\n/*@\nrequire " ^ string_of_es pre ^"\nensure " ^ string_of_es post ^"\n@*/\n\n" in 
  
  let inp = "input " ^ (List.fold_left (fun acc a -> acc ^ " " ^ a) "" ins) ^ ";\n" in 
  let outp = "output " ^ (List.fold_left (fun acc a -> acc ^ " " ^ a) "" outs) ^ ";\n" in 
  let whole = "module " ^ nm  ^": \n\n" ^ inp ^ outp ^ spec ^ body ^ "\n\nend module" in 
  whole ;;

let string_of_full_prog (full: spec_prog list):string = 
  List.fold_left (fun acc (p) -> acc ^ "\n\n" ^ string_of_spec_prog p) "" full
;;

let string_of_inclusion (lhs:es) (rhs:es) :string = 
  string_of_es lhs ^" |- " ^string_of_es rhs 
  ;;

let string_of_trace ((his, cur, trap):trace) :string = 
  "Trace: (" ^ string_of_p_es his ^")." ^ 
  (match cur with 
    None -> ""
  | Some cur -> 
  string_of_p_instance cur 
  )
  ^"  "^
  (match trap with 
    None -> ""
  | Some trapname -> 
  "exiting from "^ trapname
  )^"\n"
  ;; 

let string_of_prg_state (t_li : trace list):string = 
  List.fold_left (fun acc a -> acc ^ string_of_trace a ) "\n" t_li ;;


let compareSignal s1 s2 : bool =
  match (s1, s2) with 
    (One n1, One n2) -> String.compare n1 n2 == 0
  | (Zero n1 , Zero n2 ) -> String.compare n1 n2 == 0 
  | _ -> false 
  ;;

let controdict s1 s2 : bool =
  match (s1, s2) with 
    (One n1, Zero n2) -> String.compare n1 n2 == 0
  | (Zero n1 , One n2 ) -> String.compare n1 n2 == 0 
  | _ -> false 
  ;;

let rec oneOfFalse (sig_:signal) ss : bool =
  match ss with 
    [] -> false 
  | head_sig:: xs -> if controdict sig_ head_sig then true else oneOfFalse sig_ xs
;;
(*true return has controdiction, false means no controdiction *)
let rec checkHasFalse ss : bool = 
  match ss with 
  [] -> false 
| x::xs -> if oneOfFalse x xs then true else checkHasFalse xs 
;;

let superSetOf (bigger:instance) (smaller:instance) :bool = 
  let rec helper li cur = 
    match li with 
      [] -> false 
    | x::xs -> if compareSignal x cur then true else helper xs cur
  in List.fold_left (fun acc a -> acc && helper bigger a ) true smaller ;;


let rec compareES es1 es2 : bool = 
  match (es1, es2) with 
  | (Bot, Bot) -> true 
  | (Emp, Emp) -> true 
  | (Instance ins1, Instance ins2) -> superSetOf ins1 ins2 && superSetOf ins2 ins1
  | ( Kleene es1, Kleene es2) -> compareES es1 es2
  | ( Omega es1, Omega es2) -> compareES es1 es2
  | (Con (es1L, es1R), Con (es2L, es2R)) -> 
    if (compareES es1L es2L) == false then false
    else (compareES es1R es2R)
  | (Disj (es1L, es1R), Disj (es2L, es2R)) -> 
      if ((compareES es1L es2L) && (compareES es1R es2R)) then true 
      else ((compareES es1L es2R) && (compareES es1R es2L))
  | _ -> false 
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

  

let rec nullablePes (es:p_es):bool = 
  match es with 
    PBot -> false 
  | PEmp -> true
  | PInstance _  -> false 
  | PCon (es1, es2) -> nullablePes es1 && nullablePes es2
  | PDisj (es1, es2) -> nullablePes es1 || nullablePes es2
  | PKleene _ -> true  
  | POmega _ -> false 
  | PNtimed (_, n) -> n==0 
  ;;

let rec nullable (es:es):bool = 
  match es with 
    Bot -> false 
  | Emp -> true
  | Instance _  -> false 
  | Con (es1, es2) -> nullable es1 && nullable es2
  | Disj (es1, es2) -> nullable es1 || nullable es2
  | Kleene _ -> true  
  | Omega _ -> false 
  | Ntimed (_, n) -> n==0 
  ;;



let rec normalPES es: p_es =
  match es with 
  
  | PCon (es1, es2) -> 
      let norES1 = normalPES es1 in 
      let norES2 = normalPES es2 in 
      (*print_string (string_of_es norES1);*)
      (match (norES1, norES2) with 
        (PEmp, _) -> norES2 
      | (_, PEmp) -> norES1
      | (POmega _, _ ) -> norES1
      | (PCon(es1, es2), es3) -> normalPES (PCon (normalPES es1, normalPES (PCon(es2, es3)) ))
      | (PDisj (or1, or2), es2) -> PDisj(PCon(or1, es2), PCon(or2, es2))
      | (es1, PDisj (or1, or2)) -> PDisj(PCon(es1, or1), PCon(es1, or2))

      | (PBot, _) -> PBot 
      | (_ , PBot) -> PBot 
      
      | _ -> 
      
      PCon (norES1, norES2)
      )
  | PDisj (es1, es2) -> 
      let norES1 = normalPES es1 in 
      let norES2 = normalPES es2 in 
      (match (norES1, norES2) with 
      | (PBot, PBot) -> PBot
      | (PBot, _) -> norES2
      | (_, PBot) -> norES1
      | (PDisj(es1In, es2In), norml_es2 ) ->
        PDisj (PDisj((normalPES es1In), (normalPES es2In)), norml_es2 )
      | (norml_es2, PDisj(es1In, es2In) ) ->
        PDisj (norml_es2, PDisj((normalPES es1In), (normalPES es2In)))
      | _ ->

      PDisj (norES1, norES2)
      )
  | PInstance (ssp, ss) -> 
    let (new_a, new_b) = (deleteRedundent ssp, deleteRedundent ss) in 
    if checkHasFalse (append new_a new_b) then  PBot else 
    (PInstance (new_a, new_b))
  | PKleene esIn -> PKleene (normalPES esIn)
  | POmega esIn -> POmega (normalPES esIn)

  | PNtimed (esIn, n) -> if n==0 then PEmp else PNtimed (normalPES esIn, n) 
  | _ -> es 
  ;;

let rec isNotDisjTrace (p_Es:p_es) : bool =
  match p_Es with 
    PBot -> true  
  | PEmp -> true 
  | PInstance _ -> true  
  | PCon (es1, es2) -> isNotDisjTrace es1 || isNotDisjTrace es2
  | PDisj _ -> false
  | PKleene (es1) ->isNotDisjTrace es1 
  | POmega (es1) ->isNotDisjTrace es1 
  | PNtimed (es1, n) ->isNotDisjTrace es1 
  ;;

let rec isNotBot  (p_Es:p_es) : bool =
  match p_Es with
  PBot -> false 
| _ -> true 
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


let rec logical_correctness inp_sig es: bool =
  let p_es = normalPES es in 
  match inp_sig with
    [] -> isNotDisjTrace p_es && isNotBot p_es
  | x::xs -> 
    let temp1 = logical_correctness xs (addToHead ([], [(One x)]) es) in 
    let temp2 = logical_correctness xs (addToHead ([], [(Zero x)]) es) in 
    temp1 && temp2
    
;;

  (*let helper 
  match p_es with 
    PBot -> PBot 
  | PEmp -> PEmp
  | PInstance (path, ins)  ->  
  let (new_a, new_b) = (deleteRedundent path, deleteRedundent ins) in 
  if checkHasFalse (append new_a new_b) then  PBot else 
  (PInstance (new_a, append new_a new_b))
  | PCon (es1, es2) -> PCon (logical_correctness es1, logical_correctness es2)
  | PDisj (es1, es2) -> PDisj (logical_correctness es1, logical_correctness es2) 
  | PKleene (es1 )-> PKleene (logical_correctness es1 )  
  | POmega es1 -> POmega (logical_correctness es1) 
  | PNtimed (es1, n) -> PNtimed (logical_correctness es1, n)
  *)
  ;; 
 
let rec normalES es: es =
  match es with 
  
  | Con (es1, es2) -> 
      let norES1 = normalES es1 in 
      let norES2 = normalES es2 in 
      (*print_string (string_of_es norES1);*)
      (match (norES1, norES2) with 
        (Emp, _) -> norES2 
      | (_, Emp) -> norES1
      | (Omega _, _ ) -> norES1
      | (Kleene (esIn1), Kleene (esIn2)) -> 
          if compareES esIn1 esIn2 == true then norES2
          else Con (norES1, norES2)
      | (Kleene (esIn1), Con (Kleene (esIn2), es2)) -> 
          if compareES esIn1 esIn2 == true then norES2
          else Con (norES1, norES2) 
      | (Con(es1, es2), es3) -> normalES (Con (normalES es1, normalES (Con(es2, es3)) ))
      | (Disj (or1, or2), es2) -> Disj(Con(or1, es2), Con(or2, es2))
      | (es1, Disj (or1, or2)) -> Disj(Con(es1, or1), Con(es1, or2))

      | (Bot, _) -> Bot 
      | (_ , Bot) -> Bot 
      
      | _ -> 
      
      Con (norES1, norES2)
      )
  | Disj (es1, es2) -> 
      let norES1 = normalES es1 in 
      let norES2 = normalES es2 in 
      (match (norES1, norES2) with 
      | (Bot, Bot) -> Bot
      | (Bot, _) -> norES2
      | (_, Bot) -> norES1
      | (_, Emp) -> if nullable norES1 then norES1 else Disj (norES1, norES2)
      | (Emp, _) -> if nullable norES2 then norES2 else Disj (norES1, norES2)
      | (Disj(es1In, es2In), norml_es2 ) ->
        if compareES norml_es2 (normalES es1In) || compareES norml_es2 (normalES es2In) then Disj((normalES es1In), (normalES es2In))
        else Disj (Disj((normalES es1In), (normalES es2In)), norml_es2 )
      | (norml_es2, Disj(es1In, es2In) ) ->
        if compareES norml_es2 (normalES es1In) || compareES norml_es2 (normalES es2In) then Disj((normalES es1In), (normalES es2In))
        else Disj (norml_es2, Disj((normalES es1In), (normalES es2In)))
      | _ ->
      if compareES norES1 norES2 then norES1
      else 
      Disj (norES1, norES2)
      )
  | Instance ss -> 
    let ss1 = deleteRedundent ss in 
    if checkHasFalse (ss1) then  Bot else 
    (Instance ss1)
  | Kleene esIn -> Kleene (normalES esIn)
  | Omega esIn -> Omega (normalES esIn)

  | Ntimed (esIn, n) -> if n==0 then Emp else Ntimed (normalES esIn, n) 
  | _ -> es 
  ;;


let rec getFstPes (es:p_es) :p_instance list= 
  match es with 
    PBot -> []
  | PEmp -> []
  | PInstance ins  -> [ins] 
  | PCon (es1, es2) -> if nullablePes es1 then append (getFstPes es1) (getFstPes es2) else getFstPes es1
  | PDisj (es1, es2) -> append (getFstPes es1) (getFstPes es2)
  | PKleene esIn -> (getFstPes esIn) 
  | POmega esIn -> (getFstPes esIn) 
  | PNtimed (esIn, n) -> (getFstPes esIn) 
  ;;

let rec getFst (es:es) :instance list= 
  match es with 
    Bot -> []
  | Emp -> []
  | Instance ins  -> [ins] 
  | Con (es1, es2) -> if nullable es1 then append (getFst es1) (getFst es2) else getFst es1
  | Disj (es1, es2) -> append (getFst es1) (getFst es2)
  | Kleene esIn -> (getFst esIn) 
  | Omega esIn -> (getFst esIn) 
  | Ntimed (esIn, n) -> (getFst esIn) 
  ;;

let isBot (es:es):bool = 
  match es with 
    Bot -> true 
    |_ -> false 
    ;; 
  



let rec superESOf (bigger:es) (smaller:es) : bool = 
  match (bigger, smaller) with 
  | (Instance ins1, Instance ins2) -> superSetOf ins1 ins2
  | (Con (es1, es2), Con(es3, es4)) -> superESOf es1 es3 && superESOf es2 es4
  | (Disj (es1, es2), Disj(es3, es4))-> (superESOf es1 es3 && superESOf es2 es4) || (superESOf es1 es4 && superESOf es2 es3)
  | (Kleene es1, Kleene es2) -> superESOf es1 es2
  | (Omega es1, Omega es2) -> superESOf es1 es2

  | (Ntimed (es1, n1), Ntimed(es2, n2)) -> superESOf es1 es2 && n1 == n2
  | (Disj (es1, es2), Con _)-> (superESOf es1 smaller ) || (superESOf es2 smaller)
  | _ -> false 
  ;; 

  
let rec derivativePes (ins_given: p_instance) (es:p_es) : p_es = 
  let (a, b) = ins_given in 
  match es with 
    PBot -> PBot
  | PEmp -> PBot
  | PInstance (aa, bb)  -> if superSetOf b bb then PEmp else PBot
  | PCon (es1, es2) -> 
    let temp = PCon (derivativePes ins_given es1, es2) in 
    if nullablePes es1 then PDisj (temp, derivativePes ins_given es2)
    else temp
    
  | PDisj (es1, es2) -> PDisj (derivativePes ins_given es1, derivativePes ins_given es2)
  | PKleene esIn -> PCon (derivativePes ins_given esIn, es)
  | PNtimed (esIn, n) -> PCon (derivativePes ins_given esIn, PNtimed (esIn, n-1))
  | POmega esIn -> PCon (derivativePes ins_given esIn, es)

  ;;

let rec derivative (ins_given: instance) (es:es) : es = 
  match es with 
    Bot -> Bot
  | Emp -> Bot
  | Instance ins  -> if superSetOf ins_given ins then Emp else Bot
  | Con (es1, es2) -> 
    let temp = Con (derivative ins_given es1, es2) in 
    if nullable es1 then Disj (temp, derivative ins_given es2)
    else temp
    
  | Disj (es1, es2) -> Disj (derivative ins_given es1, derivative ins_given es2)
  | Kleene esIn -> Con (derivative ins_given esIn, es)
  | Ntimed (esIn, n) -> Con (derivative ins_given esIn, Ntimed (esIn, n-1))
  | Omega esIn -> Con (derivative ins_given esIn, es)

  ;;


let rec reoccur (evn: inclusion list) (lhs:es) (rhs:es) :bool = 
    match evn with
      [] -> false 
    | (lhs', rhs')::xs -> 
      if superESOf rhs' rhs && superESOf lhs lhs' 
      then true 
      else reoccur xs lhs rhs
;;

let rec esToPes (es:es):p_es =
  match es with 
    Bot -> PBot
  | Emp -> PEmp
  | Instance ins -> PInstance ([], ins)
  | Con (es1, es2) -> PCon (esToPes es1, esToPes es2)
  | Disj (es1, es2) ->PDisj (esToPes es1, esToPes es2) 
  | Kleene es1 -> PKleene (esToPes es1)
  | Omega es1 -> POmega (esToPes es1)
  | Ntimed (es1, n) -> PNtimed (esToPes es1, n)
  ;;

let rec pesToEs (p_es:p_es): es=
  match p_es with 
    PBot -> Bot
  | PEmp -> Emp
  | PInstance (_, ins) -> Instance ins
  | PCon (es1, es2) -> Con (pesToEs es1, pesToEs es2)
  | PDisj (es1, es2) -> Disj (pesToEs es1, pesToEs es2) 
  | PKleene es1 -> Kleene (pesToEs es1)
  | POmega es1 -> Omega (pesToEs es1)
  | PNtimed (es1, n) -> Ntimed (pesToEs es1, n)
  ;;

