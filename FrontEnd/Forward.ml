open String
open List
open Ast
open Printf
open Parser
open Lexer
open Pretty
open Rewriting
open Sys


let rec append_history_now (history:es) ((cons, now) : instance) :es = 
  match history with 
    Bot -> Bot
  | Emp -> Instance (cons, now) 
  | Instance _  ->  Con(history, Instance (cons, now))
  | Con (es1, es2) -> Con (es1, append_history_now es2 (cons, now))
  | Omega esIn -> Con (history , Instance (cons, now))
  | Any -> Con (Any, Instance (cons, now))
  | Kleene esIn -> Con (history , Instance (cons, now))
  | Ntimed (esIn, n) -> Con (history , Instance (cons, now))
  | Not esIn -> Con (history , Instance (cons, now))
;;

let compareState s1 s2 : bool =
  match (s1, s2) with 
    (One, One) -> true 
  | (Zero, Zero) -> true 
  | _ -> false 
  ;;

let union (assign : mapping list) :mapping list = 
  let rec oneOfOne all1 v :bool =
    match all1 with 
      [] -> false 
    | x::xs-> String.compare x v == 0
  in 
  let allOne = List.map (fun (a, b) -> a) (List.filter (fun (v, s) -> compareState s One) assign) in
  (*print_string ((List.fold_left (fun acc a -> acc ^"," ^ a) "" allOne)^"\n");*)
  let allZero = List.map (fun (a, b) -> a) (List.filter (fun (v, s) -> compareState s Zero) assign) in
  (*print_string ((List.fold_left (fun acc a -> acc ^"," ^ a) "" allZero)^"\n");*)
  List.fold_left (fun acc a -> if oneOfOne allOne a then List.append acc [(a,  One)] else List.append acc [(a,  Zero)]) [] allZero

  ;;




let rec oneOfFalse (var, state) ss : bool =
  match ss with 
    [] -> false 
  | (var1, state1):: xs -> if String.compare var var1 ==0 && compareState state1 state == false then true else oneOfFalse (var, state) xs
;;
(*true return has controdiction, false means no controdiction *)
let rec checkHasFalse ss : bool = 
  match ss with 
  [] -> false 
| x::xs -> if oneOfFalse x xs then true else checkHasFalse xs 
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

let rec unionTwoList (sl1) (sl2) : mapping list = 
  let app = deleteRedundent (List.append sl1 sl2) in 
  let rec helper acc sl : mapping list =  
    match sl with
      [] -> acc 
    | (nm, sta)::xs -> if oneOfFalse (nm, sta) app then helper (List.append acc [(nm, One)]) xs else helper (List.append acc [(nm, sta)]) xs
  in helper [] app
  ;;


let rec append_es_es (es1) (es2) : es = 
  match es1 with
    Bot -> Bot
  | Emp -> es2
  | Instance (con1, ss1)  ->  
        (match es2 with 
          Bot -> Bot 
        | Emp -> es1
        | Instance (con2, ss2) -> Instance (List.append con1 con2, unionTwoList ss1 ss2)
        | Con (es21, es22) -> Con (append_es_es es1 es21, es22)
        | Omega esIn2 -> Con (append_es_es es1 esIn2, es2)
        |_ -> raise (Foo "append_es_es inside")
        )
  | Con (es11, es12) -> Con (es11, append_es_es es12 es2)
  | Omega esIn1 -> Con (es1 , append_es_es esIn1 es2)
  |_ -> raise (Foo "append_es_es outside")


  ;;



let rec checkExit name ss : bool = 
  match ss with 
    [] -> false
  | (str, state)::xs -> if String.compare name str == 0 then true else checkExit name  xs

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
  | Omega esIn -> 
    (es, ([],[]))
  (*let (his, curr) = splitESfromLast esIn in 
    (Con (es, his), curr)
    *)
  | _ -> 
  print_string (string_of_es es^"\n");
  raise (Foo "splitESfromLast _")
  ;;







  
let rec normalES es: es =
  match es with 
    Con (Con(es1, es2), es3) -> normalES (Con (normalES es1, normalES (Con(es2, es3)) ))
  | Con (es1, es2) -> 
      let norES1 = normalES es1 in 
      let norES2 = normalES es2 in 
      (*print_string (string_of_es norES1);*)
      (match (norES1, norES2) with 
        (Emp, _) -> norES2 
      | (_, Emp) -> norES1
      | (Bot, _) -> Bot 
      | (_ , Bot) -> Bot 
      (*
      | (Con (ess, Omega esIn), _) -> Con (ess, Omega esIn)
      | (Omega esIn, _) -> Omega esIn
      *)
      | _ -> Con (norES1, norES2)

      )

  | Instance (con, ss) -> 
    let con1 = deleteRedundent con in 
    let ss1 = deleteRedundent ss in 
    if checkHasFalse (con1) then  Bot else 
    (Instance (con1, ss1))
  | Omega esIn -> Omega (normalES esIn)
  | _ -> es 
  ;;

let normal_post postcondition : postcondition = 
  List.map (fun (a, b, d) -> (normalES a, b, d)) postcondition

  ;;

let string_of_trace (trace :trace) :string = 
  let (his, cur, d) = trace in  
  let temp = normalES (Con(his, Instance cur))in
  string_of_es temp;;

let string_of_postcondition (post:postcondition):string = 
  List.fold_left (fun acc a -> acc  ^ string_of_trace a ^ "\n") "" post
  ;;

let rec length_of_es (es:es) : int = 
  match es with 
    Emp -> 0
  | Instance ins -> 1
  | Con (es1, es2) -> length_of_es es1 + length_of_es es2
  | _ -> raise (Foo "length_of_es")
  ;;

let rec esToList (es:es) : instance list = 
  match es with 
    Instance inI -> [inI]
  | Con (es1, es2) -> List.append (esToList es1) (esToList es2)
  | _ -> raise (Foo "esToList error")
  ;;

let rec listToES (inL:instance list) : es = 
  match inL with 
    [] -> Emp
  | x::xs -> Con (Instance x, listToES xs)
  ;;

let get_max a b :int = 
  if a < b then b else a 
  ;;

let rec zip_es_es (es_1, k1) (es_2, k2) :(es * int) = 

  let listOfES1 = esToList (normalES es_1) in
  let listOfES2 = esToList (normalES es_2) in
  
  let rec helper_zip (acc:instance list) (list1:instance list) (list2:instance list) (len:int): instance list = 
    if len == 0 then  acc
    else 
    match (list1, list2) with 
      (xs, []) -> List.append acc xs 
    | ([], xs) -> List.append acc xs 
    | ((con1, ss1)::xs, (con2, ss2)::ys) -> 
      let curr = (List.append con1 con2, unionTwoList ss1 ss2) in 
      helper_zip (List.append acc [curr]) xs ys (len -1)
  in 
  if get_max k1 k2 != 0 then 
    if k1 > k2 && List.length listOfES1 < List.length listOfES2 then 
      let length = List.length listOfES1 in  
      let ziplist = helper_zip [] (listOfES1) (listOfES2) length in  
      (normalES (listToES ziplist) , k1)
    else if k1 < k2 && List.length listOfES1 > List.length listOfES2 then 
      let length = List.length listOfES2 in  
      let ziplist = helper_zip [] (listOfES1) (listOfES2) length in  
      (normalES (listToES ziplist) , k2)
    else if k1 > k2 && List.length listOfES1 > List.length listOfES2 then 
      let length = List.length listOfES2 in  
      let ziplist = helper_zip [] (listOfES1) (listOfES2) length in  
      (normalES (listToES ziplist) , k2)
    else 
      let length = List.length listOfES1 in  
      let ziplist = helper_zip [] (listOfES1) (listOfES2) length in  
      (normalES (listToES ziplist) , k1)

  else 
  let length = get_max (List.length listOfES1) (List.length listOfES2) in 
  
  let ziplist = helper_zip [] (listOfES1) (listOfES2) length in  
  (normalES (listToES ziplist) , 0)
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
  | Trap (mn, p) -> can_fun s p 
  | Exit _ -> false 
  ;;

let rec getFirst (es:es) : instance =
  match es with 
  | Instance ins  -> ins
  | Con (es1, es2) -> getFirst es1
  | Omega es1 -> getFirst es1
  | _ -> 
  print_string (string_of_es es);
  raise ( Foo "getfirst exc")
  ;;

let rec getLast (es:es) : instance =
  match es with 
  | Instance ins  -> ins
  | Con (es1, es2) -> getLast es2
  | Omega es1 -> getLast es1
  | _ -> raise ( Foo "getLast exc")
  ;;

let rec getTail (es:es) : es =
  match es with 
  | Instance ins -> Emp
  | Con (es1, es2) -> 
    let temp = getTail es1 in
    Con (temp , es2) 
  | Omega es1 -> Con (getTail es1 , es)
  | _ -> raise ( Foo "getTail exc")
  ;;

let rec allDefalut ((con, map):instance) : bool = 
  match map with 
    [] ->  true 
  | (var, state) :: xs  -> if compareState state Zero then  allDefalut (con, xs) else false
  ;;

let rec containExit (con: mapping list) : bool = 
  match con with 
    [] -> false 
  | (var, state)::xs -> 
    if String.length var > 4 then 
      if (String.compare (String.sub var 0 3) "Exit") == 0 then true 
      else containExit xs 
    else containExit xs 

  ;;

let rec es_length (es:es) : int = 
  match es with 
    Bot -> 0
  | Emp -> 0
  | Instance _ -> 1
  | Con (es1, es2) -> es_length es1 + es_length es2
  | Any -> 1
  | Not _ -> 1
  | _ -> raise (Foo "es_length")
  ;;


let rec forward (precondition:precondition) (prog:prog) (toCheck:prog) : postcondition =
  let (evn, (history, curr)) = precondition in 
  match prog with 
    Nothing -> [(normalES history, curr, 0)]
  | Emit s -> 
    let newCurr = setTrue curr s in 
    [(normalES history, newCurr, 0)]
  | Pause -> 
    let newHis = Con (history, Instance curr) in 
    let newCurr = ([], make_nothing evn) in 
    [(normalES newHis, newCurr, 0)]

  | Present (s, p1, p2) -> 
    let eff1 = forward (evn, (history, add_Constain curr (s, One) )) p1 toCheck in 
    let eff2 = forward (evn, (history, add_Constain curr (s, Zero) )) p2 toCheck in 
    if can_fun s toCheck == false then eff2 else 
    List.append eff1 eff2
(*    if can_fun s origin == false then temp2 else 
    Or (temp1, temp2)
*)
  | Seq (p1, p2) ->  
    let eff1 = forward (evn, (history, curr )) p1 toCheck in 
    List.flatten (List.map (fun a -> 
      let (newHis, newCurr, k) = a in 
      if k = 0 then 
      forward (evn, (newHis, newCurr)) p2 toCheck
      else if k >= 2 then eff1
      else 
        let newHis' = Con (newHis, Instance newCurr) in 
        let newCurr' = ([], make_nothing evn) in 
        [(newHis', newCurr', k)]
    
    ) eff1)
  | Par (p1, p2) ->  
    let eff1 = forward (evn, (history, curr )) p1 toCheck in 
    (*print_string (string_of_postcondition eff1^"\n");*)
    let eff2 = forward (evn, (history, curr )) p2 toCheck in 
    (*print_string (string_of_postcondition eff2^"\n");*)
    List.flatten (List.map (fun (his_a, cur_a, k_a) -> 
      List.map (fun (his_b, cur_b, k_b) -> 
        let (temp, kF) = (zip_es_es ( (Con(his_a,  Instance cur_a )), k_a) ((Con (his_b, Instance cur_b )), k_b))in 
        let (a, b) = splitESfromLast temp in 
        (a, b, kF)
        ) eff2) eff1 )

    (*normalES (append_history_now history (List.append now (make_nothing evn)))*)
  | Declear (s, progIn ) -> 
    let (con, ss) = curr in 
    forward ((List.append evn [s]), (history, (con, List.append ss [(s, Zero)]) )) progIn toCheck

  | Exit (mn, d)-> 
    [(normalES history, curr, d+2)]
  
  | Loop pIn -> 
    let eff = normal_post (forward (evn, (Emp, ([], make_nothing evn) )) pIn toCheck )in 
    (*print_string (string_of_postcondition eff^"\n");*)
    List.map (fun (newHis, newCur, k) -> 
      let first = getFirst (normalES newHis) in 
      let last = newCur in 
      let middle = getTail (normalES newHis) in 

      (*print_string ("first" ^ string_of_instance first^"\n");
      print_string ("last" ^ string_of_instance last^"\n");
      print_string ("middle" ^ string_of_es middle^"\n");
      *)
      let temp = (
        if k>=2 then append_es_es (Con (history, Instance curr)) (Con (newHis, Instance newCur)) 
        else 
        (match (allDefalut first, allDefalut last) with 
          (true , true) -> 
          (*print_string ("I am here\n");
          print_string ("middle" ^ (string_of_es middle));
          Con (Con (history, Instance curr), Omega ( middle) )
                    *)
          if es_length newHis == 1 
          then Con (Con (history, Instance curr), Omega (Con (middle, Instance newCur)) )
          else Con (Con (history, Instance curr), Omega ( middle) )

        | (true, false) -> Con (Con (history, Instance curr), Omega (Con (middle, Instance newCur)))
        | (false, true) -> Con (append_es_es (Con (history, Instance curr)) (Instance first), Omega (Con (middle, Instance first)))
        | (false, false) -> 
        let res = normalES(Con (append_es_es (Con (history, Instance curr)) (Instance first), Omega (append_es_es (Con (middle, Instance newCur)) (Instance first))))
        
        in 
        res  
        )
      )
      in 
      let (a, b) = splitESfromLast temp in 
      (normalES a, b, k)
      
    )
    eff

  | Trap (mn, pIn) -> 
    let eff = forward (evn, (Emp, ([], make_nothing evn) )) pIn toCheck in 
    print_string (string_of_postcondition eff^"\n");
    List.map (fun (newHis, newCur, k) -> 

      let first = getFirst (normalES newHis) in 
      let last = newCur in 
      let middle = getTail (normalES newHis) in 

      
      let temp = (
        if k >= 2 then 
        (print_string ("I am here\n");
        append_es_es (Con (history, Instance curr)) (Con (newHis, Instance newCur)) 
        )
        else 
        (match (allDefalut first, allDefalut last) with 
          (true , true) -> Con (Con (history, Instance curr), Omega ( middle) )
        | (true, false) -> Con (Con (history, Instance curr), Omega (Con (Instance last, middle)))
        | (false, true) -> Con (append_es_es (Con (history, Instance curr)) (Instance first), Omega (Con (middle, Instance first)))
        | (false, false) -> 
        Con (append_es_es (Con (history, Instance curr)) (Instance first), Omega (append_es_es middle (Instance first)))
        )
      )
      in       
      let (a, b) = splitESfromLast temp in 
      if k ==2 then (a, b, 0)
      else if k > 2 then (a, b, k - 1)
      else 
      (normalES a, b, k)
      

    )
    eff

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
| Instance (con, ss) -> 
  let con1 = deleteRedundent con in 
  let ss1 = deleteRedundent ss in 
  let temp =   if checkHasFalse (List.append con1 ss1) then  Bot else (Instance (con1, ss1)) in 
  temp

| Omega esIn -> Omega (logical_check esIn)
| _ -> es 
;;

let logical_check_post postcondition : es list = 
  let trmp = List.map (fun (a, b, d) -> logical_check (Con (a, Instance b))) postcondition in  

  List.fold_left (fun acc a -> 
    match a with 
      Bot -> acc
    | _ -> List.append acc [a]) [] trmp
  ;;


let analyse prog1 : string = 
  let (spec, prog) = prog1 in 
  let forward:postcondition = normal_post (fowward_inter prog) in  
  let logical_res :(es list) = logical_check_post forward in
  let resultList = List.fold_left (fun acc a -> acc ^ (string_of_es a) ^ "\n") "\n" logical_res in 
  let info = "\nForward Result = " ^ resultList in 
  let head = "<<<<< Logical Correctness Checking >>>>>\n=========================\n" in 
  if List.length logical_res == 0 then head ^ "Logical incorrect! (null valid assignments)" 
  else if List.length logical_res >1 then head ^ "Logical incorrect! (multiple valid assignments)\n"  ^ info 
  else 
  if (List.length spec > 0 ) then 
    let verification  = printReport logical_res spec in 
    head ^ "Logical correct! " ^ info ^"\n <<<<< Temporal Verification >>>>>\n" ^ verification
  else 
    head ^ "Logical correct! " ^ info
   ;;


let () =
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
(*    let outputfile = (Sys.getcwd ()^ "/" ^ Sys.argv.(2)) in
print_string (inputfile ^ "\n" ^ outputfile^"\n");*)
  let ic = open_in inputfile in
  try
      let lines =  (input_lines ic ) in
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in
      let prog = Parser.full_prog Lexer.token (Lexing.from_string line) in

      (*print_string (string_of_prog prog^"\n");*)
      print_string ( (analyse prog) ^"\n");
      
      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;
