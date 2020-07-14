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
  | Seq (p1, p2) ->  "(seq " ^ string_of_prog p1 ^ " " ^ string_of_prog p2 ^" )"
  | Par (p1, p2) ->  "(par " ^ string_of_prog p1 ^ " " ^ string_of_prog p2 ^" )"
  | Loop pIn -> "(loop " ^ string_of_prog pIn ^ ")"
  | Declear (s, prog) -> "(signal " ^ s ^ " " ^ string_of_prog prog ^" )"
  | Emit s -> "(emit " ^ s ^ ")"
  | Present (s, p1, p2) -> "(present " ^ s ^ " " ^ string_of_prog p1 ^" " ^ string_of_prog p2 ^" )"
  | Trap (mn, prog) -> "(trap "  ^ mn ^" " ^ string_of_prog prog ^" )"
  | Exit (mn, d) -> "(exit " ^ mn ^" " ^ string_of_int d^ ")"
  ;;

let string_of_sl (sl):string = 
  List.fold_left (fun acc (name, state) -> acc ^ " " ^ (match state with One -> name | Zero -> (*"!" ^name*) "")) "" sl
;;

let string_of_instance ((cons, mapping):instance) :string = 
  if List.length mapping == 0 then ""
  else 
  (*let temp = "(" ^ string_of_sl cons ^ ")" in 
  *)
  let temp1 = "[" ^ string_of_sl mapping ^ "]" in 
  (*temp ^ " & " ^*)
  temp1
  ;;


let rec string_of_es (es:es) :string = 
  match es with 
    Bot -> "_|_"  
  | Emp -> "emp"
  | Instance ins  -> string_of_instance ins
  | Con (es1, es2) ->  string_of_es es1 ^ " . " ^ string_of_es es2
  | Omega esIn -> "(" ^ string_of_es esIn ^ ")^w"
  | Any -> "_"
  | Kleene esIn -> "(" ^ string_of_es esIn ^ ")^*" 
  | Ntimed (esIn, n) ->"(" ^ string_of_es esIn ^ ")^" ^ string_of_int n 
  | Not esIn -> "(!" ^ string_of_es esIn ^ ")"
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


