Module AST.

Require Import FunInd.
From Coq Require Import Arith Bool Ascii String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Require Import Coq.Program.Wf.
Require Import Coq.Arith.Plus.

Definition numEvent := 10.

(* the default value of a siganl is absent *)
Inductive signalState : Type := zero | one | undef.

Definition signal_status : Type :=  (string * signalState).

Definition instance : Type :=  (list signal_status).



Definition string_of_signal_status (pair:signal_status) : string :=
let (name, status) := pair in
(match status with
| zero => "!"  ++  name
| one  => ""  ++  name
| undef => "~" ++  name
end).

Definition compareStatus (s1 s2: signalState): bool :=
match (s1, s2) with
| (zero, zero)   => true
| (one, one) => true
| (undef, undef) => true
| _                  => false
end.

Definition string_of_instance (ins: instance): string :=
"{" ++
(
let fix helper (li:instance) : string :=
match li with
| [] => ""
| [x]  => string_of_signal_status x
| x::xs =>  string_of_signal_status x ++ "," ++ helper xs
end in
helper (List.filter (fun (pair:signal_status) =>
  let (name, status) := pair in
    Bool.eqb (compareStatus one status) true ) ins)
)
++ "}".

Inductive syncEff : Type :=
| bot
| emp
| singleton (s: instance)
| waiting   (s:string)
| cons      (es1: syncEff) (es2: syncEff)
| disj      (es1: syncEff) (es2: syncEff)
| parEff    (es1: syncEff) (es2: syncEff)
| kleene    (es: syncEff).

Inductive expression : Type :=
| nothingE
| pauseE
| emitE     (s:string)
| localDelE (s:string)  (e:expression)
| seqE      (e1:expression) (e2:expression)
| parE      (e1:expression) (e2:expression)
| ifElseE   (s:string) (e1:expression) (e2:expression)
| loopE     (e:expression)
(*| suspendE  (e:expression) (s:string)*)
| asyncE    (e:expression) (s:string)
| awaitE    (s:string)
| raiseE    (n:nat)
| trycatchE (e:expression) (handler:expression)
.
(*

differnce: sync - presnet valid for one time cycle 
           async- manuelly turn off the present signals.
*)


(* last argument is the completion code true -> normal, flase -> not completed*)
Definition state : Type := (syncEff * (option instance) * nat).

Definition states : Type := list state.


Notation "'_|_'" := bot (at level 0, right associativity).

Notation "'ϵ'" := emp (at level 0, right associativity).

Notation "+ A" := (A, one) (at level 0, right associativity).

Notation "! A" := (A, zero) (at level 0, right associativity).

Notation "'{{' Eff '}}'" := (singleton Eff) (at level 100, right associativity).

Notation " I1  @  I2 " := (cons I1 I2) (at level 100, right associativity).

Notation " I1  'or'  I2 " := (disj I1 I2) (at level 100, right associativity).

Notation " I1  '//'  I2 " := (parEff I1 I2) (at level 100, right associativity).

Notation "'star' I" := (kleene I) (at level 200, right associativity).



Notation "'nothing'" := nothingE (at level 200, right associativity).

Notation "'pause'" := pauseE (at level 200, right associativity).

Notation "'emit' A" := (emitE A) (at level 200, right associativity).

Notation "'signal' A 'in' E" := (localDelE A E)  (at level 200, right associativity).

Notation "E1 ; E2" := (seqE E1 E2)  (at level 200, right associativity).

Notation "'fork' E1 'par' E2" := (parE E1 E2)  (at level 80, right associativity).

Notation "'present' A 'then' E1 'else' E2" := (ifElseE A E1 E2)  (at level 200, right associativity).
Notation "'loop' E" := (loopE E) (at level 200, right associativity).

(*
Notation "'suspend' E 'when' S" := (suspendE E S) (at level 200, right associativity).
*)

Notation "'async' E 'with' S" := (asyncE E S) (at level 200, right associativity).

Notation "'await' S" := (awaitE S) (at level 200, right associativity).

Notation "'raise' N" := (raiseE N) (at level 200, right associativity).

Notation "'trap' E1 'catchwith' E2" := (trycatchE E1 E2) (at level 200, right associativity).
