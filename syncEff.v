Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Coq.Strings.String.

Notation instance :=  (list string).

Inductive syncEff : Type :=
| nil
| emp
| singleton (s: instance)
| waiting (s:string)
| cons (es1: syncEff) (es2: syncEff)
| parEff (es1: syncEff) (es2: syncEff)
| kleene (es: syncEff)
| infinit (es: syncEff).

Notation effects := (list syncEff).

Inductive expr : Type :=
| nothing
| pause
| emit (s:string)
| signal (s:string)  (e:expr)
| seq (e1:expr) (e2:expr)
| par (e1:expr) (e2:expr)
| present  (s:string) (e1:expr) (e2:expr)
| loop  (e:expr)
| suspend  (e:expr) (s:string)
| async (e:expr) (s:string)
| await (s:string)
| raise (s:string)
| trycatch (e:expr) (s:string) (handler:expr)
.

Notation state := (list (syncEff * instance)).

Fixpoint forward (state:state) (expr:expr) :state= 
match expr with
| nothing => state
| _ => state
end.

