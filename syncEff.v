From Coq Require Import Arith Bool Ascii String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(* the default value of a siganl is absent *)
Inductive signalState : Type := absent | present.

Definition signal : Type :=  (string * signalState).

Definition instance : Type :=  (list signal).

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
| nothing
| pause
| emit     (s:string)
| localDel (s:string)  (e:expression)
| seq      (e1:expression) (e2:expression)
| par      (e1:expression) (e2:expression)
| ifElse   (s:string) (e1:expression) (e2:expression)
| loop     (e:expression)
| suspend  (e:expression) (s:string)
| async    (e:expression) (s:string)
| await    (s:string)
| raise    (s:string)
| trycatch (e:expression) (s:string) (handler:expression)
.

Definition envenvironment : Type := (list string).

(*
Definition trace : Type := (syncEff * instance).
Definition traces : Type := (list trace).


Fixpoint initialInstance (env:envenvironment): instance :=
  List.map (fun str => (str, undef)) env.

Fixpoint setPresent (ins:instance) (str:string) :instance :=
  match ins with
  | [] => []
  | (name, status)  :: xs => if eqb name str then (str, present)::xs else  (name, status) :: (setPresent xs str)
end.
*)


Fixpoint nullable (eff:syncEff): bool :=
match eff with
| bot          => false
| emp          => true
| singleton _  => false
| waiting   _  => false
| disj e1 e2   => nullable e1 || nullable e2
| cons e1 e2   => nullable e1 && nullable e2
| parEff e1 e2 => nullable e1 && nullable e2
| kleene _     => true
end.

Fixpoint fst (eff:syncEff): list instance  :=
match eff with
| bot          => []
| emp          => []
| singleton i  => [i]
| waiting   s  => [[(s, present)]] ++ [[(s, absent)]]
| disj e1 e2   => fst e1 ++ fst e2
| cons e1 e2   => if nullable e1 then fst e1 ++ fst e2
                  else fst e1
| parEff e1 e2 => let f1 := fst e1 in
                  let f2 := fst e2 in
                  List.flat_map (fun f1In => List.map (fun f2In => List.app f1In f2In) f2) f1
| kleene e     => fst e
end.

Definition compareStatus (s1 s2: signalState): bool :=
match (s1, s2) with
| (absent, ansent)   => true
| (present, present) => true
(*
(* I decided not to care about the undefined status for now *)
| (undef, undef)     => true
*)
| _                  => false
end.

Fixpoint instanceEntail (ins1 ins2 : instance): bool :=
  let fix exist (sig:signal) (ins:instance) : bool :=
     let (name, status) := sig in
     match ins with
     | [] => false
     | (name', status') :: xs => if eqb name name' && compareStatus status status'
                                 then true else exist sig xs
     end in
  match ins1 with
  | [] => true
  | y :: ys => if exist y ins2 then instanceEntail ys ins2 else false
  end.


Definition zip_list {A : Type} (l1 l2 : list A): list (A * A) :=
List.flat_map (fun a => (List.map (fun b => (a, b)) l2)) l1.

Fixpoint derivitive (eff:syncEff) (f:instance) : syncEff :=
match eff with
| bot          => bot
| emp          => bot
| singleton i  => if instanceEntail f i then emp else bot
| waiting   s  => if instanceEntail ([(s, present)]) f then emp else waiting s
| cons e1 e2   => if nullable e1 then disj (cons (derivitive e1 f) e2)  (derivitive e2 f)
                  else cons (derivitive e1 f) e2
| disj e1 e2   => disj (derivitive e1 f) (derivitive e2 f)
| kleene e     => cons (derivitive e f) eff
| parEff e1 e2 => let f1 := fst e1 in
                  let f2 := fst e2 in
                  let zipFst := zip_list f1 f2 in
                  let deris := List.map (fun (pair:(instance * instance)) =>
                                  let (a, b) := pair in
                                  if instanceEntail f (List.app a b)
                                  then parEff (derivitive e1 a) (derivitive e2 b)
                                  else bot) zipFst in
                  List.fold_left (fun acc t => disj acc t) deris bot
end.

Fixpoint normal (eff:syncEff) : syncEff :=
match eff with
| bot          => eff
| emp          => eff
| singleton _  => eff
| waiting   _  => eff
| cons bot  _  => bot
| cons emp e   => e
| cons e emp   => e
| cons e1 e2   => cons (normal e1) (normal e2)
| disj bot e   => e
| disj e bot   => e
| disj e1 e2   => disj (normal e1) (normal e2)
| parEff e1 e2 => parEff (normal e1) (normal e2)
| kleene emp   => emp
| kleene e     => kleene (normal e)
end.

Compute (fst (kleene (singleton [("S", present)]))).
Compute (normal (derivitive (kleene (singleton [("S", present)])) [("K", present)])).

Definition state : Type := (syncEff * instance).

Definition states : Type := list state.

Fixpoint effectToStates (*cut function *) (eff:syncEff): states :=
match eff with
| bot          => []
| emp          => [(emp, [])]
| singleton i  => [(emp, i)]
| waiting   s  => [(eff, [])] (* S? = (not S)^*.(S) *)
| disj e1 e2   => List.app (effectToStates e1) (effectToStates e2)
| cons e1 e2   => let ss := effectToStates e2 in
                  List.map (fun (pair:(state)) =>
                              let (his, cur) := pair in
                              (cons e1 his, cur)) ss
| kleene e     => let ss := effectToStates e in
                  List.map (fun (pair:(state)) =>
                              let (his, cur) := pair in
                              (cons eff his, cur)) ss
| parEff e1 e2 => [] (* this should not be here ... *)
end.

Fixpoint parallelMergeEffects (eff1 eff2: syncEff) : list syncEff :=
let f1s := fst eff1 in
let f2s := fst eff2 in
let zipFst := zip_list f1s f2s in
List.flat_map (fun (pair:(instance * instance)) =>
           let (f1, f2) := pair in
           let der1 := normal (derivitive eff1 f1) in
           let der2 := normal (derivitive eff1 f2) in
           match (der1, der2) with
           | (bot, e2) => []
           | (e1, bot) => []
           | (emp, e2) => [e2]
           | (e1, emp) => [e1]
           | _         =>
             let parallelRest:list syncEff  := parallelMergeEffects der1 der2 in
             List.map (fun trace => cons (singleton (List.app f1 f2)) trace) parallelRest
           end
) zipFst.

I think perhaps I need to distinguish kleene and the rest, so that
the derivitive is decresing for sure. 


Definition parallelMergeState (states1 states2: states) : states :=
let mix_states   := zip_list states1 states2 in
List.flat_map (fun (pair:(state * state)) =>
  let (s1, s2)      := pair in
  let (eff1, cur1) := s1 in
  let (eff2, cur2) := s2 in
  let fulltraces () : syncEff :=
    let trace1 := normal (cons eff1 (singleton cur1)) in
    let trace2 := normal (cons eff2 (singleton cur2)) in
    parallelMergeEffects eff1 eff2
  in
  effectToStates (normal fulltraces)

) mix_states.






Fixpoint forward (env:envenvironment) (s:states) (expr:expression) : states :=
List.flat_map (fun (pair:state) =>
  let (his, cur) := pair in
  match expr with
  | nothing        => [pair]
  | pause          => [(cons his (singleton cur), [])]
  | emit str       => [(his, (str, present)::  cur)]
  | localDel str e => let newEnv   := (str)::env in
                      forward newEnv [pair] e
  | seq e1 e2      => let s1 := (forward env s e1) in
                      forward env s1 e2
  | par e1 e2      => let s1 := (forward env s e1) in
                      let s2 := (forward env s1 e2) in
                      parallelMergeState s1 s2
  | _              => [pair]
  end
) s.


