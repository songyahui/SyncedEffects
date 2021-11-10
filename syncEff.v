Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Sets.Ensembles.
From Coq Require Import Bool Ascii String.

Inductive signalState : Type := absent | present | undef.

Definition signal : Type :=  (string * signalState).

Definition instance : Type :=  (list signal).

Inductive syncEff : Type :=
| bot
| emp
| singleton (s: instance)
| waiting   (s:string)
| cons      (es1: syncEff) (es2: syncEff)
| parEff    (es1: syncEff) (es2: syncEff)
| kleene    (es: syncEff)
| infinit   (es: syncEff).

Definition effects : Type := (list syncEff).

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

Definition trace : Type := (syncEff * instance).
Definition traces : Type := (list trace).
Definition envenvironment : Type := (list string).

Fixpoint initialInstance (env:envenvironment): instance :=
  List.map (fun str => (str, undef)) env.

Fixpoint setPresent (ins:instance) (str:string) :instance :=
  match ins with
  | [] => []
  | (name, status)  :: xs => if eqb name str then (str, present)::xs else  (name, status) :: (setPresent xs str)
end.

Fixpoint nullable (eff:syncEff): bool :=
match eff with
| bot          => false
| emp          => true
| singleton _  => false
| waiting   _  => false
| cons e1 e2   => nullable e1 && nullable e2
| parEff e1 e2 => nullable e1 && nullable e2
| kleene _     => true
| infinit _    => false
end.

Fixpoint fst (eff:syncEff): list instance  :=
match eff with
| bot          => []
| emp          => []
| singleton i  => [i]
| waiting   s  => [[(s, present)]] ++ [[(s, absent)]]
| cons e1 e2   => if nullable e1 then fst e1 ++ fst e2
                  else fst e1
| parEff e1 e2 => let f1 := fst e1 in
                  let f2 := fst e2 in
                  List.flat_map (fun f1In => List.map (fun f2In => f1In ++ f2In) f2) f1
| kleene e     => fst e
| infinit e    => fst e
end.

Definition compareStatus (s1 s2: signalState): bool :=
match (s1, s2) with
| (absent, ansent)   => true
| (present, present) => true
| (undef, undef)     => true
| _                  => false
end.

Fixpoint instanceEntail (ins1 ins2 : instance): bool :=
  let fix exist (sig:signal) (ins:instance) : bool :=
     let (name, status) := sig in
     match ins with
     | [] => false
     | (name', status') :: xs => if eqb name name' && compareStatus status status' then true else exist sig xs
     end in
  match ins1 with
  | [] => true
  | y :: ys => if exist y ins2 then instanceEntail ys ins2 else false
  end.


Fixpoint derivitive (eff:syncEff) (f:instance) : list syncEff :=
match eff with
| bot          => [bot]
| emp          => [bot]
| singleton i  => if instanceEntail f i then [emp] else [bot]
| waiting   s  => if instanceEntail ([(s, present)]) f then [emp] else [waiting s]
| cons e1 e2   => let der1 := List.map (fun head => cons head e2)  (derivitive e1 f) in
                  if nullable e1 then der1 ++ derivitive e2 f
                  else der1
| kleene e     => List.map (fun head => cons head eff)  (derivitive e f)
| infinit e    => List.map (fun head => cons head eff)  (derivitive e f)
| parEff e1 e2 => let f1 := fst e1 in
                  let f2 := fst e2 in
                  List.flat_map (fun f1In => List.map (fun f2In => f1In ++ f2In) f2) f1
end.





Definition mergeState (s1 s2: traces) : traces :=
  let mix : (list (trace * trace)) := List.flat_map (fun s1In => List.map (fun s2In => (s1In, s2In)) s2) s1 in
  s1.


Fixpoint forward (env:envenvironment) (state:traces) (expr:expression) : traces :=
match expr with
| nothing        => state
| pause          => List.map (fun (pair:trace) =>
                         let (his, cur):= pair in
                         (cons his (singleton cur), initialInstance env )) state
| emit str       => List.map (fun (pair:trace) =>
                         let (his, cur):= pair in
                         (his, setPresent cur str )) state
| localDel str e => let newEnv   := (str)::env in
                    let newState := List.map (fun (pair: trace) =>
                                               let (his, cur):= pair in
                                               (his,(str, undef) :: cur)) state in
                    forward newEnv newState e
| seq e1 e2      => let state1 := (forward env state e1) in
                    forward env state1 e2
| par e1 e2      => let state1 := (forward env state e1) in
                    let state2 := (forward env state e2) in
                    mergeState state1 state2
| _              => state
end.

