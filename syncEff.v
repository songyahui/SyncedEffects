From Coq Require Import Arith Bool Ascii String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

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
| undef => ""
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
  Bool.eqb (compareStatus undef status) false) ins)
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
| suspendE  (e:expression) (s:string)
| asyncE    (e:expression) (s:string)
| awaitE    (s:string)
| raiseE    (n:nat)
| trycatchE (e:expression) (handler:expression)
.
(*

differnce: sync - presnet valid for one time cycle 
           async- manuelly turn off the present signals.
*)

Notation "'_|_'" := bot (at level 0, right associativity).

Notation "'ϵ'" := emp (at level 0, right associativity).

Notation "% A" := (A, one) (at level 0, right associativity).

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

Notation "'suspend' E 'when' S" := (suspendE E S) (at level 200, right associativity).

Notation "'async' E 'with' S" := (asyncE E S) (at level 200, right associativity).

Notation "'await' S" := (awaitE S) (at level 200, right associativity).

Notation "'raise' N" := (raiseE N) (at level 200, right associativity).

Notation "'trap' E1 'catchwith' E2" := (trycatchE E1 E2) (at level 200, right associativity).


Definition envenvironment : Type := (list string).


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
| waiting   s  => [([])] (*[[(s, one)]] ++ [[(s, zero)]]*)
| disj e1 e2   => fst e1 ++ fst e2
| cons e1 e2   => if nullable e1 then fst e1 ++ fst e2
                  else fst e1
| parEff e1 e2 => let f1 := fst e1 in
                  let f2 := fst e2 in
                  List.flat_map (fun f1In => List.map (fun f2In => List.app f1In f2In) f2) f1
| kleene e     => fst e
end.



Fixpoint existSigIns (sig:signal_status) (ins:instance) : bool :=
     let (name, status) := sig in
     match ins with
     | [] => false
     | (name', status') :: xs => if eqb name name' && compareStatus status status'
                                 then true else existSigIns sig xs
     end.

Fixpoint instanceEntail (ins1 ins2 : instance): bool :=
  match ins2 with
  | [] => true
  | y :: ys => if existSigIns y ins1 then instanceEntail ins1 ys else false
  end.

Definition instanceEntailShell (ins1 ins2 : option instance) : bool :=
match ins1 with
| None => true
| Some ins1In =>
  (match ins2 with
   | None => false
   | Some ins2In => instanceEntail ins1In ins2In
  end)
end.

Compute (instanceEntail [("s", zero); ("s1", one)] [("s", one)]).

Compute (instanceEntail [] [("s", one)]).


Definition zip_list {A : Type} (l1 l2 : list A): list (A * A) :=
List.flat_map (fun a => (List.map (fun b => (a, b)) l2)) l1.

Fixpoint derivitive (eff:syncEff) (f:instance) : syncEff :=
match eff with
| bot          => bot
| emp          => bot
| singleton i  => if instanceEntail f i then emp else bot
| waiting   s  => if instanceEntail f ([(s, one)]) then emp else waiting s
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

Compute (derivitive (waiting "D") [("D", undef);( "D", one)] ).

Definition controdictStatus (s1 s2: signalState): bool :=
match (s1, s2) with
| (zero, one)   => true
| _                  => false
end.

Definition controdict (ins: instance) : bool :=
let fix aux (i:signal_status) (li:instance) : bool :=
let (name',status'):= i in
match li with
| [] => false
| (name, status):: xs => if eqb name name' && (controdictStatus status status')
                         then true else aux i xs
end in
let fix helper li :bool :=
match li with
| [] => false
| y :: ys => if aux y ins then true else helper ys
end in
helper ins.

Fixpoint remove_dup (ins: instance) : instance :=
match ins with
| [] => []
| [x] => [x]
| y :: ys => if existSigIns y ys then remove_dup ys else y :: (remove_dup ys)
end.



Fixpoint normal (eff:syncEff) : syncEff :=
match eff with
| bot          => eff
| emp          => eff
| singleton ins=> eff(*if controdict ins then bot else singleton (remove_dup ins)*)
| waiting   _  => eff
| cons bot  _  => bot
| cons emp e   => normal e
| cons e emp   => normal e
| cons (kleene e) _ =>  kleene e
| cons e1 e2   => cons (normal e1) (normal e2)
| disj bot e   => normal e
| disj e bot   => normal e
| disj e1 e2   => disj (normal e1) (normal e2)
| parEff e1 e2 => parEff (normal e1) (normal e2)
| kleene emp   => emp
| kleene e     => kleene (normal e)
end.

Compute (fst (kleene (singleton [("S", one)]))).
Compute (normal (derivitive (kleene (singleton [("S", one)])) [("K", one)])).

(* last argument is the completion code true -> normal, flase -> not completed*)
Definition state : Type := (syncEff * (option instance) * nat).

Definition states : Type := list state.

Definition instanceEqual (i1 i2: instance) : bool :=
instanceEntail i1 i2 && instanceEntail i2 i1.


Fixpoint reoccur (records :list instance) (i:instance) : bool :=
match records with
| [] => false
| x::xs => if instanceEqual x i then true else  reoccur xs i
end.


Definition recordsToEff  (records :list instance) :syncEff :=
  normal (List.fold_left (fun acc a => cons acc (singleton a)) records emp).

Definition formloop  (records :list instance) (i:instance) :syncEff :=
let fix aux (re:list instance) : syncEff :=
    match re with
    | [] => emp
    | x::xs => if instanceEqual i x then kleene (recordsToEff re)
               else cons (singleton x) (aux xs)
    end
in aux records.

Require Import Coq.Program.Wf.

Definition leftHy  (records :list instance) : nat :=
numEvent * numEvent - (List.length records).

Definition conflitStatus (s1 s2: signalState): bool :=
match (s1, s2) with
| (zero, zero)   => false
| (one, one)     => false
| (undef, undef) => false
| _              => true
end.

Definition tryToMerge (i1 i2: instance) : option instance :=
  let merge := List.app i1 i2 in 
  let fix helper (li:instance) (name:string) (status:signalState) : bool :=
    match li with 
    | [] => false 
    | (name', status'):: xs => if eqb name name' && (conflitStatus status status')
                         then true else helper xs name status
    end in
  let fix hasConflits (li:instance): bool :=
    match li with 
    | [] => false 
    | (name, status):: xs => if helper xs name status
                         then true else hasConflits xs
    end
  in 
  if hasConflits merge then None else Some merge.

Compute (tryToMerge [("A", one)] [("B", zero)] ).
    

Program Fixpoint fixpoint (records :list instance) (eff1 eff2: syncEff) {measure (leftHy records)} : syncEff :=
match eff1 with
| emp => cons (recordsToEff records) eff2
| _   =>
  (match eff2 with
   | emp => cons (recordsToEff records) eff1
   | _ =>
     let f1s := fst eff1 in
     let f2s := fst eff2 in
     let zipFst := zip_list f1s f2s in
     let effList : list (syncEff):= 
         List.map (fun (pair: (instance * instance )) =>
            let (f1, f2):=pair in
            let merge := (List.app f1 f2) in
            let der1 := (normal (derivitive eff1 f1)) in
            let der2 := (normal (derivitive eff2 f2)) in
            if (reoccur records merge) then (formloop records merge)
            else (fixpoint (merge :: records) der1 der2)
            
         ) zipFst in
     normal (List.fold_left (fun acc a => disj acc a) effList bot)
     (*let effList : list (option syncEff):= 
         List.map (fun (pair: (instance * instance )) =>
            let (f1, f2):=pair in
            let merge := (tryToMerge f1 f2) in
            match merge with 
            | None => None
            | Some merge =>
                let der1 := (normal (derivitive eff1 f1)) in
                let der2 := (normal (derivitive eff2 f2)) in
                if (reoccur records merge) then Some (formloop records merge)
                else Some (fixpoint (merge :: records) der1 der2)
            end
         ) zipFst in
     normal (List.fold_left (fun acc a => 
          match a with 
          | None => acc 
          | Some a => disj acc a
          end ) effList bot)
*)
  end)
end.

Next Obligation. Proof. Admitted.

Local Open Scope nat_scope.

Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | 0  , _   => true
  | _  , 0   => false
  | S n, S m => leb n m
  end.

Definition greaterThan (n m: nat) : bool  :=
  match (leb n m) with
  | true => false
  | false=> true
  end.

Definition natEq (n m: nat) : bool  :=
 leb n m && leb m n.


Definition max_k (k1 k2: nat) : nat :=
if greaterThan k1 k2 then k1 else k2.

Compute (max_k 1 2).

Compute (max_k 10 5).

Compute (natEq 4 4).

Definition mergeCurrentToEff (c: option instance) (eff:syncEff): syncEff :=
match c with
| None => eff
| Some i =>
  match normal eff with
  | emp => singleton i
  | _   =>
    let fst := fst eff in
    let effList := List.map (fun f => cons (singleton (List.app f i)) (derivitive eff f)) fst in
    normal (List.fold_left (fun acc a => disj acc a) effList bot)
  end
end.

Definition mergeCurrent (c1 c2: option instance) : option instance :=
match c1, c2 with
| None, None => None
| Some i1, None => c1
| None, _ => c2
| Some i1, Some i2 => Some (List.app i1 i2)
end.



(*
"{}.{A}"
"{A,B,H}.{C}.{D,S}"
*)


Program Fixpoint fixpointState (records :list instance) (s1 s2:state) {measure (leftHy records)} : states :=
let '(eff1, cur1, k1) := s1 in
let '(eff2, cur2, k2) := s2 in
let f1s := fst eff1 in
let f2s := fst eff2 in
match normal eff1, normal eff2(*List.length f1s, List.length f2s*) with
| emp, emp => [(recordsToEff records, mergeCurrent cur1 cur2, max_k k1 k2)]
| emp, _   => [(cons (recordsToEff records) (mergeCurrentToEff cur1 eff2), cur2, k2)]
| _, emp   => [(cons (recordsToEff records) (mergeCurrentToEff cur2 eff1), cur1, k1)]
| _,_      =>
     let zipFst := zip_list f1s f2s in
     List.flat_map (fun (pair: (instance * instance )) =>
          let (f1, f2):=pair in
          let merge := (List.app f1 f2) in
          let der1 := (normal (derivitive eff1 f1)) in
          let der2 := (normal (derivitive eff2 f2)) in
          if (reoccur records merge) then [(formloop records merge, None, max_k k1 k2)]
          else (fixpointState (merge :: records) (der1, cur1, k1) (der2, cur2, k2))
     ) zipFst
     (*let stateListRow: list (option state) :=
         List.flat_map (fun (pair: (instance * instance )) =>
             let (f1, f2):=pair in
             let merge := (tryToMerge f1 f2) in
             match merge with 
             | None => [None]
             | Some merge =>
                  let der1 := (normal (derivitive eff1 f1)) in
                  let der2 := (normal (derivitive eff2 f2)) in
                  if (reoccur records merge) then [(Some (formloop records merge, None, max_k k1 k2))]
                  else (List.map (fun a=> Some a)
                        (fixpointState (merge :: records) (der1, cur1, k1) (der2, cur2, k2)))
             end) zipFst in 
     List.fold_left (fun acc a => 
        match a with 
        | None => acc
        | Some s => List.app acc [s] end) stateListRow []
*)
    
end.



Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.

Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.

Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.

Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.
Next Obligation. Proof. Admitted.



Definition parallelMergeState (states1 states2: states) : states :=
let mix_states   := zip_list states1 states2 in
List.flat_map (fun (pair:(state * state)) =>
  let (s1, s2)     := pair in
  fixpointState [] s1 s2
) mix_states.


Definition instanceToEff (cur: option instance) : syncEff :=
match cur with
| None => emp
| Some ins => singleton ins
end.



Fixpoint extendEff (eff:syncEff) (i:signal_status): syncEff :=
match eff with
| singleton ins=> singleton (List.app ins [i])
| cons e1 e2   => cons (extendEff e1 i) (extendEff e2 i)
| disj e1 e2   => disj (extendEff e1 i) (extendEff e2 i)
| parEff e1 e2 => parEff (extendEff e1 i) (extendEff e2 i)
| kleene e     =>  kleene (extendEff e i)
| _            => eff
end.

Definition existRaise (s: string) (ins: option instance)  : bool :=
match ins with
| None => false
| Some insIn =>
  let fix aux insA : bool :=
  (match insA with
   | [] => false
   | (name, one) :: xs => if eqb name s then true else aux xs
   | _ :: xs           => aux xs
  end) in aux insIn
end.


Definition initalCur (env:envenvironment) : instance :=
List.map (fun a => (a, undef)) env.


Definition setSigInCur (env:envenvironment) (cur: option instance) (ss:signal_status): option instance :=
let (name', status') := ss in
let fix aux (li:instance) : instance :=
    match li with
    | [] => [(ss)]
    | (name, status) :: xs => if eqb name name' && (compareStatus status status' || compareStatus status undef)
                              then ss :: xs
                              else (name, status) :: (aux xs)
    end
in
match cur with
| None => Some (aux (initalCur env))
| Some insIn => Some (aux insIn)
end.

Compute (setSigInCur ["A";"B";"C"] (setSigInCur ["A";"B";"C"] None ("A", one)) ("A", one)).

Definition appendSigInCur (env:envenvironment) (cur: option instance) (ss:signal_status): option instance :=
match cur with
| None => (Some (ss :: initalCur env))
| Some insIn => (Some (ss :: insIn))
end.



Fixpoint forward (env:envenvironment) (s:states) (expr:expression) : states :=
List.flat_map (fun (pair:state) =>
  let '(his, cur, k) := pair in
  (*
    if greaterThan k 0 then [pair]
  else
   *)
  match expr with
  | nothingE        => [pair]
  | pauseE          => [(cons his (instanceToEff cur), Some (initalCur env), k)]
  | raiseE n        => [(his, cur, S k)]
  | emitE str       => [(his, setSigInCur env cur (str, one), k)]
  | localDelE str e => let newEnv   := (str)::env in
                       forward newEnv [pair] e
  | seqE e1 e2      => match e1 with
                       | asyncE _ _ =>
                         let s1 := (forward env [pair] e1) in
                         let s2 := (forward env [pair] e2) in
                         parallelMergeState s1 s2
                       | _ =>
                         let s1 := (forward env [pair] e1) in
                         List.flat_map
                           (fun (pairE:state)  =>
                              let '(hisE, curE, kE) := pairE in
                              if greaterThan kE 0 then [pairE]
                              else forward env [pairE] e2) s1
                       end
  | parE e1 e2      => let s1 := (forward env [pair] e1) in
                       let s2 := (forward env [pair] e2) in
                       parallelMergeState s1 s2
  | ifElseE s e1 e2 => if instanceEntailShell cur (Some [(s, one)])
                       then forward env [pair] e1
                       else forward env [pair] e2
  | asyncE e str    => let s1 := (forward env [pair] e) in
                       List.map (fun (pairE:state) =>
                                   let '(hisE, curE, kE) := pairE in
                                   (hisE, setSigInCur env curE (str, one), kE)) s1
  | awaitE s        => [(cons his (cons (instanceToEff cur) (waiting s)), None, k)]
  | suspendE e str  => let s1 := (forward env [(emp, cur, k)] e) in
                       List.map (fun (pairE:state) =>
                                   let '(hisE, curE, kE) := pairE in
                                   let newhis := cons his (extendEff hisE (str, zero)) in
                                   let newCur := setSigInCur env curE (str, zero) in
                                   (newhis, newCur, kE)) s1
  | trycatchE e h => let s1 := (forward env [pair] e) in
                       List.flat_map
                         (fun (pairE:state) =>
                            let '(hisE, curE, kE) := pairE in
                            if  natEq k 0 then  [pairE]
                            else if  natEq k 1 then (forward env [(hisE, curE, 0)] h)
                            else [(hisE, curE, kE -1)]) s1
  | loopE e         => let s1 := (forward env [(emp, cur, k)] e) in
                       let newState :=
                           (List.map (fun (pairE:state) =>
                                        let '(_, curE, kE) := pairE in
                                        (emp, curE, kE)) s1) in
                       let hisList :=
                           (List.map (fun (pairE:state) =>
                                        let '(hisE, _, _) := pairE in
                                        hisE) s1) in
                       let s2 := (forward env newState e) in
                       List.map (fun (pairE:(state*syncEff)) =>
                                  let (tuple, hisS1) := pairE in
                                  let '(hisE, curE, kE) := tuple in
                                  if greaterThan k 0 then tuple
                                  else (cons (cons his hisS1) (kleene hisE), None, k))
                                (List.combine s2 hisList)
  end
) s.



Fixpoint string_of_effects (eff:syncEff) : string :=
match eff with
| bot          => "_|_"
| emp          => ""
| singleton ins=> string_of_instance ins
| waiting   s  => s ++ "?"
| cons e1 e2   =>  string_of_effects e1 ++ "." ++ string_of_effects e2
| disj e1 e2   =>  "(" ++ string_of_effects e1 ++ "\/" ++ string_of_effects e2 ++ ")"
| parEff e1 e2 =>  "(" ++ string_of_effects e1 ++ "||" ++ string_of_effects e2 ++ ")"
| kleene e     =>  "(" ++ string_of_effects e ++ ")^*"
end.

Definition state_to_eff (s:state) : syncEff :=
let '(his, cur, k) := s in
if greaterThan k 0 then bot
else normal (cons his (instanceToEff cur)).

Definition states_to_eff (states:states) : syncEff :=
normal (List.fold_left (fun acc a => disj acc (state_to_eff a)) states bot).

Definition env := ["A"; "B"; "C"; "D"; "E"; "F"; "H"; "T"; "X"; "Y"; "Z" ].

Definition forward_Shell (expr:expression) : string :=
  string_of_effects(
      states_to_eff(
          forward env [(emp, None, 0)] expr)).


Definition testSeq : expression :=
  emit "B";
  emit "A";
  emit "B";
  pause;
  emit "C";
  pause;
  emit "D".


Definition testSeq1 : expression :=
  emit "A";
  emit "B";
  pause;
  emit "C";
  pause;
  emit "D";
  pause.

Definition testSeq2 : expression :=
  pause;
  emit "A";
  emit "B";
  pause;
  emit "C";
  pause;
  emit "D";
  pause.

Definition testSeq3 : expression :=
  pause;
  emit "A";
  emit "B";
  pause;
  emit "C";
  pause;
  emit "D".

Definition testRaise : expression :=
  raise 1.

Definition testTry : expression :=
  trap testRaise catchwith testSeq.

Definition testTry1 : expression :=
  trap testRaise catchwith testSeq.


Definition testPresent : expression :=
  present "A" then testSeq else (emit "B").

Definition testLoop : expression :=
  loop testSeq.


Definition testSuspend : expression :=
  suspend testSeq when "S".



Definition testLoop1 : expression :=
  (loop testSeq).


Definition testPause : expression :=
  pause; pause; emit "P".

Definition testAsync : expression :=
  async testSeq with "S".

Definition testPal : expression :=
  fork testSeq  par (await "C").

Definition testPal1 : expression :=
  fork (testPause) par (fork testAsync  par (emit "H")).

Definition testPal2 : expression :=
   fork (emit "C") par (await "C").

Definition testPal3 : expression :=
   fork (emit "D";pause;emit"D") par (await "D").

Definition testAsyncSeq : expression :=
  async testSeq with "S"; emit "L".

Definition testAsyncSeq1 : expression :=
  async testSeq with "S"; await "S" ; emit "K".

Compute (forward_Shell testPal2).





(*

cav14 https://www.comp.nus.edu.sg/~chinwn/papers/TRs2.pdf
aplas13 https://trinhmt.github.io/home/SpecInfer/technical_report.pdf




 append :: xs::LL<n> -> ys::LL<m> --> res::LL<r> & R(n,m,r)
 
 // verification
  n=0 /\ r=m -> R(n,m,r)
  /\ n>0 /\ R(n-1,m,r1) /\ r=1+r1 -> R(n,m,r)
  
  R(n,m,r) -> r=n+m
 
 
 infer[R,n,m] ..... |- ....

Ind inv stp = 
  \x xs b b' -> 
      inv xs b => (stp x b b'  => inv (x:xs) b')
      inv xs b /\ stp x b b'  => inv (x:xs) b'
              
  (inv xs b => stp x b b') /\ (inv xs b => inv (x:xs) b')
			   
foldr :: (Ind inv stp) =>
  (x:a -> b:b -> {b':b:stp x b b'})
  -> {b:b|inv [] b} -> xs:[a] -> {v:b|inv xs v}
foldr f z xs = case
  xs of [] -> z
       x:xs -> f x (foldr f z xs)

(i) write pre/post withn 2nd-order unknown
(ii) verifier collects relational assumption
(iii) normalization + simplification
(iv) fixpoint 	   
CAV2014 - shape analysis
	Quang Loc Le, Cristian Gherghina, Shengchao Qin, Wei-Ngan Chin:
Shape Analysis via Second-Order Bi-Abduction. CAV 2014: 52-68


APLAS2013 
Minh-Thai Trinh, Quang Loc Le, Cristina David, Wei-Ngan Chin:
Bi-Abduction with Pure Properties for Specification Inference. APLAS 2013: 107-123


======================================
let rec foldr op b ys = 
(*@
given (inv: list->int->bool)
requires
  inv([],b) &
  op(arg1:int,arg2:int) |= 
    Given (xs:list) (xs':list), 
      { xs::Cons(arg1,xs') & inv(xs',arg2) } *->:r 
      { inv(xs,r) }
ensures[res] inv(ys,res)
@*)
match ys with
| [] -> b
| y::ys -> op y (foldr op b ys)

	   
	   D1 x xs
	   D2 y
	   
	   CAV2014,APLAS13 shape analysis (relational assumptuon)
	   
	   length xs = case xs of 
	      [] ->  0
		  x:xs -> 1+ length xs
		  
		xs::LL<>
		
	   
- can this spec be automatically verified?
- can this spec be automatically inferred?
- can be spec be improved by pre-condition?

  q x y => p y z => r x z
  
  q x y /\ p y z => r x z
  
  (a => b) => c
  a => (b => c)

  a /\ b => c
  

  
Chain p q r = \x y z -> 
    /\ q x y /\ p y z => r x z
compose::(Chain p q r) =>
  (y:b -> {z:c|p y z})
  -> (x:b -> {z:c|q x z})
  -> (x:b -> {z:c|r x z})
		   
*)
