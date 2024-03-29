Load ast.

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
| None =>
  match ins2 with
  | None => true
  | Some ins2In => false
  end
| Some ins1In =>
  (match ins2 with
   | None => false
   | Some ins2In => instanceEntail ins1In ins2In
  end)
end.

Definition controdictStatus (s1 s2: signalState): bool :=
match (s1, s2) with
| (zero, one)   => true
| (undef, one)  => true
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


Local Open Scope nat_scope.

Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | 0  , _   => true
  | _  , 0   => false
  | S n, S m => leb n m
  end.

Fixpoint geb (n m : nat) : bool :=
  match n, m with
  | _  , 0   => true
  | 0  , _   => false
  | S n, S m => geb n m
  end.

Compute (geb 3 4).

Definition greaterThan (n m: nat) : bool  :=
  match (leb n m) with
  | true => false
  | false=> true
  end.

Definition natEq (n m: nat) : bool  :=
 leb n m && leb m n.


Definition max_k (k1 k2: nat) : nat :=
if greaterThan k1 k2 then k1 else k2.



Program Fixpoint normalIn (eff:syncEff) (n:nat) {measure n} :syncEff :=
match n with
| O => eff
| S n' =>
  (match eff with
   | bot          => eff
   | emp          => eff
   | singleton ins=> if controdict ins then bot else singleton (remove_dup ins)
   | waiting   _  => eff
   | cons bot  _  => bot
   | cons emp e   => normalIn e n'
   | cons e emp   => normalIn e n'
   | cons e1 e2   => normalIn (cons (normalIn e1 n') (normalIn e2 n')) n'
   | disj bot e   => normalIn e n'
   | disj e bot   => normalIn e n'
   | disj e1 e2   => normalIn (disj (normalIn e1 n') (normalIn e2 n')) n'
   | parEff bot _ => bot
   | parEff _ bot => bot
   | parEff e1 e2 => normalIn (parEff (normalIn e1 n') (normalIn e2 n')) n'
   | kleene emp   => emp
   | kleene e     => normalIn (kleene (normalIn e n')) n'
   end)
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




Definition normal (effIn:syncEff) : syncEff :=
  normalIn effIn 6
.



Fixpoint string_of_effects (eff:syncEff) : string :=
match eff with
| bot          => "_|_"
| emp          => "ϵ"
| singleton ins=> string_of_instance ins
| waiting   s  => s ++ "?"
| cons e1 e2   =>  string_of_effects e1 ++ "." ++ string_of_effects e2
| disj e1 e2   =>  "(" ++ string_of_effects e1 ++ "\/" ++ string_of_effects e2 ++ ")"
| parEff e1 e2 =>  "(" ++ string_of_effects e1 ++ "||" ++ string_of_effects e2 ++ ")"
| kleene e     =>  "(" ++ string_of_effects e ++ ")^*"
end.

Definition string_of_instance1 (cur: option instance) : string :=
match cur with
| None => "None"
| Some ins =>  string_of_effects (singleton ins)
end.


Definition string_of_nat (n:nat) : string :=
match n with
| 0 => "0"
| 1 => "1"
| 2 => "2"
| 3 => "3"
| 4 => "4"
| _ => "other number"
end.

Definition instanceToEff (cur: option instance) : syncEff :=
match cur with
| None => emp
| Some ins => singleton ins
end.






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
| waiting   s  => [[]] (*[[(s, one)]] ++ [[(s, zero)]]*)
| disj e1 e2   => fst e1 ++ fst e2
| cons e1 e2   => if nullable e1 then fst e1 ++ fst e2
                  else fst e1
| parEff e1 e2 => let f1 := fst e1 in
                  let f2 := fst e2 in
                  List.flat_map (fun f1In => List.map (fun f2In => List.app f1In f2In) f2) f1
| kleene e     => fst e
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



Compute (fst (kleene (singleton [("S", one)]))).
Compute (normal (derivitive (kleene (singleton [("S", one)])) [("K", one)])).


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


Definition leftHy  (records :list instance) : nat :=
numEvent * numEvent - (List.length records).


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
            else (fixpoint (List.app (records) [merge]) der1 der2)
         ) zipFst in
     normal (List.fold_left (fun acc a => disj acc a) effList bot)
  end)
end.

Next Obligation.
Proof.
Admitted.


Compute (max_k 1 2).

Compute (max_k 10 5).

Compute (natEq 4 4).




Definition mergeCurrentToEff (c: option instance) (eff:syncEff): syncEff :=
match c with
| None => eff
| Some i =>
  let fix mergeAux eFF: (syncEff*bool) :=
      (match  eFF with
      | bot => (bot, true)
      | emp => (emp, false)
      | singleton i2 => (singleton (List.app i i2), true)
      | waiting s => if instanceEntail i ([(s, one)]) then ((singleton i), true) else (cons (singleton i) (waiting s), true)
      | cons e1 e2 =>
        match mergeAux e1 with
        | (eIn, true) => (cons eIn e2, true)
        | (eIn, false) => let (a, b) := (mergeAux e2) in (cons e1 a, b)
        end
      | disj e1 e2 =>
        let (e11, re1) := mergeAux e1 in
        let (e22, re2) := mergeAux e2 in
        (disj e11 e22, re1 || re2)
      | parEff e1 e2 =>
        let (e11, re1) := mergeAux e1 in
        let (e22, re2) := mergeAux e2 in
        (parEff e11 e22, re1 && re2)
      | kleene e =>
        let (eIn, re) := mergeAux e in
        match re with
        | true => (cons eIn eff, true)
        | flase => (cons eff (singleton i), true)
        end
      end) in
  let (final, re):=  mergeAux eff in if re then final else cons eff ((singleton i))
end.




Definition mergeCurrent (c1 c2: option instance) : option instance :=
match c1, c2 with
| None, None => None
| Some i1, None => c1
| None, _ => c2
| Some i1, Some i2 => Some (List.app i1 i2)
end.



Program Fixpoint fixpointState (records :list instance) (s1 s2:state) {measure (leftHy records)} : states :=
let '(eff1, cur1, k1) := s1 in
let '(eff2, cur2, k2) := s2 in
let f1s:  list instance := fst eff1 in
let f2s: list instance := fst eff2 in
match normal eff1, normal eff2 with
| emp, emp => [(recordsToEff records, mergeCurrent cur1 cur2, max_k k1 k2)]
| emp, _   =>
  if greaterThan k1 0
  then List.map (fun (f:instance) =>
                   (recordsToEff records, mergeCurrent cur1 (Some f), k1)) f2s
  else [(cons (recordsToEff records) (mergeCurrentToEff cur1 eff2), cur2, k2)]
| _, emp   =>
  if greaterThan k2 0
  then List.map (fun (f:instance) =>
                   (recordsToEff records, mergeCurrent cur2 (Some f), k2)) f1s
  else [(cons (recordsToEff records) (mergeCurrentToEff cur2 eff1), cur1, k1)]
| _,_      =>
     let zipFst := zip_list f1s f2s in
     List.flat_map (fun (pair: (instance * instance )) =>
          let (f1, f2):=pair in
          let merge := (List.app f1 f2) in
          if controdict merge then []
          else
            let der1 := if Nat.eqb (List.length f1) 0 then (normal (derivitive eff1 merge)) else  (normal (derivitive eff1 f1)) in 
            let der2 := if Nat.eqb (List.length f2) 0 then (normal (derivitive eff2 merge))  else (normal (derivitive eff2 f2)) in
            if (reoccur records merge) then [(formloop records merge, None, max_k k1 k2)]
            else (fixpointState (List.app records [merge]) (der1, cur1, k1) (der2, cur2, k2))
     ) zipFst
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


Compute (fixpointState [] (ϵ, Some [("A", one)] , 0) (waiting "A", None,0)).


Compute (fixpointState [] (cons (singleton [("C", one);("E", undef)]) (singleton []), Some [], 0) (waiting "C", Some [], 0)).



Definition normalCurrent (c: option instance) : option instance :=
match c with
| None => None
| Some ins => Some (remove_dup ins)
end.


Definition parallelMergeState (states1 states2: states) : states :=
let mix_states   := zip_list states1 states2 in
let temp := List.flat_map (fun (pair:(state * state)) =>
                             let (s1, s2) := pair in fixpointState [] s1 s2) mix_states in
List.map (fun (tuple:state) =>
            let '(his, cur, k):= tuple in
            (normal his, normalCurrent cur, k)) temp.



Definition state_to_eff (s:state) : syncEff :=
let '(his, cur, k) := s in
if greaterThan k 0 then normal (cons (normal his) (instanceToEff cur))
else normal (cons (normal his) (instanceToEff cur)).


Definition states_to_eff (states:states) : syncEff :=
normal (List.fold_left (fun acc a => disj acc (state_to_eff a)) states bot).



Definition string_of_state (state: state) : string:=
let '(his, cur, k) := state in
string_of_effects (state_to_eff state) ++ " with exit code ("++ string_of_nat k ++")   ".



Definition string_of_states (states: states) : string:=
List.fold_left (fun acc a => acc ++ "" ++ string_of_state a) states "".



(*
Definition parallelMergeState' (states1 states2: states) : states :=
let mix_states   := zip_list states1 states2 in
List.flat_map
   (fun (pair:(state * state)) =>
      let (s1, s2) := pair in
      let eff1 := states_to_eff s1 in
      let eff2 := states_to_eff s2 in
      let merged := fixpoint [] eff1 eff2 in
      effectsToState merged) mix_states.
*)

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
    | (name, status) :: xs => if eqb name name' && ((*compareStatus status status' ||*) compareStatus status undef)
                              then ss :: xs
                              else (name, status) :: (aux xs)
    end
in
match cur with
| None => Some (aux (initalCur env))
| Some insIn => Some (aux insIn)
end.


Definition extendCur (env:envenvironment) (cur: option instance) (ss:signal_status): option instance :=
  match cur with
  | None => Some (ss:: initalCur env)
  | Some insIn => Some (ss:: insIn)
  end.

Compute (setSigInCur ["A";"B";"C"] (setSigInCur ["A";"B";"C"] None ("A", one)) ("A", one)).


(*Definition appendSigInCur (env:envenvironment) (cur: option instance) (ss:signal_status): option instance :=
match cur with
| None => (Some (ss :: initalCur env))
| Some insIn => (Some (ss :: insIn))
end.
*)

Require Import PeanoNat.

Local Open Scope nat_scope.

(*
Suspension by suspend is delayed, just as abortion by abort: in the starting instant, the presence of the suspension signal is not tested for and the body is run anyway.
*)
Definition approxSuspension (env:envenvironment) (eff: syncEff) (s:string) (cur: option instance):  syncEff :=
let additon :=  disj emp (cons (waiting s) (singleton (initalCur env))) in
let tail :=
    match cur with
    | None => emp
    | Some _ => additon
    end in
let fix helper (effIn : syncEff) : syncEff :=
    match effIn with
    | bot          => bot
    | emp          => emp
    | singleton ins=> eff
    | waiting   s  => eff
    | cons e1 e2   => cons (helper e1) (cons additon (helper e2))
    | disj e1 e2   => disj (helper e1) (helper e2)
    | parEff e1 e2 => parEff (helper e1) (helper e2)
    | kleene e     => kleene (helper e)
    end in
cons (helper eff) tail.




