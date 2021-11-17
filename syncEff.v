From Coq Require Import Arith Bool Ascii String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(* the default value of a siganl is absent *)
Inductive signalState : Type := zero | one.

Definition signal_status : Type :=  (string * signalState).

Definition instance : Type :=  (list signal_status).

Definition string_of_signal_status (pair:signal_status) : string :=
let (name, status) := pair in
(match status with
| zero => "!"
| one  => ""
end) ++  name.

Definition string_of_instance (ins: instance): string :=
"{" ++
(
let fix helper (li:instance) : string :=
match li with
| [] => ""
| [x]  => string_of_signal_status x
| x::xs =>  string_of_signal_status x ++ "," ++ helper xs
end in
helper ins
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
| waiting   s  => [[(s, one)]] ++ [[(s, zero)]]
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
| (zero, zero)   => true
| (one, one) => true
| _                  => false
end.

Fixpoint instanceEntail (ins1 ins2 : instance): bool :=
  let fix exist (sig:signal_status) (ins:instance) : bool :=
     let (name, status) := sig in
     match ins with
     | [] => false
     | (name', status') :: xs => if eqb name name' && compareStatus status status'
                                 then true else exist sig xs
     end in
  match ins2 with
  | [] => true
  | y :: ys => if exist y ins1 then instanceEntail ins1 ys else false
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
| waiting   s  => if instanceEntail ([(s, one)]) f then emp else waiting s
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
1000 - (List.length records).

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
     let effList :=
         List.map (fun (pair: (instance * instance )) =>
            let (f1, f2):=pair in
            let merge := (List.app f1 f2) in
            let der1 := (normal (derivitive eff1 f1)) in
            let der2 := (normal (derivitive eff2 f2)) in
            if (reoccur records merge) then formloop records merge
            else (fixpoint (merge :: records) der1 der2)
         ) zipFst in
     normal (List.fold_left (fun acc a => disj acc a) effList bot)
  end)
end.

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

Definition mergeCurrent (c: option instance) (eff:syncEff): syncEff :=
match c with
| None => eff
| Some i =>
  let fst := fst eff in
  let effList := List.map (fun f => cons (singleton (List.app f i)) (derivitive eff f)) fst in
  normal (List.fold_left (fun acc a => disj acc a) effList bot)
end.


Program Fixpoint fixpointState (records :list instance) (s1 s2:state) {measure (leftHy records)} : states :=
let '(eff1, cur1, k1) := s1 in
let '(eff2, cur2, k2) := s2 in
let f1s := fst eff1 in
let f2s := fst eff2 in
match normal eff1 with
| emp => [(cons (recordsToEff records) (mergeCurrent cur1 eff2), cur2, k2)]
| _   =>
  (match normal eff2 with
   | emp => [(cons (recordsToEff records) (mergeCurrent cur2 eff1),  cur1, k1)]
   | _ =>
     let zipFst := zip_list f1s f2s in
     List.flat_map (fun (pair: (instance * instance )) =>
                      let (f1, f2):=pair in
                      let merge := (List.app f1 f2) in
                      let der1 := (normal (derivitive eff1 f1)) in
                      let der2 := (normal (derivitive eff2 f2)) in
                      if (reoccur records merge) then [(formloop records merge, None, max_k k1 k2)]
                      else (fixpointState (merge :: records) (der1, cur1, k1) (der2, cur2, k2))
                   ) zipFst
   end)
end.


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


Definition appendCurrent (cur: option instance) (i:signal_status): option instance :=
match cur with
| None => Some [i]
| Some ins => Some (List.app ins [i])
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



Fixpoint forward (env:envenvironment) (s:states) (expr:expression) : states :=
List.flat_map (fun (pair:state) =>
  let '(his, cur, k) := pair in
  (*
    if greaterThan k 0 then [pair]
  else
   *)
  match expr with
  | nothingE        => [pair]
  | pauseE          => [(cons his (instanceToEff cur), Some [], k)]
  | raiseE n      => [(his, cur, S k)]
  | emitE str       => [(his, appendCurrent cur (str, one), k)]
  | localDelE str e => let newEnv   := (str)::env in
                       forward newEnv [pair] e
  | seqE e1 e2      => let s1 := (forward env [pair] e1) in
                       List.flat_map
                         (fun (pairE:state)  =>
                            let '(hisE, curE, kE) := pairE in
                            if greaterThan k 0 then [pairE]
                            else forward env [pairE] e2) s1
  | parE e1 e2      => let s1 := (forward env [pair] e1) in
                       let s2 := (forward env [pair] e2) in
                       parallelMergeState s1 s2
  | ifElseE s e1 e2 => if instanceEntailShell cur (Some [(s, one)])
                       then forward env [pair] e1
                       else forward env [pair] e2
  | asyncE e str    => let s1 := (forward env [pair] e) in
                       List.map (fun (pairE:state) =>
                                   let '(hisE, curE, kE) := pairE in
                                   (hisE, appendCurrent curE (str, one), kE)) s1
  | awaitE s        => [(cons his (cons (instanceToEff cur) (waiting s)), Some [], k)]
  | suspendE e str  => let s1 := (forward env [(emp, cur, k)] e) in
                       List.map (fun (pairE:state) =>
                                   let '(hisE, curE, kE) := pairE in
                                   let newhis := cons his (extendEff hisE (str, zero)) in
                                   let newCur := appendCurrent curE (str, zero) in
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
| cons e1 e2   => string_of_effects e1 ++ "." ++ string_of_effects e2
| disj e1 e2   => string_of_effects e1 ++ "\/" ++ string_of_effects e2
| parEff e1 e2 => string_of_effects e1 ++ "||" ++ string_of_effects e2
| kleene e     =>  "(" ++ string_of_effects e ++ ")^*"
end.

Definition state_to_eff (s:state) : syncEff :=
let '(his, cur, k) := s in
if greaterThan k 0 then bot 
else normal (cons his (instanceToEff cur)).

Definition states_to_eff (states:states) : syncEff :=
normal (List.fold_left (fun acc a => disj acc (state_to_eff a)) states bot).

Definition forward_Shell (expr:expression) : string :=
  string_of_effects(
      states_to_eff(
          forward [] [(emp, None, 0)] expr)).


Definition testSeq : expression :=
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


Definition testAsync : expression :=
  async testSeq with "S".

Definition testPal : expression :=
  fork testSeq1  par (emit "H").

Compute (forward_Shell testPal).


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
