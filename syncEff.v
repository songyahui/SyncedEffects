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
| raiseE    (s:string)
| trycatchE (e:expression) (s:string) (handler:expression)
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

Notation "'raise' T" := (raiseE T) (at level 200, right associativity).

Notation "'try' E1 'catch' S 'with' E2" := (trycatchE E1 S E2) (at level 200, right associativity).


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
(*
(* I decided not to care about the undefined status for now *)
| (undef, undef)     => true
*)
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
Definition state : Type := (syncEff * (option instance) * bool).

Definition states : Type := list state.

Fixpoint effectToStates (*cut function *) (eff:syncEff): list (syncEff * (option instance)) :=
match eff with
| bot          => []
| emp          => [(emp, None)]
| singleton i  => [(emp, Some i)]
| waiting   s  => [(eff, Some [])] (* S? = (not S)^*.(S) *)
| disj e1 e2   => List.app (effectToStates e1) (effectToStates e2)
| cons e1 e2   => let ss := effectToStates e2 in
                  List.map (fun (pair:(syncEff * (option instance))) =>
                              let (his, cur) := pair in
                              (cons e1 his, cur)) ss
| kleene e     => let ss := effectToStates e in
                  List.map (fun (pair:(syncEff * (option instance))) =>
                              let (his, cur) := pair in
                              (cons eff his, cur)) ss
| parEff e1 e2 => [] (* this should not be here ... *)
end.

Definition parallelMergeEffects (eff1 eff2: syncEff) : syncEff :=
let f1s := fst eff1 in
    let f2s := fst eff2 in
    let zipFst := zip_list f1s f2s in
    let effList := List.map
                   (fun (pair:(instance * instance )) =>
                         let (f1, f2):=pair in
                         let der1 := (normal (derivitive eff1 f1)) in
                         let der2 := (normal (derivitive eff2 f2)) in
                         let tail := parEff der1 der2 in
                         cons (singleton (List.app f1 f2)) tail) zipFst in
    normal (List.fold_left (fun acc a => disj acc a) effList bot).

Definition instanceToEff (cur: option instance) : syncEff :=
match cur with
| None => emp
| Some ins => singleton ins
end.

Definition parallelMergeState (states1 states2: states) : states :=
let mix_states   := zip_list states1 states2 in
List.flat_map (fun (pair:(state * state)) =>
  let (s1, s2)     := pair in
  let '(eff1, cur1, k1) := s1 in
  let '(eff2, cur2, k2) := s2 in
  let fulltraces : syncEff :=
    let trace1 := normal (cons eff1 (instanceToEff cur1)) in
    let trace2 := normal (cons eff2 (instanceToEff cur2)) in
    parallelMergeEffects eff1 eff2
  in
  List.map (fun (p:((syncEff * (option instance)))) =>
              let (his, cur) := p in
              if (Bool.eqb k1 false) || (Bool.eqb k2 false) then (his, cur, false) else  (his, cur, true)
           ) (effectToStates (normal fulltraces))

) mix_states.

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
  if Bool.eqb k false then [pair]
  else
  match expr with
  | nothingE        => [pair]
  | pauseE          => [(cons his (instanceToEff cur), Some [], k)]
  | raiseE str      => [(his, appendCurrent cur (str, one), false)]
  | emitE str       => [(his, appendCurrent cur (str, one), k)]
  | localDelE str e => let newEnv   := (str)::env in
                      forward newEnv [pair] e
  | seqE e1 e2      => let s1 := (forward env [pair] e1) in
                      List.flat_map (fun (pairE:state)  =>
                                 let '(hisE, curE, kE) := pairE in
                                 if Bool.eqb kE false then [pairE]
                                 else forward env [pairE] e2 ) s1
  | parE e1 e2      => let s1 := (forward env [pair] e1) in
                      let s2 := (forward env s1 e2) in
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
                                  (cons his (extendEff hisE (str, zero)), appendCurrent curE (str, zero), kE)) s1
  | trycatchE e s h => let s1 := (forward env [pair] e) in
                      List.flat_map (fun (pairE:state) =>
                                  let '(hisE, curE, kE) := pairE in
                                  if (Bool.eqb kE false) && (existRaise s curE)  then
                                    (forward env [(hisE, curE, true)] h)
                                  else  [pairE]) s1
  | loopE e         => let s1 := (forward env [(emp, cur, k)] e) in
                       let newState := (List.map (fun (pairE:state) =>
                                                       let '(_, curE, kE) := pairE in
                                                       (emp, curE, kE)
                                                        ) s1) in 
                       let hisList := (List.map (fun (pairE:state) =>
                                                       let '(hisE, _, _) := pairE in
                                                       hisE) s1) in 
                       let s2 := (forward env newState e) in
                       List.map (fun (pairE:state) =>
                                  let (tuple, hisS1) := pairE in
                                  let '(hisE, curE, kE) := tuple in 
                                  if  Bool.eqb kE false then pairE
                                  else (cons (cons his hisS1) (kleene hisE), None, true)
                                ) (List.combine s2 hisList)
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
let '(his, cur, _) := s in
normal (cons his (instanceToEff cur)).

Definition states_to_eff (states:states) : syncEff :=
normal (List.fold_left (fun acc a => disj acc (state_to_eff a)) states bot).

Definition forward_Shell (expr:expression) : string :=
  string_of_effects(
      states_to_eff(
          forward [] [(emp, None, true)] expr)).


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
  raise "T".

Definition testTry : expression :=
  try testRaise catch "T1" with testSeq.

Definition testTry1 : expression :=
  try testRaise catch "T" with testSeq.


Definition testPresent : expression :=
  present "A" then testSeq else (emit "B").

Definition testLoop : expression :=
  loop testSeq.


Definition testSuspend : expression :=
  suspend testSeq when "S".


Definition testAsync : expression :=
  async testSeq with "S".


Definition testLoop1 : expression :=
  (loop testSeq3).




Compute (forward_Shell testLoop1).

{A, B} .{C}.{D}
{A, B, D} {C}

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
