Load util.


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
  | raiseE n        => [(his, cur, (*Nat.add k*) n)]
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
  | ifElseE s e1 e2 => (*if instanceEntailShell cur (Some [(s, one)])
                       then forward env [pair] e1
                       else forward env [pair] e2
                       *)
                       let s1 := (forward env [(his, extendCur env cur (s, one), k)] e1) in
                       let s2 := (forward env [(his, extendCur env cur (s,zero), k)] e2) in
                       List.app s1 s2
  | asyncE e str    => let s1 := (forward env [pair] e) in
                       List.map (fun (pairE:state) =>
                                   let '(hisE, curE, kE) := pairE in
                                   (hisE, setSigInCur env curE (str, one), kE)) s1
  | awaitE s        => [(cons his (cons (instanceToEff cur) (waiting s)), None, k)]
(*  | suspendE e str  => let s1 := (forward env [(emp, cur, k)] e) in
                       List.map (fun (pairE:state) =>
                                   let '(hisE, curE, kE) := pairE in
                                   let newhis := cons his (approxSuspension env hisE str) in
                                   let newCur := curE(*setSigInCur env curE (str, zero)*) in
                                   (newhis, newCur, kE)) s1
*)
  | trycatchE e h => let s1 := (forward env [pair] e) in
                       List.flat_map
                         (fun (pairE:state) =>
                            let '(hisE, curE, kE) := pairE in
                            if  natEq kE 0 then  [pairE]
                            else if  natEq kE 1 then (forward env [(hisE, curE, 0)] h)
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





Definition env := ["A"; "B"; "C"; "D"; "E"; "F" ].

Definition env1 := ["C"].


Definition forward_Shell (expr:expression) : string :=
 (* string_of_effects(
      states_to_eff*)
 string_of_states (forward env [(emp, None, 0)] expr)
(*)*).


Definition testSeq : expression :=
  emit "B";
  emit "A";
  emit "B";
  pause;
  emit "C";
  pause;
  emit "D".

Compute (forward_Shell testSeq). (* "{A,B}.{C}.{D} with exit code (0)   " *)

Definition testSeq1 : expression :=
  emit "A";
  emit "B";
  pause;
  emit "C";
  pause;
  emit "D";
  pause.

Compute (forward_Shell testSeq1). (* "{A,B}.{C}.{D}.{} with exit code (0)   " *)

Definition testSeq2 : expression :=
  pause;
  emit "A";
  emit "B";
  pause;
  emit "C";
  pause;
  emit "D";
  pause.

Compute (forward_Shell testSeq2). (* "{A,B}.{C}.{D}.{} with exit code (0)   " *)

Definition testSeq3 : expression :=
  pause;
  emit "A";
  emit "B";
  pause;
  emit "C";
  pause;
  emit "D".

Compute (forward_Shell testSeq3). (* "{A,B}.{C}.{D} with exit code (0)   " *)


Definition testRaise : expression :=
  raise 2.

Compute (2-1).

Compute (forward_Shell testRaise). (* "ϵ with exit code (2)   " *)


Definition testTry : expression :=
  trap testRaise catchwith testSeq.



Compute (forward_Shell testTry). (* "ϵ with exit code (1)   " *)


Definition testTry1 : expression :=
  trap testTry catchwith testSeq.

Compute (forward_Shell testTry1). (* "{A,B}.{C}.{D} with exit code (0)   " *)



Definition testPresent : expression :=
  present "A" then testSeq else (emit "A").

Compute (forward_Shell testPresent). (* "{A,B}.{C}.{D} with exit code (0)   _|_ with exit code (0)    " *)


Definition testPresent4 : expression :=
  present "A" then testSeq else (emit "B").

Compute (forward_Shell testPresent4). (* "{A,B}.{C}.{D} with exit code (0)   {B} with exit code (0)   " *)


Definition testPresent3 : expression :=
  emit "A" ; present "A" then testSeq else (emit "B").

Compute (forward_Shell testPresent3). (* "{A,B}.{C}.{D} with exit code (0)   _|_ with exit code (0)    " *)


Definition testPresent1 : expression :=
  emit "A"; present "A" then testSeq else (emit "B").

Compute (forward_Shell testPresent1). (* "{A,B}.{C}.{D} with exit code (0)  " *)

Definition testPresent2 : expression :=
  present "A" then emit "B" else emit "C".
Compute (forward_Shell testPresent2). (*"{C} with exit code (3)   "*)


Definition testLoop : expression :=
  loop testSeq.

Compute (forward_Shell testLoop). (* "{A,B}.{C}.({A,B,D}.{C})^* with exit code (0)   " *)

Definition testLoop1 : expression :=
  (loop testSeq1).

Compute (forward_Shell testLoop1). (* "{A,B}.{C}.{D}.({A,B}.{C}.{D})^* with exit code (0)   "*)

Definition testLoop2 : expression :=
  (loop (emit "A"; pause; pause)).

Compute (forward_Shell testLoop2). (*"{A}.{}.({A}.{})^* with exit code (0)   " *)


Definition testPause : expression :=
  pause; pause; emit "B".

Compute (forward_Shell testPause). (*"{}.{B} with exit code (0)   " *)


Definition testAsync : expression :=
  async testSeq with "S".
Compute (forward_Shell testAsync). (*"{A,B}.{C}.{D,S} with exit code (0)   " *)


Definition testPal : expression :=
  fork (emit "A";pause) par (await "A").
Compute (forward_Shell testPal). (*"{A}.{} with exit code (0)   "*)


Definition testPal_ : expression :=
  fork (emit "A";pause) par (emit "B").
Compute (forward_Shell testPal_). (*"{A, B}.{} with exit code (0)   "*)


Definition testPal1 : expression :=
  fork (testPause) par (fork testAsync  par (emit "A"; emit "B")).
Compute (forward_Shell testPal1). (*"{A,B}.{B,C}.{D,S} with exit code (0)   "*)


Definition testPal2 : expression :=
   fork (emit "C") par (await "C").
Compute (forward_Shell testPal2). (*"{C} with exit code (0)   "*)

Definition testPal3 : expression :=
   fork (emit "C";pause;emit"D") par (await "E").
Compute (forward_Shell testPal3). (*"{C}.{D}.E?  with exit code (0)   "*)


Definition testAsyncSeq : expression :=
  async testSeq with "E".
Compute (forward_Shell testAsyncSeq). (*"{A,B}.{C}.{D,E} with exit code (0)   "*)



Definition testAsyncSeq1 : expression :=
  fork (async testSeq with "E") par (await "F") .
Compute (forward_Shell testAsyncSeq1). (*"{A,B}.{C}.{D,E}.F? with exit code (0)   "*)



Definition testPal0 : expression :=
  fork testSeq  par (await "C").

Compute (forward_Shell testPal0). (*"{A,B}.{C}.{D} with exit code (0)   "*)



Definition testPal4 : expression :=
   fork (emit "C";pause;emit"D"; raise 3) par (emit "A"; raise 2).

Compute (forward_Shell testPal4). (*"{A,C} with exit code (2)   "*)


Definition testPal5 : expression :=
   async testSeq with "E"; await "A";await "E";await "D".

Compute (forward_Shell testPal5). (*"{A,B}.{C}.{D,E}.D? with exit code (0)   "*)

Definition testPal6 : expression :=
   fork (emit "C";pause;emit"D"; raise 3) par (emit "A").

Compute (forward_Shell testPal6). (*"{A,C}.{D} with exit code (3)   "*)



(*
Definition testSuspend : expression :=
  suspend testSeq when "S".



Definition testSuspend1 : expression :=
  suspend (emit "A";pause) when "B".

Definition testPal6 : expression :=
  fork testSuspend1  par (emit "B").

Compute (forward_Shell testPresent1).

*)







