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
  | raiseE n        => [(his, cur, Nat.add k n)]
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
                       let s1 := (forward env [(his, setSigInCur env cur (s, one), k)] e1) in
                       let s2 := (forward env [(his, setSigInCur env cur (s,zero), k)] e2) in
                       let zipStates := zip_list s1 s2 in 
                       List.map (fun (pair: (state * state)) => let (a, b) := pair in normal (disj a b)) zipStates
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


Definition testLoop1 : expression :=
  (loop testSeq).

Definition testLoop2 : expression :=
  (loop (emit "A"; pause; pause)).



Definition testPause : expression :=
  pause; pause; emit "P".

Definition testAsync : expression :=
  async testSeq with "S".


Definition testPal : expression :=
  fork (emit "A";pause) par (await "A").

Definition testPal1 : expression :=
  fork (testPause) par (fork testAsync  par (emit "H")).

Definition testPal2 : expression :=
   fork (emit "C") par (await "C").

Definition testPal3 : expression :=
   fork (emit "C";pause;emit"D") par (await "E").

Definition testAsyncSeq : expression :=
  async testSeq with "E".

Definition testAsyncSeq1 : expression :=
  fork (async testSeq with "E") par (await "F") .


Definition testPal0 : expression :=
  fork testSeq  par (await "C").


Definition testPal4 : expression :=
   fork (emit "C";pause;emit"D"; raise 3) par (emit "A"; raise 2).


Definition testPal5 : expression :=
   async testSeq with "E"; await "C";await "E";await "D".

Definition testPresent1 : expression :=
  present "A" then emit "B" else emit "C".


(*
Definition testSuspend : expression :=
  suspend testSeq when "S".



Definition testSuspend1 : expression :=
  suspend (emit "A";pause) when "B".

Definition testPal6 : expression :=
  fork testSuspend1  par (emit "B").
*)


Compute (forward_Shell testPresent1).





