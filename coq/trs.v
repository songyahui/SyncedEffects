Load util.

Definition hypothesis : Type := list (syncEff * syncEff).

(*returns a set of hypothesis and the entailment validility*)
Definition result : Type := (hypothesis * bool).

Definition neg (v:bool): bool :=
match v with
| true => false
| false => true
end.

Definition leftHy'  (records : hypothesis) : nat :=
numEvent * numEvent - (List.length records).

Fixpoint compareEff (eff1 eff2: syncEff): bool :=
match eff1, eff2 with
| emp, emp => true
| _,_ => false
end.

Fixpoint reoccurTRS (hy:hypothesis) (lhs rhs: syncEff) : bool :=
match hy with
| [] => false
| (lhs', rhs')::xs => if compareEff lhs lhs' &&  compareEff rhs rhs' then true else reoccurTRS xs lhs rhs
end.

Program Fixpoint entailment (hy:hypothesis) (lhs rhs: syncEff) {measure (leftHy' hy)}: bool :=
  if nullable lhs && neg (nullable rhs) then false
  else if reoccurTRS hy lhs rhs then true
  else
    let fst := fst lhs in
    let subTrees := List.map (fun f =>
        let der1 := normal (derivitive lhs f) in
        let der2 := normal (derivitive rhs f) in
        entailment ((lhs, rhs) :: hy) der1 der2
        ) fst in
    List.fold_left (fun acc a => acc && a) subTrees true
.

Next Obligation. Proof. Admitted.


Definition entailmentShell (lhs rhs: syncEff) : bool :=
  entailment [] lhs rhs.

Definition eff1 : syncEff := emp.
Definition eff2 : syncEff := {{[("A", one)]}}.
Definition eff3 : syncEff := waiting "A".


A? |- {A}

Compute (entailmentShell eff3 eff).

