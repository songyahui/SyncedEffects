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
| bot, bot => true
| emp, emp => true
| singleton i1, singleton i2 => if instanceEntail i1 i2 && instanceEntail i2 i1 then true else false
| waiting   s1, waiting   s2 => eqb s1 s2
| cons e1 e2, cons e3 e4 => compareEff e1 e3 && compareEff e2 e4
| disj e1 e2, disj e3 e4 => (compareEff e1 e3 && compareEff e2 e4) ||
                            (compareEff e1 e4 && compareEff e2 e3)
| parEff e1 e2, parEff e3 e4 => (compareEff e1 e3 && compareEff e2 e4) ||
                            (compareEff e1 e4 && compareEff e2 e3)
| kleene e1, kleene e2 => compareEff e1 e2
| _,_ => false
end.

Fixpoint reoccurTRS (hy:hypothesis) (lhs rhs: syncEff) : bool :=
match hy with
| [] => false
| (lhs', rhs')::xs => if compareEff (normal lhs) (normal lhs') &&  compareEff (normal rhs) (normal rhs') then true else reoccurTRS xs lhs rhs
end.

Fixpoint fstTRS (eff:syncEff): list instance  :=
match eff with
| bot          => []
| emp          => []
| singleton i  => [i]
| waiting   s  => [[(s, one)]] ++ [[(s, zero)]]
| disj e1 e2   => fstTRS e1 ++ fstTRS e2
| cons e1 e2   => if nullable e1 then fstTRS e1 ++ fstTRS e2
                  else fstTRS e1
| parEff e1 e2 => let f1 := fstTRS e1 in
                  let f2 := fstTRS e2 in
                  List.flat_map (fun f1In => List.map (fun f2In => List.app f1In f2In) f2) f1
| kleene e     => fstTRS e
end.

Program Fixpoint entailment (hy:hypothesis) (lhs rhs: syncEff) {measure (leftHy' hy)}: bool :=
  if nullable lhs && neg (nullable rhs) then false
  else if reoccurTRS hy lhs rhs then true
  else
    let fst := fstTRS lhs in
    let subTrees := List.map (fun f =>
        let der1 := normal (derivitive lhs f) in
        let der2 := normal (derivitive rhs f) in
        entailment ((lhs, rhs) :: hy) der1 der2
        ) fst in
    List.fold_left (fun acc a => acc && a) subTrees true
.


Next Obligation. Admitted.


Definition entailmentShell (lhs rhs: syncEff) : bool :=
  entailment [] lhs rhs.

Definition eff1 : syncEff := emp.
Definition eff2 : syncEff := {{[("A", one)]}}.
Definition eff3 : syncEff := waiting "A".

Compute (entailmentShell eff3 eff2).

Compute (entailmentShell eff2 eff3).


Compute (entailmentShell (kleene eff2) (kleene eff2)).



