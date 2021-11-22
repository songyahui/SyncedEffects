Load ast.


Definition emittion : Type := option string.

Definition programState : Type := (expression * instance * emittion * nat).


Definition microStep (ps:programState) : programState :=
  let '(expr, env, e, k) := ps in
  match expr with
  | nothingE        => ps
  | pauseE          => (nothingE, env, None, 1)
  | emitE s         => (nothingE, env, Some s, 0)
  | localDelE s q   => (nothingE, (s, undef)::env, e, 0)
  | raiseE n        => (nothingE, env, e, k)
  | seqE p q        => 
 
  | _ => ps
  end.

  
