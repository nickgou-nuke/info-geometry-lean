From Stdlib Require Import Reals.
Open Scope R_scope.

Theorem reflection_invariance :
  forall b a : R,
  b <> 0 ->
  let Q := b + 1/b in
  a * (Q - a) = (Q - a) * (Q - (Q - a)).
Proof.
  intros b a Hb Q.
  subst Q.
  ring.
Qed.
