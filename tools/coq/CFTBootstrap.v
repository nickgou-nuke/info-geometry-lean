From Stdlib Require Import Reals.
Open Scope R_scope.

Lemma cft_bootstrap_inv : forall t : R, t <> 0 -> -1 / (-1 / t) = t.
Proof.
  intros t H.
  field.
  exact H.
Qed.
