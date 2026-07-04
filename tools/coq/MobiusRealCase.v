From Stdlib Require Import Reals.
From Stdlib Require Import Psatz.
Local Open Scope R_scope.

Lemma trace_sq_nonneg : forall a d : R, 0 <= (a + d)^2.
Proof.
  intros a d.
  generalize (a + d); intro x.
  nra.
Qed.
