From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

Theorem sum_roots_eq_sum_poles :
  forall a d c : R,
  c <> 0 ->
  (a - d) / c = (a / c) + (-d / c).
Proof.
  intros a d c Hc.
  unfold Rdiv. unfold Rminus.
  rewrite Rmult_plus_distr_r.
  reflexivity.
Qed.
