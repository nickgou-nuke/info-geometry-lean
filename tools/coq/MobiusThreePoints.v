From Stdlib Require Import Reals Lra.
Open Scope R_scope.

Definition mobius_cross_ratio (z z1 z2 z3 : R) : R :=
  ((z - z1) * (z2 - z3)) / ((z - z3) * (z2 - z1)).

Lemma mobius_at_z1 :
  forall z1 z2 z3 : R,
    z1 <> z3 ->
    z2 <> z1 ->
    mobius_cross_ratio z1 z1 z2 z3 = 0.
Proof.
  intros z1 z2 z3 H13 H21.
  unfold mobius_cross_ratio.
  assert (z1 - z1 = 0) by lra.
  rewrite H.
  unfold Rdiv.
  rewrite Rmult_0_l.
  rewrite Rmult_0_l.
  reflexivity.
Qed.

Lemma mobius_at_z2 :
  forall z1 z2 z3 : R,
    z2 <> z3 ->
    z2 <> z1 ->
    mobius_cross_ratio z2 z1 z2 z3 = 1.
Proof.
  intros z1 z2 z3 H23 H21.
  unfold mobius_cross_ratio.
  unfold Rdiv.
  assert ((z2 - z1) * (z2 - z3) = (z2 - z3) * (z2 - z1)) by ring.
  rewrite H.
  apply Rinv_r.
  apply Rmult_integral_contrapositive.
  split; lra.
Qed.
