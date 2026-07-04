From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

Theorem super_virasoro_ns_vacuum_limit :
  forall r : R, r * r - 1 / 4 = 0 <-> r = 1 / 2 \/ r = - (1 / 2).
Proof.
  intros r.
  split.
  - intros H.
    assert (H1: (r - 1/2) * (r + 1/2) = 0).
    { nra. }
    apply Rmult_integral in H1.
    destruct H1 as [H1 | H1].
    + left; lra.
    + right; lra.
  - intros [H | H]; rewrite H; lra.
Qed.
