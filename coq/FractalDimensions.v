From Coq Require Import Reals.
From Coq Require Import Lra.
From Coq Require Import Rpower.

Open Scope R_scope.

Section FractalDimensions.

Variable UpperPhi LowerPhi : R.
Hypothesis UpperPhi_pos : UpperPhi > 0.
Hypothesis UpperPhi_eq_one_add_LowerPhi : UpperPhi = 1 + LowerPhi.
Hypothesis UpperPhi_mul_LowerPhi : UpperPhi * LowerPhi = 1.

Lemma UpperPhi_sub_LowerPhi : UpperPhi - LowerPhi = 1.
Proof.
  lra.
Qed.

(* The exact transfinite relation: UpperPhi^5 - LowerPhi^5 = 11. *)
Theorem UpperPhi_fifth_minus_LowerPhi_fifth :
  UpperPhi ^ 5 - LowerPhi ^ 5 = 11.
Proof.
  assert (H_factor : UpperPhi ^ 5 - LowerPhi ^ 5 =
    (UpperPhi - LowerPhi) ^ 5 +
    5 * (UpperPhi * LowerPhi) * (UpperPhi - LowerPhi) ^ 3 +
    5 * (UpperPhi * LowerPhi) ^ 2 * (UpperPhi - LowerPhi)) by ring.
  assert (H_sub : UpperPhi - LowerPhi = 1) by apply UpperPhi_sub_LowerPhi.
  assert (H_mul : UpperPhi * LowerPhi = 1) by apply UpperPhi_mul_LowerPhi.
  rewrite H_factor.
  rewrite H_sub.
  rewrite H_mul.
  ring.
Qed.

(* Transfinite dimension of spacetime at stage n: D(n) = 10 * UpperPhi^(n - 6). *)
Definition D (n : Z) : R := 10 * Rpower UpperPhi (IZR n - 6).

(* Theorem: The sequence scales by UpperPhi: D(n+1) = UpperPhi * D(n). *)
Theorem D_scaling (n : Z) :
  D (n + 1) = UpperPhi * D n.
Proof.
  unfold D.
  assert (H_add : IZR (n + 1) - 6 = (IZR n - 6) + 1).
  { rewrite plus_IZR. lra. }
  rewrite H_add.
  rewrite Rpower_plus.
  rewrite Rpower_1.
  ring.
  all: exact UpperPhi_pos.
Qed.

Definition D_E8 : nat := 248.
Definition D_E8E8 : nat := 496.

Theorem E8_E8_dim_eq_double : D_E8E8 = (2 * D_E8)%nat.
Proof.
  reflexivity.
Qed.

End FractalDimensions.
