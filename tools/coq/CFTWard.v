From Stdlib Require Import Reals.
Open Scope R_scope.

Theorem dimension_symmetry_limit :
  forall C z1 z2 D1 D2 : R,
  C * (z1 - z2) * (D1 - D2) = 0 ->
  C <> 0 ->
  z1 - z2 <> 0 ->
  D1 = D2.
Proof.
  intros C z1 z2 D1 D2 H_eq H_C_neq H_z_neq.
  apply Rminus_diag_uniq.
  destruct (Rmult_integral _ _ H_eq) as [H_C_z | H_D].
  - destruct (Rmult_integral _ _ H_C_z) as [H_C | H_z].
    + contradiction.
    + contradiction.
  - assumption.
Qed.
