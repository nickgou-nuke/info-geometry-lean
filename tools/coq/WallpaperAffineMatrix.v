From Stdlib Require Import Reals Psatz.

Open Scope R_scope.

Definition p2_square : R := (-1) * (-1).
Definition pm_square : R := (-1) * (-1).
Definition pg_shift : R := /2 + /2.

Theorem p2_square_eq_one : p2_square = 1.
Proof. unfold p2_square; nra. Qed.

Theorem pm_square_eq_one : pm_square = 1.
Proof. unfold pm_square; nra. Qed.

Theorem pg_shift_eq_one : pg_shift = 1.
Proof. unfold pg_shift; nra. Qed.

Theorem pm_conjugates_y_translation_example :
  (-1) * (3 + 1) = ((-1) * 3) - 1.
Proof. nra. Qed.
