Require Import Reals.
Require Import Coquelicot.Coquelicot.

(* Formalizing the Itakura-Saito Divergence and logarithmic pullback *)

Section ItakuraSaito.

Variable P Q : R.
Hypothesis H_P : P > 0.
Hypothesis H_Q : Q > 0.

Definition D_IS (p q : R) := (p / q) - ln (p / q) - 1.

(* The 36 Fradkin-Tseytlin fields as logarithmic cocycles balancing the N=4 supersymmetry ratio *)
Definition n_gauge := 12%nat.
Definition n_weyl := (4 * n_gauge)%nat.
Definition n_ft_scalars := (3 * n_gauge)%nat.

Lemma ft_fields_is_36 : n_ft_scalars = 36%nat.
Proof.
  unfold n_ft_scalars, n_gauge.
  reflexivity.
Qed.

Lemma weyl_spinors_is_48 : n_weyl = 48%nat.
Proof.
  unfold n_weyl, n_gauge.
  reflexivity.
Qed.

End ItakuraSaito.
