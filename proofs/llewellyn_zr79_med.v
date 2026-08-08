From Stdlib Require Import QArith.

Open Scope Q_scope.

Definition Tz (N Z0 : Q) : Q := (N - Z0) / 2.

Lemma Zr79_Y79_Tz :
  Tz 39 40 == -1 / 2 /\ Tz 40 39 == 1 / 2.
Proof. split; unfold Tz; field. Qed.

Definition MED (excitation_tz_neg_half excitation_tz_pos_half : Q) : Q :=
  excitation_tz_neg_half - excitation_tz_pos_half.

Definition level_from_transition (lower gamma : Q) : Q := lower + gamma.

Lemma MED_7_2_exact : MED 184 183 == 1.
Proof. unfold MED; field. Qed.

Lemma MED_9_2_exact : MED 416 411 == 5.
Proof. unfold MED; field. Qed.

Lemma MED_11_2_exact : MED 715 726 == -11.
Proof. unfold MED; field. Qed.

Lemma MED_13_2_exact : MED 1042 1042 == 0.
Proof. unfold MED; field. Qed.

Lemma Y79_cascade_cross_over_discrepancy :
  level_from_transition 183 227 - 411 == -1.
Proof. unfold level_from_transition; field. Qed.

Lemma Zr79_cascade_cross_over_discrepancy :
  level_from_transition 184 230 - 416 == -2.
Proof. unfold level_from_transition; field. Qed.

Lemma beta_Y_ordering_difference :
  296 / 1000 - 294 / 1000 == 1 / 500.
Proof. field. Qed.

Lemma beta_Zr_ordering_difference :
  304 / 1000 - 298 / 1000 == 3 / 500.
Proof. field. Qed.

Lemma selected_to_mixing_configurations :
  (10 * 4)%nat = 40%nat.
Proof. reflexivity. Qed.
