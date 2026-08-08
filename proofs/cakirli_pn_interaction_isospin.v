From Stdlib Require Import QArith Lra.

Open Scope Q_scope.

Definition Tz (N Z0 : Q) : Q := (N - Z0) / 2.

Lemma Tz_23Na_23Mg :
  Tz 12 11 == 1 / 2 /\ Tz 11 12 == -1 / 2.
Proof. split; unfold Tz; field. Qed.

Definition binding_energy (Z0 N mp mn M c2 : Q) : Q :=
  (Z0 * mp + N * mn - M) * c2.

Definition mirror_delta (delta_tz_neg_half delta_tz_pos_half : Q) : Q :=
  delta_tz_neg_half - delta_tz_pos_half.

Definition near_zero_band (x : Q) : Prop := -50 <= x <= 50.

Lemma A7_delta_exact : mirror_delta 5785 5970 == -185.
Proof. unfold mirror_delta; field. Qed.

Lemma A9_delta_exact : mirror_delta 914 1037 == -123.
Proof. unfold mirror_delta; field. Qed.

Lemma A13_central_delta_exact :
  mirror_delta 1661 2222 == -561.
Proof. unfold mirror_delta; field. Qed.

Lemma A15_delta_exact : mirror_delta (41384 / 10) (41320 / 10) == 64 / 10.
Proof. unfold mirror_delta; field. Qed.

Lemma A17_central_delta_exact :
  mirror_delta 935 (14625 / 10) == -1055 / 2.
Proof. unfold mirror_delta; field. Qed.

Lemma A23_delta_exact :
  mirror_delta (31920 / 10) (318140 / 100) == 106 / 10.
Proof. unfold mirror_delta; field. Qed.

Lemma A25_central_delta_exact :
  mirror_delta (10650 / 10) (10650 / 10) == 0.
Proof. unfold mirror_delta; field. Qed.

Lemma A13_large_magnitude_exact :
  - mirror_delta 1661 2222 == 561.
Proof. unfold mirror_delta; field. Qed.
