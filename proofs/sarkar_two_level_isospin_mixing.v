From Stdlib Require Import QArith.

Open Scope Q_scope.

Definition observed_gap (E1 E2 : Q) : Q := E2 - E1.

Definition H11 (E1 E2 b2 : Q) : Q :=
  E1 + b2 * observed_gap E1 E2.

Definition H22 (E1 E2 b2 : Q) : Q :=
  E2 - b2 * observed_gap E1 E2.

Definition unperturbed_gap (E1 E2 b2 : Q) : Q :=
  H22 E1 E2 b2 - H11 E1 E2 b2.

Lemma trace_invariant (E1 E2 b2 : Q) :
  H11 E1 E2 b2 + H22 E1 E2 b2 == E1 + E2.
Proof. unfold H11, H22, observed_gap; ring. Qed.

Lemma unperturbed_gap_eq (E1 E2 b2 : Q) :
  unperturbed_gap E1 E2 b2 == (1 - 2 * b2) * observed_gap E1 E2.
Proof. unfold unperturbed_gap, H11, H22, observed_gap; ring. Qed.

Definition b2_from_gap (gap obs_gap : Q) : Q :=
  (1 - gap / obs_gap) / 2.

Lemma b2_from_gap_reconstructs (gap obs_gap : Q) :
  ~ obs_gap == 0 -> (1 - 2 * b2_from_gap gap obs_gap) * obs_gap == gap.
Proof. intros h; unfold b2_from_gap; field; exact h. Qed.

Definition H12sq (E1 E2 b2 : Q) : Q :=
  (b2 - b2 * b2) * observed_gap E1 E2 * observed_gap E1 E2.

Lemma H12sq_symmetric_half (E1 E2 : Q) :
  H12sq E1 E2 (1 / 2) == observed_gap E1 E2 * observed_gap E1 E2 / 4.
Proof. unfold H12sq; field. Qed.

Definition Mg24_E1 : Q := 982811 / 100.
Definition Mg24_E2 : Q := 996719 / 100.
Definition Mg24_shell_gap : Q := 3.
Definition Mg24_obs_gap : Q := observed_gap Mg24_E1 Mg24_E2.
Definition Mg24_b2_gap : Q := b2_from_gap Mg24_shell_gap Mg24_obs_gap.

Lemma Mg24_observed_gap_exact :
  Mg24_obs_gap == 3477 / 25.
Proof. unfold Mg24_obs_gap, observed_gap, Mg24_E1, Mg24_E2; field. Qed.

Lemma Mg24_gap_formula_b2_exact :
  Mg24_b2_gap == 567 / 1159.
Proof.
  unfold Mg24_b2_gap, b2_from_gap, Mg24_shell_gap, Mg24_obs_gap,
    observed_gap, Mg24_E1, Mg24_E2.
  field.
Qed.

Lemma Mg24_unperturbed_gap_reconstructs :
  unperturbed_gap Mg24_E1 Mg24_E2 Mg24_b2_gap == Mg24_shell_gap.
Proof.
  unfold unperturbed_gap, H11, H22, Mg24_b2_gap, b2_from_gap,
    Mg24_shell_gap, Mg24_obs_gap, observed_gap, Mg24_E1, Mg24_E2.
  field.
Qed.

Definition Co54_H11_central : Q := 265244 / 100.
Definition Co54_H22_central : Q := 285084 / 100.

Lemma Co54_table_unperturbed_gap_exact :
  Co54_H22_central - Co54_H11_central == 992 / 5.
Proof. unfold Co54_H11_central, Co54_H22_central; field. Qed.
