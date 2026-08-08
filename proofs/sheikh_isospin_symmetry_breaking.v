From Stdlib Require Import QArith.

Open Scope Q_scope.

Definition two_Tz (N Z0 : Z) : Z := (N - Z0)%Z.
Definition Tz (N Z0 : Q) : Q := (N - Z0) / 2.

Lemma two_Tz_self_conjugate : two_Tz 16 16 = 0%Z.
Proof. reflexivity. Qed.

Definition up_quark_mass : Q := 219 / 100.
Definition down_quark_mass : Q := 467 / 100.
Definition strange_quark_mass : Q := 94.

Definition qcd_isoscalar : Q := (up_quark_mass + down_quark_mass) / 2.
Definition qcd_isovector : Q := (up_quark_mass - down_quark_mass) / 2.

Lemma down_minus_up_quark_mass : down_quark_mass - up_quark_mass == 62 / 25.
Proof. unfold down_quark_mass, up_quark_mass; field. Qed.

Lemma qcd_isoscalar_exact : qcd_isoscalar == 343 / 100.
Proof. unfold qcd_isoscalar, up_quark_mass, down_quark_mass; field. Qed.

Lemma qcd_isovector_exact : qcd_isovector == -31 / 25.
Proof. unfold qcd_isovector, up_quark_mass, down_quark_mass; field. Qed.

Lemma qcd_u_entry_reconstructs :
  qcd_isoscalar + qcd_isovector == up_quark_mass.
Proof. unfold qcd_isoscalar, qcd_isovector, up_quark_mass, down_quark_mass; field. Qed.

Lemma qcd_d_entry_reconstructs :
  qcd_isoscalar - qcd_isovector == down_quark_mass.
Proof. unfold qcd_isoscalar, qcd_isovector, up_quark_mass, down_quark_mass; field. Qed.

Definition tz_neutron : Q := 1 / 2.
Definition tz_proton : Q := -1 / 2.

Definition henley_class_I (a b tau_dot : Q) : Q := a + b * tau_dot.
Definition henley_class_II (c tau3_i tau3_j tau_dot : Q) : Q :=
  c * (tau3_i * tau3_j - tau_dot / 3).
Definition henley_class_III (d tau3_i tau3_j : Q) : Q :=
  d * (tau3_i + tau3_j).

Lemma henley_classIII_np_vanishes (d : Q) :
  henley_class_III d tz_neutron tz_proton == 0.
Proof. unfold henley_class_III, tz_neutron, tz_proton; field. Qed.

Definition IMME (a b c tz : Q) : Q := a + b * tz + c * tz * tz.

Lemma IMME_mirror_difference (a b c t : Q) :
  IMME a b c t - IMME a b c (-t) == 2 * b * t.
Proof. unfold IMME; ring. Qed.

Lemma IMME_mirror_sum (a b c t : Q) :
  IMME a b c t + IMME a b c (-t) == 2 * a + 2 * c * t * t.
Proof. unfold IMME; ring. Qed.

Definition split (left right : Q) : Q := left - right.

Lemma neutron_proton_mass_split_exact :
  split (93957 / 100) (93828 / 100) == 129 / 100.
Proof. unfold split; field. Qed.

Lemma H3_He3_mass_split_exact :
  split (280894 / 100) (280842 / 100) == 13 / 25.
Proof. unfold split; field. Qed.

Lemma He5_Li5_mass_split_exact :
  split (466787 / 100) (466766 / 100) == 21 / 100.
Proof. unfold split; field. Qed.

Lemma Li7_Be7_mass_split_exact :
  split (653389 / 100) (653424 / 100) == -7 / 20.
Proof. unfold split; field. Qed.
