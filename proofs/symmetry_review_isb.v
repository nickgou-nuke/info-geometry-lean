From Stdlib Require Import QArith.

Open Scope Q_scope.

Definition Tz (N Z0 : Q) : Q := (N - Z0) / 2.
Definition IMME (a b c tz : Q) : Q := a + b * tz + c * tz * tz.
Definition cubic_IMME (a b c d tz : Q) : Q := IMME a b c tz + d * tz * tz * tz.

Lemma Tz_projection_formula (N Z0 : Q) :
  2 * Tz N Z0 == N - Z0.
Proof. unfold Tz; field. Qed.

Definition up_quark_mass : Q := 219 / 100.
Definition down_quark_mass : Q := 467 / 100.
Definition qcd_isoscalar : Q := (up_quark_mass + down_quark_mass) / 2.
Definition qcd_isovector : Q := (up_quark_mass - down_quark_mass) / 2.

Lemma qcd_mass_split_exact :
  down_quark_mass - up_quark_mass == 62 / 25.
Proof. unfold down_quark_mass, up_quark_mass; field. Qed.

Lemma qcd_isoscalar_exact :
  qcd_isoscalar == 343 / 100.
Proof. unfold qcd_isoscalar, down_quark_mass, up_quark_mass; field. Qed.

Lemma qcd_isovector_exact :
  qcd_isovector == -31 / 25.
Proof. unfold qcd_isovector, down_quark_mass, up_quark_mass; field. Qed.

Lemma IMME_mirror_difference (a b c t : Q) :
  IMME a b c t - IMME a b c (-t) == 2 * b * t.
Proof. unfold IMME; ring. Qed.

Lemma cubic_IMME_odd_part (a b c d t : Q) :
  cubic_IMME a b c d t - cubic_IMME a b c d (-t) ==
    2 * b * t + 2 * d * t * t * t.
Proof. unfold cubic_IMME, IMME; ring. Qed.

Definition scattering_CIB (app ann anp : Q) : Q := (app + ann) / 2 - anp.
Definition scattering_CSB (app ann : Q) : Q := app - ann.

Lemma scattering_CIB_reported_anchor :
  scattering_CIB 0 0 (-57 / 10) == 57 / 10.
Proof. unfold scattering_CIB; field. Qed.

Lemma scattering_CSB_reported_anchor :
  scattering_CSB (3 / 4) (-3 / 4) == 3 / 2.
Proof. unfold scattering_CSB; field. Qed.

Definition MED (EminusTz EplusTz : Q) : Q := EminusTz - EplusTz.

Lemma MED_26Si_4plus :
  MED 477 0 == 477.
Proof. unfold MED; field. Qed.

Lemma MED_24Si_0plus :
  MED (-1298) 0 == -1298.
Proof. unfold MED; field. Qed.
