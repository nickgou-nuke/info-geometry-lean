theory SymmetryReviewISB
  imports Complex_Main
begin

definition Tz :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "Tz N Z = (N - Z) / 2"

lemma Tz_projection_formula:
  "2 * Tz N Z = N - Z"
  by (simp add: Tz_def; algebra)

definition up_quark_mass :: rat where "up_quark_mass = 219 / 100"
definition down_quark_mass :: rat where "down_quark_mass = 467 / 100"
definition qcd_isoscalar :: rat where
  "qcd_isoscalar = (up_quark_mass + down_quark_mass) / 2"
definition qcd_isovector :: rat where
  "qcd_isovector = (up_quark_mass - down_quark_mass) / 2"

lemma qcd_mass_split_exact:
  "down_quark_mass - up_quark_mass = 62 / 25"
  by (simp add: down_quark_mass_def up_quark_mass_def; normalization)

lemma qcd_isoscalar_exact:
  "qcd_isoscalar = 343 / 100"
  by (simp add: qcd_isoscalar_def down_quark_mass_def up_quark_mass_def; normalization)

lemma qcd_isovector_exact:
  "qcd_isovector = -31 / 25"
  by (simp add: qcd_isovector_def down_quark_mass_def up_quark_mass_def; normalization)

definition IMME :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "IMME a b c tz = a + b * tz + c * tz^2"

lemma IMME_mirror_difference:
  "IMME a b c t - IMME a b c (-t) = 2 * b * t"
  by (simp add: IMME_def; algebra)

definition scattering_CIB :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "scattering_CIB app ann anp = (app + ann) / 2 - anp"

definition scattering_CSB :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "scattering_CSB app ann = app - ann"

lemma scattering_CIB_reported_anchor:
  "scattering_CIB 0 0 (-57 / 10) = 57 / 10"
  by (simp add: scattering_CIB_def; normalization)

lemma scattering_CSB_reported_anchor:
  "scattering_CSB (3 / 4) (-3 / 4) = 3 / 2"
  by (simp add: scattering_CSB_def; normalization)

definition MED :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "MED EminusTz EplusTz = EminusTz - EplusTz"

lemma MED_26Si_4plus:
  "MED 477 0 = 477"
  by (simp add: MED_def; normalization)

lemma MED_24Si_0plus:
  "MED (-1298) 0 = -1298"
  by (simp add: MED_def; normalization)

end
