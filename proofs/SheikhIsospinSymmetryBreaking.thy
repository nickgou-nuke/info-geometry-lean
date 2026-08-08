theory SheikhIsospinSymmetryBreaking
  imports Complex_Main
begin

definition two_Tz :: "int \<Rightarrow> int \<Rightarrow> int" where
  "two_Tz N Z = N - Z"

definition Tz :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "Tz N Z = (N - Z) / 2"

lemma two_Tz_self_conjugate:
  "two_Tz 16 16 = 0"
  by (simp add: two_Tz_def)

definition up_quark_mass :: rat where "up_quark_mass = 219 / 100"
definition down_quark_mass :: rat where "down_quark_mass = 467 / 100"
definition strange_quark_mass :: rat where "strange_quark_mass = 94"

definition qcd_isoscalar :: rat where
  "qcd_isoscalar = (up_quark_mass + down_quark_mass) / 2"

definition qcd_isovector :: rat where
  "qcd_isovector = (up_quark_mass - down_quark_mass) / 2"

lemma down_minus_up_quark_mass:
  "down_quark_mass - up_quark_mass = 62 / 25"
  by (simp add: down_quark_mass_def up_quark_mass_def; normalization)

lemma qcd_isoscalar_exact:
  "qcd_isoscalar = 343 / 100"
  by (simp add: qcd_isoscalar_def down_quark_mass_def up_quark_mass_def; normalization)

lemma qcd_isovector_exact:
  "qcd_isovector = -31 / 25"
  by (simp add: qcd_isovector_def down_quark_mass_def up_quark_mass_def; normalization)

definition tz_neutron :: rat where "tz_neutron = 1 / 2"
definition tz_proton :: rat where "tz_proton = -1 / 2"

definition henley_class_I :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "henley_class_I a b tau_dot = a + b * tau_dot"

definition henley_class_II :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "henley_class_II c tau3_i tau3_j tau_dot =
    c * (tau3_i * tau3_j - tau_dot / 3)"

definition henley_class_III :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "henley_class_III d tau3_i tau3_j = d * (tau3_i + tau3_j)"

lemma henley_classIII_np_vanishes:
  "henley_class_III d tz_neutron tz_proton = 0"
  by (simp add: henley_class_III_def tz_neutron_def tz_proton_def; normalization)

definition IMME :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "IMME a b c tz = a + b * tz + c * tz^2"

lemma IMME_mirror_difference:
  "IMME a b c t - IMME a b c (-t) = 2 * b * t"
  by (simp add: IMME_def; algebra)

lemma IMME_mirror_sum:
  "IMME a b c t + IMME a b c (-t) = 2 * a + 2 * c * t^2"
  by (simp add: IMME_def; algebra)

definition split :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "split left right = left - right"

lemma neutron_proton_mass_split_exact:
  "split (93957 / 100) (93828 / 100) = 129 / 100"
  by (simp add: split_def; normalization)

lemma H3_He3_mass_split_exact:
  "split (280894 / 100) (280842 / 100) = 13 / 25"
  by (simp add: split_def; normalization)

lemma He5_Li5_mass_split_exact:
  "split (466787 / 100) (466766 / 100) = 21 / 100"
  by (simp add: split_def; normalization)

lemma Li7_Be7_mass_split_exact:
  "split (653389 / 100) (653424 / 100) = -7 / 20"
  by (simp add: split_def; normalization)

end
