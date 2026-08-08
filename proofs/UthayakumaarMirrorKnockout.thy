theory UthayakumaarMirrorKnockout
  imports Complex_Main
begin

definition two_tz :: "int \<Rightarrow> int \<Rightarrow> int" where
  "two_tz Z N = N - Z"

lemma two_tz_Mn47: "two_tz 25 22 = -3"
  by (simp add: two_tz_def)

lemma two_tz_Ti47: "two_tz 22 25 = 3"
  by (simp add: two_tz_def)

lemma two_tz_Cr45: "two_tz 24 21 = -3"
  by (simp add: two_tz_def)

lemma two_tz_Sc45: "two_tz 21 24 = 3"
  by (simp add: two_tz_def)

definition med :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "med e_proton_rich e_neutron_rich = e_proton_rich - e_neutron_rich"

definition suppression_line :: "rat \<Rightarrow> rat" where
  "suppression_line deltaS = 61 / 100 - (2 / 125) * deltaS"

definition Rs_Ti47 :: rat where
  "Rs_Ti47 = suppression_line (1916 / 1000)"

definition Rs_Mn47 :: rat where
  "Rs_Mn47 = suppression_line (1442 / 100)"

lemma Rs_Ti47_exact:
  "Rs_Ti47 = 72418 / 125000"
  by (simp add: Rs_Ti47_def suppression_line_def; normalization)

lemma Rs_Mn47_exact:
  "Rs_Mn47 = 4741 / 12500"
  by (simp add: Rs_Mn47_def suppression_line_def; normalization)

lemma Mn47_more_suppressed:
  "Rs_Mn47 < Rs_Ti47"
  by (simp add: Rs_Ti47_exact Rs_Mn47_exact; normalization)

lemma first_excited_energy_MED_A47:
  "med (1226 / 10) (1594 / 10) = -184 / 5"
  by (simp add: med_def; normalization)

definition BM1_ratio :: rat where
  "BM1_ratio = 97 / 100"

lemma BM1_ratio_precision_10_percent:
  "abs (BM1_ratio - 1) \<le> 1 / 10"
  by (simp add: BM1_ratio_def; normalization)

end
