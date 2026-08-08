theory SarkarTwoLevelIsospinMixing
  imports Complex_Main
begin

definition observed_gap :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "observed_gap E1 E2 = E2 - E1"

definition H11 :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "H11 E1 E2 b2 = E1 + b2 * observed_gap E1 E2"

definition H22 :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "H22 E1 E2 b2 = E2 - b2 * observed_gap E1 E2"

definition unperturbed_gap :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "unperturbed_gap E1 E2 b2 = H22 E1 E2 b2 - H11 E1 E2 b2"

lemma trace_invariant:
  "H11 E1 E2 b2 + H22 E1 E2 b2 = E1 + E2"
  by (simp add: H11_def H22_def observed_gap_def; algebra)

lemma unperturbed_gap_eq:
  "unperturbed_gap E1 E2 b2 = (1 - 2 * b2) * observed_gap E1 E2"
  by (simp add: unperturbed_gap_def H11_def H22_def observed_gap_def; algebra)

definition b2_from_gap :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "b2_from_gap gap obs_gap = (1 - gap / obs_gap) / 2"

lemma b2_from_gap_reconstructs:
  assumes "obs_gap \<noteq> 0"
  shows "(1 - 2 * b2_from_gap gap obs_gap) * obs_gap = gap"
  using assms by (simp add: b2_from_gap_def field_simps)

definition Mg24_E1 :: rat where "Mg24_E1 = 982811 / 100"
definition Mg24_E2 :: rat where "Mg24_E2 = 996719 / 100"
definition Mg24_shell_gap :: rat where "Mg24_shell_gap = 3"
definition Mg24_obs_gap :: rat where "Mg24_obs_gap = observed_gap Mg24_E1 Mg24_E2"
definition Mg24_b2_gap :: rat where "Mg24_b2_gap = b2_from_gap Mg24_shell_gap Mg24_obs_gap"

lemma Mg24_observed_gap_exact:
  "Mg24_obs_gap = 3477 / 25"
  by (simp add: Mg24_obs_gap_def observed_gap_def Mg24_E1_def Mg24_E2_def; normalization)

lemma Mg24_gap_formula_b2_exact:
  "Mg24_b2_gap = 567 / 1159"
  by (simp add: Mg24_b2_gap_def b2_from_gap_def Mg24_shell_gap_def
    Mg24_obs_gap_def observed_gap_def Mg24_E1_def Mg24_E2_def; normalization)

lemma Mg24_unperturbed_gap_reconstructs:
  "unperturbed_gap Mg24_E1 Mg24_E2 Mg24_b2_gap = Mg24_shell_gap"
  by (simp add: unperturbed_gap_def H11_def H22_def Mg24_b2_gap_def
    b2_from_gap_def Mg24_shell_gap_def Mg24_obs_gap_def observed_gap_def
    Mg24_E1_def Mg24_E2_def; normalization)

definition Co54_H11_central :: rat where "Co54_H11_central = 265244 / 100"
definition Co54_H22_central :: rat where "Co54_H22_central = 285084 / 100"

lemma Co54_table_unperturbed_gap_exact:
  "Co54_H22_central - Co54_H11_central = 992 / 5"
  by (simp add: Co54_H11_central_def Co54_H22_central_def; normalization)

end
