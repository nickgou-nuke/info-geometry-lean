theory BizzetiA67IVGMR
  imports Complex_Main
begin

definition mirror_asymmetry_ratio :: "rat \<Rightarrow> rat" where
  "mirror_asymmetry_ratio eps = ((1 + eps) / (1 - eps))^2"

definition uniform_one_body :: rat where "uniform_one_body = 752 / 1000"
definition uniform_two_body :: rat where "uniform_two_body = 410 / 1000"
definition uniform_eta :: rat where
  "uniform_eta = (uniform_one_body - uniform_two_body) / uniform_one_body"

lemma uniform_eta_exact:
  "uniform_eta = 171 / 376"
  by (simp add: uniform_eta_def uniform_one_body_def uniform_two_body_def; normalization)

definition eps_uniform_A1_negligible :: rat where
  "eps_uniform_A1_negligible = -872 / 10000"

definition eps_uniform_A0_negligible :: rat where
  "eps_uniform_A0_negligible = 120 / 1000"

definition R_uniform_A1_negligible :: rat where
  "R_uniform_A1_negligible = mirror_asymmetry_ratio eps_uniform_A1_negligible"

definition R_uniform_A0_negligible :: rat where
  "R_uniform_A0_negligible = mirror_asymmetry_ratio eps_uniform_A0_negligible"

lemma R_uniform_A1_negligible_exact:
  "R_uniform_A1_negligible = 1301881 / 1846881"
  by (simp add: R_uniform_A1_negligible_def mirror_asymmetry_ratio_def
    eps_uniform_A1_negligible_def; normalization)

lemma R_uniform_A0_negligible_exact:
  "R_uniform_A0_negligible = 196 / 121"
  by (simp add: R_uniform_A0_negligible_def mirror_asymmetry_ratio_def
    eps_uniform_A0_negligible_def; normalization)

definition higher_order_upper_relative :: rat where
  "higher_order_upper_relative = 1 / 1000"

lemma higher_order_three_orders:
  "higher_order_upper_relative = (1 / 10)^3"
  by (simp add: higher_order_upper_relative_def; normalization)

definition pf_average_lower_shell :: rat where
  "pf_average_lower_shell = 615 / 1000"

lemma two_body_coefficient_exact:
  "(2 / 3) * pf_average_lower_shell = 41 / 100"
  by (simp add: pf_average_lower_shell_def; normalization)

end
