theory BizzetiMirrorE1IVGMRFull
  imports Complex_Main
begin

definition T3 :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "T3 Z N = (Z - N) / 2"

lemma T3_As67_Se67:
  "T3 33 34 = -1 / 2 \<and> T3 34 33 = 1 / 2"
  by (simp add: T3_def; normalization)

definition As725_BE1 :: rat where "As725_BE1 = 14 / 10000000"
definition Se717_BE1 :: rat where "Se717_BE1 = 4 / 10000000"
definition As725_ME1 :: rat where "As725_ME1 = 37 / 10000"
definition Se717_ME1 :: rat where "Se717_ME1 = 20 / 10000"
definition As319_BE1 :: rat where "As319_BE1 = 83 / 10000000"
definition Se303_BE1_upper :: rat where "Se303_BE1_upper = 14 / 10000000"
definition As319_ME1 :: rat where "As319_ME1 = 91 / 10000"
definition Se303_ME1_upper :: rat where "Se303_ME1_upper = 37 / 10000"

lemma tableI_first_BE1_ratio:
  "As725_BE1 / Se717_BE1 = 7 / 2"
  by (simp add: As725_BE1_def Se717_BE1_def; normalization)

lemma tableI_first_ME1_ratio:
  "As725_ME1 / Se717_ME1 = 37 / 20"
  by (simp add: As725_ME1_def Se717_ME1_def; normalization)

lemma tableI_second_BE1_ratio_upper:
  "As319_BE1 / Se303_BE1_upper = 83 / 14"
  by (simp add: As319_BE1_def Se303_BE1_upper_def; normalization)

lemma tableI_second_ME1_ratio_upper:
  "As319_ME1 / Se303_ME1_upper = 91 / 37"
  by (simp add: As319_ME1_def Se303_ME1_upper_def; normalization)

definition MIV :: rat where "MIV = 29 / 10000"
definition MIS :: rat where "MIS = 9 / 10000"

lemma isoscalar_fraction:
  "MIS / MIV = 9 / 29"
  by (simp add: MIS_def MIV_def; normalization)

definition radial_cubic_siegert_ratio :: rat where
  "radial_cubic_siegert_ratio = 834 / 1000"
definition charge_correction_1MeV :: rat where
  "charge_correction_1MeV = 190 / 10000000"
definition magnetic_correction_1MeV :: rat where
  "magnetic_correction_1MeV = 53 / 100000"

lemma higher_order_corrections_subpermille:
  "charge_correction_1MeV < 1 / 1000 \<and> magnetic_correction_1MeV < 1 / 1000"
  by (simp add: charge_correction_1MeV_def magnetic_correction_1MeV_def)

definition C :: rat where "C = 116 / 1000"
definition one_body :: rat where "one_body = 752 / 1000"
definition two_body :: rat where "two_body = 410 / 1000"
definition eta :: rat where "eta = (one_body - two_body) / one_body"
definition pf_average_r2 :: rat where "pf_average_r2 = 615 / 1000"

lemma eta_exact:
  "eta = 171 / 376"
  by (simp add: eta_def one_body_def two_body_def; normalization)

lemma two_body_from_pf_average:
  "(2 / 3) * pf_average_r2 = two_body"
  by (simp add: pf_average_r2_def two_body_def; normalization)

definition mirror_ratio :: "rat \<Rightarrow> rat" where
  "mirror_ratio eps = ((1 + eps) / (1 - eps))^2"

definition eps_A1_negligible :: rat where "eps_A1_negligible = -872 / 10000"
definition eps_A0_negligible :: rat where "eps_A0_negligible = 120 / 1000"
definition eps_WS_A1_negligible :: rat where "eps_WS_A1_negligible = -852 / 10000"
definition eps_WS_A0_negligible :: rat where "eps_WS_A0_negligible = 116 / 1000"

lemma ratio_A1_negligible_exact:
  "mirror_ratio eps_A1_negligible = 1301881 / 1846881"
  by (simp add: mirror_ratio_def eps_A1_negligible_def; normalization)

lemma ratio_A0_negligible_exact:
  "mirror_ratio eps_A0_negligible = 196 / 121"
  by (simp add: mirror_ratio_def eps_A0_negligible_def; normalization)

lemma ratio_WS_exact:
  "mirror_ratio eps_WS_A1_negligible = 5230369 / 7360369 \<and>
   mirror_ratio eps_WS_A0_negligible = 77841 / 48841"
  by (simp add: mirror_ratio_def eps_WS_A1_negligible_def eps_WS_A0_negligible_def; normalization)

definition eq60_epsilon_kernel :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "eq60_epsilon_kernel C0 radial eta0 A1 A0 =
    3 * C0 * radial * ((eta0 * A1 - A0) / (A1 + 3 * A0))"

lemma eq60_A0_negligible_epsilon:
  "eq60_epsilon_kernel C one_body eta 1 0 = 14877 / 125000"
  by (simp add: eq60_epsilon_kernel_def C_def one_body_def eta_def two_body_def; normalization)

lemma A67_IVGMR_unit_kernel:
  "((67 - 1) / (4 * 20)) * (1 + 1) = (33 / 20 :: rat)"
  by normalization

end
