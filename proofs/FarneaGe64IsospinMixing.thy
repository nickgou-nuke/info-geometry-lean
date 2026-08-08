theory FarneaGe64IsospinMixing
  imports Complex_Main
begin

definition T3 :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "T3 Z N = (Z - N) / 2"

definition mass_number :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "mass_number N Z = N + Z"

definition fusion_evaporation_mass :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "fusion_evaporation_mass target projectile alpha_count =
    target + projectile - 4 * alpha_count"

lemma Ge64_NZ:
  "mass_number 32 32 = 64 \<and> T3 32 32 = 0"
  by (simp add: mass_number_def T3_def; normalization)

lemma Ca40_S32_twoAlpha_to_Ge64:
  "fusion_evaporation_mass 40 32 2 = 64"
  by (simp add: fusion_evaporation_mass_def; normalization)

definition large_delta :: rat where "large_delta = -39 / 10"
definition chi2_large :: rat where "chi2_large = 54 / 100"
definition chi2_small :: rat where "chi2_small = 80 / 100"
definition quadrupole_content :: "rat \<Rightarrow> rat" where
  "quadrupole_content delta = delta^2 / (1 + delta^2)"

lemma large_delta_statistically_favoured:
  "chi2_large < chi2_small"
  by (simp add: chi2_large_def chi2_small_def)

lemma large_delta_quadrupole_content_exact:
  "quadrupole_content large_delta = 1521 / 1621"
  by (simp add: quadrupole_content_def large_delta_def; normalization)

lemma large_delta_quadrupole_content_above_93_percent:
  "93 / 100 < quadrupole_content large_delta"
  using large_delta_quadrupole_content_exact by simp

definition tau9_upper_ps :: rat where "tau9_upper_ps = 4"
definition tau7_ps :: rat where "tau7_ps = 431 / 10"
definition tau5_ps :: rat where "tau5_ps = 242 / 10"
definition lambda7_ps_inv :: rat where "lambda7_ps_inv = 232 / 10000"

lemma reported_lifetime_order:
  "tau9_upper_ps < tau5_ps \<and> tau5_ps < tau7_ps"
  by (simp add: tau9_upper_ps_def tau5_ps_def tau7_ps_def)

lemma lambda7_reciprocal_window:
  "43 < 1 / lambda7_ps_inv \<and> 1 / lambda7_ps_inv < 432 / 10"
  by (simp add: lambda7_ps_inv_def)

definition I1665 :: rat where "I1665 = 567"
definition I1048 :: rat where "I1048 = 130"
definition I747 :: rat where "I747 = 89"

lemma branch_intensity_sum:
  "I1665 + I1048 + I747 = 786"
  by (simp add: I1665_def I1048_def I747_def; normalization)

lemma branch_1665_dominates:
  "I1048 + I747 < I1665"
  by (simp add: I1665_def I1048_def I747_def)

definition BE1_64Ge_Wu :: rat where "BE1_64Ge_Wu = 247 / 1000000000"
definition BM2_64Ge_Wu :: rat where "BM2_64Ge_Wu = 606 / 100"
definition BE1_66Ge_Wu :: rat where "BE1_66Ge_Wu = 37 / 10000000"
definition BM2_66Ge_Wu :: rat where "BM2_66Ge_Wu = 39 / 10000"
definition BM2_68Ge_Wu :: rat where "BM2_68Ge_Wu = 71 / 100"

lemma BE1_64Ge_order_of_magnitude_below_66Ge:
  "BE1_64Ge_Wu / BE1_66Ge_Wu = 247 / 3700 \<and>
   BE1_64Ge_Wu < BE1_66Ge_Wu"
  by (simp add: BE1_64Ge_Wu_def BE1_66Ge_Wu_def; normalization)

lemma BM2_64Ge_large_against_66Ge:
  "BM2_64Ge_Wu / BM2_66Ge_Wu = 20200 / 13"
  by (simp add: BM2_64Ge_Wu_def BM2_66Ge_Wu_def; normalization)

lemma BM2_64Ge_above_68Ge:
  "BM2_68Ge_Wu < BM2_64Ge_Wu"
  by (simp add: BM2_68Ge_Wu_def BM2_64Ge_Wu_def)

definition BE2_64Ge_747_Wu :: rat where "BE2_64Ge_747_Wu = 1"
definition BE2_66Ge_886_Wu :: rat where "BE2_66Ge_886_Wu = 4 / 10"

lemma weak_E2_ratio:
  "BE2_64Ge_747_Wu / BE2_66Ge_886_Wu = 5 / 2"
  by (simp add: BE2_64Ge_747_Wu_def BE2_66Ge_886_Wu_def; normalization)

definition alpha_difference :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "alpha_difference alpha_i alpha_f = alpha_i - alpha_f"

definition eq6_amplitude_scale :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "eq6_amplitude_scale alpha_i alpha_f =
    (2 / 3) * (alpha_difference alpha_i alpha_f)^2"

definition eq7_BE1_64_from_66 :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "eq7_BE1_64_from_66 alpha2 BE1_66 = (8 / 3) * alpha2 * BE1_66"

definition alpha2_from_BE1 :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "alpha2_from_BE1 BE1_64 BE1_66 = (3 / 8) * (BE1_64 / BE1_66)"

definition alpha2_extracted :: rat where
  "alpha2_extracted = alpha2_from_BE1 BE1_64Ge_Wu BE1_66Ge_Wu"

lemma eq7_alpha_symmetric_mixing:
  "eq6_amplitude_scale 1 (-1) = 8 / 3"
  by (simp add: eq6_amplitude_scale_def alpha_difference_def; normalization)

lemma alpha2_extracted_exact:
  "alpha2_extracted = 741 / 29600"
  by (simp add: alpha2_extracted_def alpha2_from_BE1_def BE1_64Ge_Wu_def BE1_66Ge_Wu_def; normalization)

lemma alpha2_extracted_percent:
  "100 * alpha2_extracted = 741 / 296"
  by (simp add: alpha2_extracted_def alpha2_from_BE1_def BE1_64Ge_Wu_def BE1_66Ge_Wu_def; normalization)

lemma alpha2_extracted_reported_window:
  "24 / 1000 < alpha2_extracted \<and> alpha2_extracted < 26 / 1000"
  by (simp add: alpha2_extracted_def alpha2_from_BE1_def BE1_64Ge_Wu_def BE1_66Ge_Wu_def)

lemma eq7_reconstructs_BE1_64:
  "eq7_BE1_64_from_66 alpha2_extracted BE1_66Ge_Wu = BE1_64Ge_Wu"
  by (simp add: eq7_BE1_64_from_66_def alpha2_extracted_def alpha2_from_BE1_def
      BE1_64Ge_Wu_def BE1_66Ge_Wu_def; normalization)

end
