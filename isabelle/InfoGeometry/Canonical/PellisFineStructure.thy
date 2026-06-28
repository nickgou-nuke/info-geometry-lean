-- Pellis Fine-Structure Constant - Isabelle/HOL Formalization
-- Stergios Pellis (2022): α⁻¹ = 360·φ⁻² - 2·φ⁻³ + (3·φ)⁻⁵

theory PellisFineStructure
  imports Main Transcendental
begin

section ‹Golden Ratio›

definition phi :: real where
  "phi = (1 + sqrt 5) / 2"

lemma phi_pos [simp]: "phi > 0"
  unfolding phi_def
  by (simp add: sqrt_nonneg)

lemma phi_neq_zero [simp]: "phi ≠ 0"
  using phi_pos by auto

lemma phi_quadratic: "phi^2 = phi + 1"
proof -
  have "sqrt 5 ≥ 0" by simp
  then show ?thesis
    unfolding phi_def
    by (nlinarith [real_sqrt_pow2[OF order_refl]])
qed

lemma phi_inv_sq: "1 / phi^2 = 2 - phi"
proof -
  have "phi^2 = phi + 1" by (rule phi_quadratic)
  then show ?thesis
    by (field_simp, nlinarith)
qed

lemma phi_inv_cube: "1 / phi^3 = 2 * phi - 3"
proof -
  have "phi^3 = 2 * phi + 1"
    by (metis phi_quadratic power3_eq_cube ring_class.ring_distribs(1) ring_class.ring_distribs(4) semiring_norm(5))
  then show ?thesis
    by (field_simp, nlinarith)
qed

lemma phi_inv_fifth: "1 / phi^5 = 5 * phi - 8"
proof -
  have "phi^5 = 5 * phi + 3"
    by (metis phi_quadratic power Suc_numeral power3_eq_cube power4_eq_pow 
              semiring_norm(2,5,8,9) add.commute add.left_commute mult.assoc 
              mult.commute mult.left_commute ring_class.ring_distribs(1,4))
  then show ?thesis
    by (field_simp, nlinarith)
qed

section ‹Pellis Formula›

definition pellis_alpha_inv :: real where
  "pellis_alpha_inv = 360 / phi^2 - 2 / phi^3 + 1 / (3 * phi)^5"

theorem pellis_normal_form:
  "pellis_alpha_inv = (176410 :: real) / 243 - (88447 :: real) / 243 * phi"
proof -
  have "pellis_alpha_inv = 360 * (1/phi^2) - 2 * (1/phi^3) + 1/(243 * phi^5)"
    unfolding pellis_alpha_inv_def
    by (field_simp, simp add: power5_eq)
  also have "... = 360 * (2 - phi) - 2 * (2*phi - 3) + 1/243 * (5*phi - 8)"
    using phi_inv_sq phi_inv_cube phi_inv_fifth by simp
  also have "... = 176410/243 - 88447/243 * phi"
    by simp
  finally show ?thesis .
qed

theorem pellis_bounds:
  "(1370359991 :: real) / 10000000 < pellis_alpha_inv ∧ 
   pellis_alpha_inv < (171294999 :: real) / 1250000"
proof -
  have "sqrt 5 > 2.236067977499789696"
    by (rule real_sqrt_less_iff[THEN iffD2], norm_num)
  moreover have "sqrt 5 < 2.236067977499789697"
    by (rule real_sqrt_less_iff[THEN iffD2], norm_num)
  ultimately show ?thesis
    unfolding pellis_alpha_inv_def phi_def
    by (auto simp add: intro!: nlinarith [real_sqrt_pow2[OF order_refl]])
qed

corollary codata_agreement:
  "abs (pellis_alpha_inv - (137035999084 :: real) / 1000000000) < 1 / 10000000"
  using pellis_bounds
  by (auto simp add: abs_less_iff)

section ‹Alternative Forms›

theorem pellis_v9:
  "(362 - 3 - 4 :: real) / phi^2 - (1 - 3 - 5) / phi = pellis_alpha_inv"
  unfolding pellis_alpha_inv_def
  using phi_inv_sq by (simp add: field_simps)

theorem pellis_v11:
  "phi^0 - 2 / phi + 360 / phi^2 - 1 / phi^3 + 1 / (3 * phi)^5 = pellis_alpha_inv"
  unfolding pellis_alpha_inv_def
  by simp

end