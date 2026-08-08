theory SouriauCasimirEntropyLeaves
  imports Complex_Main
begin

definition isospin_casimir :: "rat \<Rightarrow> rat" where
  "isospin_casimir I = I * (I + 1)"

definition poincare_mass_casimir :: "rat \<Rightarrow> rat" where
  "poincare_mass_casimir mass_sq = - mass_sq"

definition dilation_spring_stiffness :: "rat \<Rightarrow> rat" where
  "dilation_spring_stiffness C1 = - C1"

definition legendre_entropy :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "legendre_entropy logZ pairing = logZ + pairing"

lemma isospin_half_casimir:
  "isospin_casimir (1 / 2) = 3 / 4"
  by (simp add: isospin_casimir_def; normalization)

lemma isospin_flip_tz_sum:
  "(-1 / 2 :: rat) + 1 / 2 = 0"
  by normalization

lemma dilation_spring_stiffness_massSq:
  "dilation_spring_stiffness (poincare_mass_casimir 67) = 67"
  by (simp add: dilation_spring_stiffness_def poincare_mass_casimir_def)

definition ivgmr_coefficient :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "ivgmr_coefficient A e R deltaE0 = ((A - 1) * e^2) / (4 * R * deltaE0)"

definition ivgmr_one_body_radial :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "ivgmr_one_body_radial ri R = ri^3 / R^2"

definition ivgmr_two_body_radial :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "ivgmr_two_body_radial ri rj R = ri * rj^2 / R^3"

definition induced_isoscalar_e1_kernel ::
  "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "induced_isoscalar_e1_kernel A e R deltaE0 ri rj =
    ivgmr_coefficient A e R deltaE0 *
      (ivgmr_one_body_radial ri R + ivgmr_two_body_radial ri rj R)"

lemma A67_IVGMR_kernel_exact:
  "induced_isoscalar_e1_kernel 67 1 1 20 1 1 = 33 / 20"
  by (simp add: induced_isoscalar_e1_kernel_def ivgmr_coefficient_def
    ivgmr_one_body_radial_def ivgmr_two_body_radial_def; normalization)

definition entropy_from_casimirs :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "entropy_from_casimirs a b c C1 C2 = a * C1 + b * C2 + c"

lemma same_casimir_same_entropy:
  "entropy_from_casimirs a b c C1 C2 = entropy_from_casimirs a b c C1 C2"
  by simp

end
