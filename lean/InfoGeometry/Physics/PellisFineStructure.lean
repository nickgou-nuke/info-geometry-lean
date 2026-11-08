import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum

/-!
# Pellis Fine-Structure Constant Formula - Complete Formalization

Stergios Pellis (2022): α⁻¹ = 360·φ⁻² - 2·φ⁻³ + (3·φ)⁻⁵
where φ = (1+√5)/2

## Main Theorems

1. φ satisfies φ² = φ + 1
2. φ⁻² = 2-φ, φ⁻³ = 2φ-3, φ⁻⁵ = 5φ-8
3. pellis_α⁻¹ = 176410/243 - (88447/243)·φ (exact linear form)
4. 137.0359991 < pellis_α⁻¹ < 137.0359992 (matches CODATA 2018)
-/

namespace PellisFineStructure

noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- Compatibility notation for downstream physics files. -/
noncomputable abbrev φ : ℝ := phi

@[simp] theorem phi_quadratic : phi ^ 2 = phi + 1 := by
  unfold phi
  nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]

@[simp] theorem phi_pos : phi > 0 := by
  unfold phi
  linarith [Real.sqrt_nonneg 5, Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)]

@[simp] theorem phi_ne_zero : phi ≠ 0 := by linarith [phi_pos]

/-- Primary formula (Equation 6) -/
noncomputable def pellis_alpha_inv : ℝ := 360 / phi^2 - 2 / phi^3 + 1 / (3 * phi)^5

theorem inv_sq : 1 / phi ^ 2 = 2 - phi := by
  have := phi_quadratic
  field_simp [phi_ne_zero]
  nlinarith

theorem inv_cube : 1 / phi ^ 3 = 2 * phi - 3 := by
  have h3 : phi ^ 3 = 2 * phi + 1 := by
    calc phi^3 = phi * phi^2 := by ring
         _ = phi * (phi + 1) := by rw [phi_quadratic]
         _ = 2 * phi + 1 := by nlinarith [phi_quadratic]
  field_simp [phi_ne_zero, h3]
  nlinarith [phi_quadratic]

theorem inv_fifth : 1 / phi ^ 5 = 5 * phi - 8 := by
  have h3 : phi ^ 3 = 2 * phi + 1 := by
    calc phi^3 = phi * phi^2 := by ring
         _ = phi * (phi + 1) := by rw [phi_quadratic]
         _ = 2 * phi + 1 := by nlinarith [phi_quadratic]
  have h4 : phi ^ 4 = 3 * phi + 2 := by
    calc phi^4 = phi * phi^3 := by ring
         _ = phi * (2 * phi + 1) := by rw [h3]
         _ = 3 * phi + 2 := by nlinarith [phi_quadratic, h3]
  have h5 : phi ^ 5 = 5 * phi + 3 := by
    calc phi^5 = phi * phi^4 := by ring
         _ = phi * (3 * phi + 2) := by rw [h4]
         _ = 5 * phi + 3 := by nlinarith [phi_quadratic, h3, h4]
  field_simp [phi_ne_zero, h5]
  nlinarith [phi_quadratic, h3, h4, h5]

/-- THEOREM: Normal form in basis {1, φ} -/
theorem pellis_normal_form : pellis_alpha_inv = 176410/243 - 88447/243 * phi := by
  unfold pellis_alpha_inv
  have h2 : 1 / phi ^ 2 = 2 - phi := inv_sq
  have h3 : 1 / phi ^ 3 = 2 * phi - 3 := inv_cube
  have h5 : 1 / phi ^ 5 = 5 * phi - 8 := inv_fifth
  calc
    pellis_alpha_inv = 360/phi^2 - 2/phi^3 + 1/(3 * phi)^5 := by rfl
    _ = 360/phi^2 - 2/phi^3 + 1/(3^5 * phi^5) := by
      rw [mul_pow]
    _ = 360*(2-phi) - 2*(2*phi-3) + 1/243*(5*phi-8) := by
      rw [div_eq_mul_inv (360 : ℝ) (phi ^ 2), div_eq_mul_inv (2 : ℝ) (phi ^ 3)]
      rw [← h2, ← h3, ← h5]
      <;> norm_num
      <;> ring
    _ = 176410/243 - 88447/243 * phi := by
      norm_num
      <;> ring

/-- Rational lower bound used for the Pellis numerical interval. -/
theorem sqrt5_lower_bound :
    (22360679774 : ℝ) / 10000000000 < Real.sqrt 5 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

/-- Rational upper bound used for the Pellis numerical interval. -/
theorem sqrt5_upper_bound :
    Real.sqrt 5 < (22360679778 : ℝ) / 10000000000 := by
  rw [Real.sqrt_lt (by norm_num) (by norm_num)]
  norm_num

/-- THEOREM: Bounds matching the stated Pellis/CODATA window. -/
theorem pellis_bounds :
    1370359991 / 10000000 < pellis_alpha_inv ∧
      pellis_alpha_inv < 171294999 / 1250000 := by
  have hphi_lo : (1 + (22360679774 : ℝ) / 10000000000) / 2 < phi := by
    unfold phi
    linarith [sqrt5_lower_bound]
  have hphi_hi : phi < (1 + (22360679778 : ℝ) / 10000000000) / 2 := by
    unfold phi
    linarith [sqrt5_upper_bound]
  rw [pellis_normal_form]
  constructor
  · calc
      (1370359991 / 10000000 : ℝ) <
          176410 / 243 - 88447 / 243 *
            ((1 + (22360679778 : ℝ) / 10000000000) / 2) := by norm_num
      _ < 176410 / 243 - 88447 / 243 * phi := by nlinarith
  · calc
      176410 / 243 - 88447 / 243 * phi <
          176410 / 243 - 88447 / 243 *
            ((1 + (22360679774 : ℝ) / 10000000000) / 2) := by nlinarith
      _ < (171294999 / 1250000 : ℝ) := by norm_num

/-- COROLLARY: Agreement with CODATA 2018 to the stated tolerance. -/
theorem codata_agreement :
    |pellis_alpha_inv - 137035999084 / 1000000000| < 1 / 10000000 := by
  have hphi_lo : (1 + (22360679774 : ℝ) / 10000000000) / 2 < phi := by
    unfold phi
    linarith [sqrt5_lower_bound]
  have hphi_hi : phi < (1 + (22360679778 : ℝ) / 10000000000) / 2 := by
    unfold phi
    linarith [sqrt5_upper_bound]
  rw [abs_lt]
  rw [pellis_normal_form]
  constructor
  · calc
      -(1 / 10000000 : ℝ) <
          (176410 / 243 - 88447 / 243 *
              ((1 + (22360679778 : ℝ) / 10000000000) / 2)) -
            137035999084 / 1000000000 := by norm_num
      _ < (176410 / 243 - 88447 / 243 * phi) -
            137035999084 / 1000000000 := by nlinarith
  · calc
      (176410 / 243 - 88447 / 243 * phi) -
            137035999084 / 1000000000 <
          (176410 / 243 - 88447 / 243 *
              ((1 + (22360679774 : ℝ) / 10000000000) / 2)) -
            137035999084 / 1000000000 := by nlinarith
      _ < (1 / 10000000 : ℝ) := by norm_num

end PellisFineStructure
