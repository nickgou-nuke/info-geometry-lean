import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.NormNum
import InfoGeometry.Clifford.CliffordTower
import InfoGeometry.Physics.PellisFineStructure

namespace InfoGeometry.Physics.FineStructureModels

open InfoGeometry.Clifford.CliffordTower
open PellisFineStructure

theorem clifford_dims : mersenne 2 = 3 ∧ mersenne 3 = 7 ∧ mersenne 7 = 127 :=
  ⟨mersenne_two, mersenne_three, mersenne_seven⟩

theorem mersenne_sum : mersenne 2 + mersenne 3 + mersenne 7 = 137 :=
  combinatorial_hierarchy_sum

/-- Pellis α⁻¹ ≈ 137.036, normal form verified -/
theorem pellis_normal : pellis_alpha_inv = 176410/243 - 88447/243 * phi :=
  pellis_normal_form

/-- α⁻¹ is close to 137 -/
theorem pellis_near_137 : |(pellis_alpha_inv : ℝ) - 137| < 1 := by
  have h₁ : 1370359991 / 10000000 < pellis_alpha_inv ∧ pellis_alpha_inv < 171294999 / 1250000 := PellisFineStructure.pellis_bounds
  have h₂ : |(pellis_alpha_inv : ℝ) - 137| < 1 := by
    rw [abs_lt]
    constructor <;> norm_num at h₁ ⊢ <;> linarith
  exact h₂

/-- Speculative α = 1/137 (definition) -/
noncomputable def alpha_c : ℝ := 1/137
theorem alpha_c_def : alpha_c = 1/137 := rfl

/-- Speculative α from Pellis (definition) -/
noncomputable def alpha_p : ℝ := 1 / pellis_alpha_inv
theorem alpha_p_def : alpha_p = 1 / pellis_alpha_inv := rfl

/-- α_p ≈ 0.0073 -/
theorem alpha_p_approx : |alpha_p - 0.0073| < 0.0001 := by
  have h₁ : 1370359991 / 10000000 < pellis_alpha_inv ∧ pellis_alpha_inv < 171294999 / 1250000 := PellisFineStructure.pellis_bounds
  have h₂ : |alpha_p - 0.0073| < 0.0001 := by
    rw [alpha_p_def]
    have h₃ : 0 < pellis_alpha_inv := by linarith [h₁.1]
    have h₄ : 1 / pellis_alpha_inv < 0.0073 + 1 / 10000 := by
      have h₅ : pellis_alpha_inv > 1370359991 / 10000000 := h₁.1
      have h₆ : 1 / pellis_alpha_inv < 1 / (1370359991 / 10000000 : ℝ) := by
        apply one_div_lt_one_div_of_lt
        · positivity
        · linarith
      have h₇ : (1 / (1370359991 / 10000000 : ℝ) : ℝ) < 0.0073 + 1 / 10000 := by norm_num
      linarith
    have h₅ : 1 / pellis_alpha_inv > 0.0073 - 1 / 10000 := by
      have h₆ : pellis_alpha_inv < 171294999 / 1250000 := h₁.2
      have h₇ : 1 / pellis_alpha_inv > 1 / (171294999 / 1250000 : ℝ) := by
        apply one_div_lt_one_div_of_lt
        · positivity
        · linarith
      have h₈ : (1 / (171294999 / 1250000 : ℝ) : ℝ) > 0.0073 - 1 / 10000 := by norm_num
      linarith
    rw [abs_lt]
    constructor <;> norm_num at h₄ h₅ ⊢ <;> linarith
  exact h₂

/-- Centralizer dimension = 137 (defined, not derived) -/
def cent_dim : ℕ := 137
theorem cent_dim_sum : cent_dim = mersenne 2 + mersenne 3 + mersenne 7 := by
  rw [cent_dim]; exact combinatorial_hierarchy_sum

end InfoGeometry.Physics.FineStructureModels
