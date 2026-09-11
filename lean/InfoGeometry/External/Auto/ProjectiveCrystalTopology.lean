import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Projective crystal momentum glide

Repaired external file: cancellation of a nonzero translation phase shows that a
projective sign constraint forces the shifted phase to be `-1`.
-/

noncomputable section

namespace ProjectiveCrystal

open Complex

/-- Translation phase `exp(i k_y b)`. -/
def translation_phase (ky b : ℝ) : ℂ := exp (I * ((ky * b : ℝ) : ℂ))

/-- Projective algebraic sign flip. -/
def projective_algebra_constraint (ky b : ℝ) : ℂ := -translation_phase ky b

/-- Geometric shifted phase. -/
def geometric_shifted_phase (ky kappa b : ℝ) : ℂ := translation_phase (ky + kappa) b

/-- Product decomposition of the shifted translation phase. -/
theorem shifted_phase_factor (ky kappa b : ℝ) :
    geometric_shifted_phase ky kappa b = translation_phase ky b * translation_phase kappa b := by
  unfold geometric_shifted_phase translation_phase
  rw [← Complex.exp_add]
  congr 1
  norm_num
  ring

/-- The projective sign constraint forces the fractional shifted phase to be `-1`. -/
theorem projective_forces_momentum_glide (ky kappa b : ℝ)
    (h_eq : geometric_shifted_phase ky kappa b = projective_algebra_constraint ky b) :
    translation_phase kappa b = -1 := by
  rw [shifted_phase_factor, projective_algebra_constraint] at h_eq
  have h_nz : translation_phase ky b ≠ 0 := Complex.exp_ne_zero _
  calc
    translation_phase kappa b = (translation_phase ky b)⁻¹ *
        (translation_phase ky b * translation_phase kappa b) := by
      rw [← mul_assoc, inv_mul_cancel₀ h_nz, one_mul]
    _ = (translation_phase ky b)⁻¹ * (-(translation_phase ky b)) := by rw [h_eq]
    _ = -1 := by rw [mul_neg, inv_mul_cancel₀ h_nz]

#check shifted_phase_factor
#check projective_forces_momentum_glide

end ProjectiveCrystal
