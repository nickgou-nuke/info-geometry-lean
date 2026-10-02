import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace InfoGeometry.Physics.CobaltAsymmetry

noncomputable section

def betaAngularIntensity (alignment angle : ℝ) : ℝ :=
  1 - alignment * Real.cos angle

def gammaAngularModel (amplitude anisotropy angle : ℝ) : ℝ :=
  amplitude ^ 2 - anisotropy * (Real.sin angle) ^ 2

def IsReflectionInvariant (intensity : ℝ → ℝ) : Prop :=
  ∀ angle, intensity (Real.pi - angle) = intensity angle

def IsAnisotropic (intensity : ℝ → ℝ) : Prop :=
  ∃ first second, intensity first ≠ intensity second

theorem betaAngularIntensity_nonneg (alignment angle : ℝ)
    (alignment_bound : |alignment| ≤ 1) :
    0 ≤ betaAngularIntensity alignment angle := by
  have absolute_bound : |alignment * Real.cos angle| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul alignment_bound (Real.abs_cos_le_one angle)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have upper := (abs_le.mp absolute_bound).2
  unfold betaAngularIntensity
  linarith

theorem betaAngularIntensity_reflection_difference (alignment angle : ℝ) :
    betaAngularIntensity alignment angle -
        betaAngularIntensity alignment (Real.pi - angle) =
      -2 * alignment * Real.cos angle := by
  simp only [betaAngularIntensity, Real.cos_pi_sub]
  ring

theorem beta_reflection_invariant_iff (alignment : ℝ) :
    IsReflectionInvariant (betaAngularIntensity alignment) ↔ alignment = 0 := by
  constructor
  · intro invariant
    have at_axis := invariant 0
    simp only [betaAngularIntensity, sub_zero, Real.cos_pi, Real.cos_zero,
      mul_neg_one, mul_one, sub_neg_eq_add] at at_axis
    linarith
  · rintro rfl
    intro angle
    simp [betaAngularIntensity]

theorem beta_anisotropic (alignment : ℝ) (alignment_ne : alignment ≠ 0) :
    IsAnisotropic (betaAngularIntensity alignment) := by
  refine ⟨0, Real.pi / 2, ?_⟩
  simp only [betaAngularIntensity, Real.cos_zero, Real.cos_pi_div_two,
    mul_one, mul_zero, sub_zero]
  intro equal
  apply alignment_ne
  linarith

theorem gamma_reflection_invariant (amplitude anisotropy : ℝ) :
    IsReflectionInvariant (gammaAngularModel amplitude anisotropy) := by
  intro angle
  simp only [gammaAngularModel, Real.sin_pi_sub]

theorem gamma_axis_value (amplitude anisotropy : ℝ) :
    gammaAngularModel amplitude anisotropy 0 = amplitude ^ 2 := by
  simp [gammaAngularModel]

theorem gamma_equator_value (amplitude anisotropy : ℝ) :
    gammaAngularModel amplitude anisotropy (Real.pi / 2) =
      amplitude ^ 2 - anisotropy := by
  simp [gammaAngularModel, Real.sin_pi_div_two]

theorem gamma_global_bounds (amplitude anisotropy angle : ℝ)
    (anisotropy_nonneg : 0 ≤ anisotropy) :
    amplitude ^ 2 - anisotropy ≤ gammaAngularModel amplitude anisotropy angle ∧
      gammaAngularModel amplitude anisotropy angle ≤ amplitude ^ 2 := by
  have upper := mul_le_mul_of_nonneg_left (Real.sin_sq_le_one angle) anisotropy_nonneg
  have lower := mul_nonneg anisotropy_nonneg (sq_nonneg (Real.sin angle))
  unfold gammaAngularModel
  constructor <;> linarith

theorem gamma_minimal_at_equator (amplitude anisotropy angle : ℝ)
    (anisotropy_nonneg : 0 ≤ anisotropy) :
    gammaAngularModel amplitude anisotropy (Real.pi / 2) ≤
      gammaAngularModel amplitude anisotropy angle := by
  rw [gamma_equator_value]
  exact (gamma_global_bounds amplitude anisotropy angle anisotropy_nonneg).1

theorem gamma_nonneg (amplitude anisotropy angle : ℝ)
    (anisotropy_nonneg : 0 ≤ anisotropy) (anisotropy_bound : anisotropy ≤ amplitude ^ 2) :
    0 ≤ gammaAngularModel amplitude anisotropy angle :=
  (sub_nonneg.mpr anisotropy_bound).trans
    (gamma_global_bounds amplitude anisotropy angle anisotropy_nonneg).1

theorem gamma_anisotropic (amplitude anisotropy : ℝ) (anisotropy_ne : anisotropy ≠ 0) :
    IsAnisotropic (gammaAngularModel amplitude anisotropy) := by
  refine ⟨0, Real.pi / 2, ?_⟩
  rw [gamma_axis_value, gamma_equator_value]
  intro equal
  apply anisotropy_ne
  linarith

theorem anisotropy_does_not_imply_reflection_violation :
    ∃ intensity : ℝ → ℝ,
      (∀ angle, 0 ≤ intensity angle) ∧
        IsAnisotropic intensity ∧ IsReflectionInvariant intensity := by
  refine ⟨gammaAngularModel 1 (1 / 2), ?_, ?_, gamma_reflection_invariant _ _⟩
  · intro angle
    exact gamma_nonneg _ _ angle (by norm_num) (by norm_num)
  · exact gamma_anisotropic _ _ (by norm_num)

end

end InfoGeometry.Physics.CobaltAsymmetry
