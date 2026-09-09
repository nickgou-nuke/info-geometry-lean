import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.CelestialMellin

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def dilationEigenmode (E : ℝ) (omega : ℝ) : ℂ :=
  Complex.exp ((Complex.I * (E : ℂ) - (1 / 2 : ℂ)) * ((Real.log omega : ℝ) : ℂ))

def celestialWeight (lambda : ℝ) : ℂ :=
  ⟨1 / 2, lambda⟩

def mellinScaleFreePhase (E lambda omega : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((lambda + E : ℝ) * Real.log omega : ℝ) : ℂ))

theorem celestial_weight_re (lambda : ℝ) :
    (celestialWeight lambda).re = 1 / 2 := by
  unfold celestialWeight
  rfl

theorem celestial_weight_reflection (lambda : ℝ) :
    1 - star (celestialWeight lambda) = celestialWeight lambda := by
  unfold celestialWeight
  apply Complex.ext
  · simp only [sub_re, one_re, star_def, conj_re]
    norm_num
  · simp only [sub_im, one_im, star_def, conj_im, zero_sub, neg_neg]

theorem mellin_scale_free_norm (E lambda omega : ℝ) :
    ‖mellinScaleFreePhase E lambda omega‖ = 1 := by
  unfold mellinScaleFreePhase
  have h_comm : Complex.I * (((lambda + E) * Real.log omega : ℝ) : ℂ) =
      (((lambda + E) * Real.log omega : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h_comm, Complex.norm_exp_ofReal_mul_I]

def IsCelestialPrimary (Phi : ℝ → ℂ) (Delta : ℂ) : Prop :=
  ∀ (a omega : ℝ), 0 < a → 0 < omega →
    Phi (a * omega) = Complex.exp ((-Delta) * ((Real.log a : ℝ) : ℂ)) * Phi omega

theorem dilation_mode_is_celestial_primary (E : ℝ) :
    IsCelestialPrimary (dilationEigenmode E) (⟨1 / 2, -E⟩) := by
  unfold IsCelestialPrimary dilationEigenmode
  intro a omega ha hom_pos
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt hom_pos)]
  push_cast
  have h_exp : Complex.I * (E : ℂ) - 1 / 2 = - (⟨1 / 2, -E⟩ : ℂ) := by
    apply Complex.ext <;> simp
  rw [mul_add, Complex.exp_add, h_exp]

theorem grand_apollonius_celestial_mellin_synthesis
    (E lambda omega : ℝ) (h_omega : 0 < omega) :
    ((celestialWeight lambda).re = 1 / 2) ∧
    (1 - star (celestialWeight lambda) = celestialWeight lambda) ∧
    (‖mellinScaleFreePhase E lambda omega‖ = 1) ∧
    (IsCelestialPrimary (dilationEigenmode E) (⟨1 / 2, -E⟩)) :=
  ⟨celestial_weight_re lambda,
   celestial_weight_reflection lambda,
   mellin_scale_free_norm E lambda omega,
   dilation_mode_is_celestial_primary E⟩

end
end InfoGeometry.Quantum.CelestialMellin
