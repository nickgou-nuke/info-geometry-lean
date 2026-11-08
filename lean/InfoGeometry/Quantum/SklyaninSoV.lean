import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.SklyaninSoV

open Complex Real Matrix

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def sovWaveComponent (γ x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((γ / 2) * x : ℝ) : ℂ))

def sovWaveFunction2 (γ₁ γ₂ x₁ x₂ : ℝ) : ℂ :=
  sovWaveComponent γ₁ x₁ * sovWaveComponent γ₂ x₂

def sovBaxter1DLHS (γ x η : ℝ) : ℂ :=
  ((2 * Real.cosh ((γ / 2) * η) : ℝ) : ℂ) * sovWaveComponent γ x

def sovBaxter1DRHS (γ x η : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((((γ / 2) * x : ℝ) : ℂ) + Complex.I * (((γ / 2) * η : ℝ) : ℂ))) +
  Complex.exp (Complex.I * ((((γ / 2) * x : ℝ) : ℂ) - Complex.I * (((γ / 2) * η : ℝ) : ℂ)))

theorem sov_baxter_1d_exact (γ x η : ℝ) :
    sovBaxter1DLHS γ x η = sovBaxter1DRHS γ x η := by
  unfold sovBaxter1DLHS sovBaxter1DRHS sovWaveComponent
  have h_fwd : Complex.exp (Complex.I * ((((γ / 2 * x : ℝ) : ℂ)) + Complex.I * (((γ / 2 * η : ℝ) : ℂ)))) =
               ((Real.exp (- (γ / 2 * η)) : ℝ) : ℂ) * Complex.exp (Complex.I * (((γ / 2 * x : ℝ) : ℂ))) := by
    have h_add : Complex.I * ((((γ / 2) * x : ℝ) : ℂ) + Complex.I * (((γ / 2) * η : ℝ) : ℂ)) =
                 - (((γ / 2 * η : ℝ) : ℂ)) + Complex.I * (((γ / 2 * x : ℝ) : ℂ)) := by
      have h_I : Complex.I * Complex.I = -1 := Complex.I_mul_I
      calc Complex.I * ((((γ / 2) * x : ℝ) : ℂ) + Complex.I * (((γ / 2) * η : ℝ) : ℂ))
        _ = Complex.I * (((γ / 2 * x : ℝ) : ℂ)) + (Complex.I * Complex.I) * (((γ / 2 * η : ℝ) : ℂ)) := by ring
        _ = Complex.I * (((γ / 2 * x : ℝ) : ℂ)) + (-1) * (((γ / 2 * η : ℝ) : ℂ)) := by rw [h_I]
        _ = - (((γ / 2 * η : ℝ) : ℂ)) + Complex.I * (((γ / 2 * x : ℝ) : ℂ)) := by ring
    rw [h_add, Complex.exp_add]
    have h_exp : Complex.exp (- (((γ / 2 * η : ℝ) : ℂ))) = ((Real.exp (- (γ / 2 * η)) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [h_exp]
  have h_bwd : Complex.exp (Complex.I * ((((γ / 2 * x : ℝ) : ℂ)) - Complex.I * (((γ / 2 * η : ℝ) : ℂ)))) =
               ((Real.exp ((γ / 2 * η)) : ℝ) : ℂ) * Complex.exp (Complex.I * (((γ / 2 * x : ℝ) : ℂ))) := by
    have h_add : Complex.I * ((((γ / 2) * x : ℝ) : ℂ) - Complex.I * (((γ / 2) * η : ℝ) : ℂ)) =
                 (((γ / 2 * η : ℝ) : ℂ)) + Complex.I * (((γ / 2 * x : ℝ) : ℂ)) := by
      have h_I : Complex.I * Complex.I = -1 := Complex.I_mul_I
      calc Complex.I * ((((γ / 2) * x : ℝ) : ℂ) - Complex.I * (((γ / 2) * η : ℝ) : ℂ))
        _ = Complex.I * (((γ / 2 * x : ℝ) : ℂ)) - (Complex.I * Complex.I) * (((γ / 2 * η : ℝ) : ℂ)) := by ring
        _ = Complex.I * (((γ / 2 * x : ℝ) : ℂ)) - (-1) * (((γ / 2 * η : ℝ) : ℂ)) := by rw [h_I]
        _ = (((γ / 2 * η : ℝ) : ℂ)) + Complex.I * (((γ / 2 * x : ℝ) : ℂ)) := by ring
    rw [h_add, Complex.exp_add]
    have h_exp : Complex.exp (((γ / 2 * η : ℝ) : ℂ)) = ((Real.exp ((γ / 2 * η)) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [h_exp]
  rw [h_fwd, h_bwd]
  have h_cosh_def : Real.exp (- (γ / 2 * η)) + Real.exp (γ / 2 * η) = 2 * Real.cosh ((γ / 2) * η) := by
    have h_cosh := Real.cosh_eq ((γ / 2) * η)
    have : (γ / 2 * η) = (γ / 2) * η := by ring
    rw [this]
    linarith
  have h_sum : ((Real.exp (- (γ / 2 * η)) : ℝ) : ℂ) * Complex.exp (Complex.I * (((γ / 2 * x : ℝ) : ℂ))) +
               ((Real.exp (γ / 2 * η) : ℝ) : ℂ) * Complex.exp (Complex.I * (((γ / 2 * x : ℝ) : ℂ))) =
               (((Real.exp (- (γ / 2 * η)) + Real.exp (γ / 2 * η) : ℝ) : ℂ)) *
               Complex.exp (Complex.I * (((γ / 2 * x : ℝ) : ℂ))) := by
    push_cast
    ring
  rw [h_sum, h_cosh_def]

theorem sov_wave_component_unitary (γ x : ℝ) :
    ‖sovWaveComponent γ x‖ = 1 := by
  unfold sovWaveComponent
  have h_re : (Complex.I * (((γ / 2 * x : ℝ) : ℂ))).re = 0 := by
    simp [mul_re, I_re, ofReal_re, I_im, ofReal_im]
  have h_abs := Complex.norm_exp (Complex.I * (((γ / 2 * x : ℝ) : ℂ)))
  rw [h_re, Real.exp_zero] at h_abs
  exact h_abs

theorem sov_wavefunction2_unitary (γ₁ γ₂ x₁ x₂ : ℝ) :
    ‖sovWaveFunction2 γ₁ γ₂ x₁ x₂‖ = 1 := by
  unfold sovWaveFunction2
  rw [norm_mul, sov_wave_component_unitary γ₁ x₁, sov_wave_component_unitary γ₂ x₂, mul_one]
