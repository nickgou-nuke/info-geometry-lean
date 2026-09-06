import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.HilbertPolya

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def dilationEigenfunction (γ x : ℝ) : ℂ :=
  ((Real.rpow x (-1 / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * ((γ * Real.log x : ℝ) : ℂ))

def cylinderPhaseMode (γ τ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((γ * τ : ℝ) : ℂ))

theorem dilation_mode_factorization (γ x : ℝ) (hx : 0 < x) :
    dilationEigenfunction γ x =
    ((Real.rpow x (-1 / 2) : ℝ) : ℂ) * cylinderPhaseMode γ (Real.log x) := by
  unfold dilationEigenfunction cylinderPhaseMode
  rfl

theorem cylinder_mode_unitary (γ τ : ℝ) :
    ‖cylinderPhaseMode γ τ‖ = 1 := by
  unfold cylinderPhaseMode
  have h_re : (Complex.I * ((γ * τ : ℝ) : ℂ)).re = 0 := by
    simp [mul_re, I_re, ofReal_re, I_im, ofReal_im]
  have h_norm := Complex.norm_exp (Complex.I * ((γ * τ : ℝ) : ℂ))
  rw [h_re, Real.exp_zero] at h_norm
  exact h_norm

theorem grand_hilbert_polya_synthesis (γ x : ℝ) (hx : 0 < x) (τ : ℝ) :
    (dilationEigenfunction γ x =
     ((Real.rpow x (-1 / 2) : ℝ) : ℂ) * cylinderPhaseMode γ (Real.log x)) ∧
    (‖cylinderPhaseMode γ τ‖ = 1) :=
  ⟨dilation_mode_factorization γ x hx,
   cylinder_mode_unitary γ τ⟩
