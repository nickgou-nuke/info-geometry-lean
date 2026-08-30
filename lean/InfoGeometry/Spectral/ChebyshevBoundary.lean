import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Spectral.ChebyshevBoundary

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def criticalZero (γ : ℝ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * (γ : ℂ)

def spectralInterferenceMode (x : ℝ) (γ : ℝ) : ℂ :=
  Complex.cpow (x : ℂ) (criticalZero γ) / (criticalZero γ)

theorem critical_zero_norm_sq (γ : ℝ) :
    Complex.normSq (criticalZero γ) = 1 / 4 + γ ^ 2 := by
  unfold criticalZero
  simp [Complex.normSq, add_re, ofReal_re, I_re, mul_re, ofReal_im, I_im]
  ring

theorem critical_zero_ne_zero (γ : ℝ) :
    criticalZero γ ≠ 0 := by
  intro h
  have h_re : (criticalZero γ).re = 0 := by rw [h]; rfl
  unfold criticalZero at h_re
  dsimp [add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im] at h_re
  norm_num at h_re

theorem spectral_mode_factorization (x γ : ℝ) (hx : 0 < x) :
    Complex.exp (criticalZero γ * ((Real.log x : ℝ) : ℂ)) =
    ((Real.sqrt x : ℝ) : ℂ) * Complex.exp (Complex.I * ((γ * Real.log x : ℝ) : ℂ)) := by
  unfold criticalZero
  have h_split : ((1 / 2 : ℂ) + Complex.I * (γ : ℂ)) * ((Real.log x : ℝ) : ℂ) =
                 (((1 / 2 * Real.log x : ℝ) : ℂ) + Complex.I * ((γ * Real.log x : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [h_split, Complex.exp_add]
  have h_sqrt : Complex.exp (((1 / 2 * Real.log x : ℝ) : ℂ)) = ((Real.sqrt x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp]
    congr 1
    rw [mul_comm, Real.exp_mul, Real.exp_log hx]
    exact (Real.sqrt_eq_rpow x).symm
  rw [h_sqrt]

theorem grand_chebyshev_boundary_synthesis (x γ : ℝ) (hx : 0 < x) :
    (Complex.normSq (criticalZero γ) = 1 / 4 + γ ^ 2) ∧
    (criticalZero γ ≠ 0) ∧
    (Complex.exp (criticalZero γ * ((Real.log x : ℝ) : ℂ)) =
     ((Real.sqrt x : ℝ) : ℂ) * Complex.exp (Complex.I * ((γ * Real.log x : ℝ) : ℂ))) :=
  ⟨critical_zero_norm_sq γ,
   critical_zero_ne_zero γ,
   spectral_mode_factorization x γ hx⟩
