import Mathlib.Analysis.SpecialFunctions.Complex.Log
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace InfoGeometry.Spectral.ChebyshevBoundary

noncomputable section

def criticalZero (γ : ℝ) : ℂ := ⟨1 / 2, γ⟩

theorem criticalZero_normSq (γ : ℝ) :
    Complex.normSq (criticalZero γ) = 1 / 4 + γ ^ 2 := by
  simp [criticalZero, Complex.normSq]
  ring

theorem criticalZero_ne_zero (γ : ℝ) : criticalZero γ ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [criticalZero] at this

theorem criticalZero_mellin_factor (x γ : ℝ) (hx : 0 < x) :
    Complex.exp (criticalZero γ * ((Real.log x : ℝ) : ℂ)) =
      ((Real.sqrt x : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((γ * Real.log x : ℝ) : ℂ)) := by
  rw [show criticalZero γ * ((Real.log x : ℝ) : ℂ) =
      ((1 / 2 : ℝ) * Real.log x : ℝ) +
        Complex.I * ((γ * Real.log x : ℝ) : ℂ) by
        apply Complex.ext <;> simp [criticalZero] <;> ring]
  rw [Complex.exp_add]
  have hroot : Real.exp (Real.log x / 2) = Real.sqrt x := by
    have h := Real.rpow_def_of_pos hx (1 / 2 : ℝ)
    calc
      Real.exp (Real.log x / 2) = Real.exp (Real.log x * (1 / 2 : ℝ)) := by
        congr 1 <;> ring
      _ = x ^ (1 / 2 : ℝ) := h.symm
      _ = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
  rw [show (1 / 2 : ℝ) * Real.log x = Real.log x / 2 by ring]
  rw [← Complex.ofReal_exp]
  rw [hroot]

theorem grand_chebyshev_boundary_synthesis (x γ : ℝ) (hx : 0 < x) :
    (Complex.normSq (criticalZero γ) = 1 / 4 + γ ^ 2) ∧
    (criticalZero γ ≠ 0) ∧
    (Complex.exp (criticalZero γ * ((Real.log x : ℝ) : ℂ)) =
      ((Real.sqrt x : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((γ * Real.log x : ℝ) : ℂ))) :=
  ⟨criticalZero_normSq γ, criticalZero_ne_zero γ,
    criticalZero_mellin_factor x γ hx⟩

end
end InfoGeometry.Spectral.ChebyshevBoundary
