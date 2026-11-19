/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.FiniteParitySupertrace
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Heat supertrace of a finite odd matrix

The exponential is Mathlib's convergent matrix exponential on the full finite
real matrix ring. Graded cyclicity cancels every positive even power of an odd
matrix; continuity then passes this identity through the exponential series.
Self-adjointness is not needed for this finite trace identity. The result does
not construct an infinite-dimensional heat trace or a boundary eta invariant.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiniteParitySupertrace

open scoped BigOperators Matrix.Norms.Operator
open NormedSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Positive even powers of an odd matrix have vanishing supertrace. -/
theorem supertrace_even_pow_succ (sign : n → ℝ) (Q : Matrix n n ℝ)
    (hQ : IsOdd sign Q) (k : ℕ) :
    supertrace sign ((Q ^ 2) ^ (k + 1)) = 0 := by
  have hc := supertrace_mul_comm_of_odd_left sign Q (Q ^ (2 * k + 1)) hQ
  have hl : Q * Q ^ (2 * k + 1) = (Q ^ 2) ^ (k + 1) := by
    rw [← pow_succ', ← pow_mul]
    congr 1
  have hr : Q ^ (2 * k + 1) * Q = (Q ^ 2) ^ (k + 1) := by
    rw [← pow_succ, ← pow_mul]
    congr 1
  rw [hl, hr] at hc
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp hc)

/-- The existing finite supertrace is a continuous linear functional. -/
def supertraceCLM (sign : n → ℝ) : Matrix n n ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := supertrace sign
      map_add' := fun A B => by simp [supertrace, mul_add, Matrix.trace_add]
      map_smul' := fun c A => by simp [supertrace, Matrix.trace_smul] }

@[simp]
theorem supertraceCLM_apply (sign : n → ℝ) (A : Matrix n n ℝ) :
    supertraceCLM sign A = supertrace sign A := rfl

/-- Native finite exponential cancellation, for every real scale parameter. -/
theorem supertrace_exp_smul_sq (sign : n → ℝ) (Q : Matrix n n ℝ)
    (hQ : IsOdd sign Q) (t : ℝ) :
    supertrace sign (exp (t • Q ^ 2)) = Matrix.trace (parityOperator sign) := by
  have hs := (exp_series_hasSum_exp' (𝕂 := ℝ) (t • Q ^ 2)).map
    (supertraceCLM sign) (supertraceCLM sign).continuous
  have hterm : (fun k : ℕ => supertraceCLM sign ((k.factorial : ℝ)⁻¹ •
      (t • Q ^ 2) ^ k)) =
      (fun k : ℕ => if k = 0 then Matrix.trace (parityOperator sign) else 0) := by
    funext k
    cases k with
    | zero => simp [supertrace]
    | succ k =>
      simp only [smul_pow, map_smul, supertraceCLM_apply]
      rw [supertrace_even_pow_succ sign Q hQ]
      simp
  simp only [Function.comp_def] at hs
  rw [hterm] at hs
  exact hs.unique (hasSum_ite_eq 0 (Matrix.trace (parityOperator sign)))

/-- In particular, the finite heat supertrace is independent of temperature. -/
theorem heat_supertrace_constant (sign : n → ℝ) (Q : Matrix n n ℝ)
    (hQ : IsOdd sign Q) (β₁ β₂ : ℝ) :
    supertrace sign (exp ((-β₁) • Q ^ 2)) =
      supertrace sign (exp ((-β₂) • Q ^ 2)) := by
  rw [supertrace_exp_smul_sq sign Q hQ, supertrace_exp_smul_sq sign Q hQ]

end InfoGeometry.OperatorAlgebra.FiniteParitySupertrace
