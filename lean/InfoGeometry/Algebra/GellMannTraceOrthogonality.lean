import Mathlib
import InfoGeometry.Algebra.SpecialUnitary
import InfoGeometry.Algebra.GellMannBasis

open Matrix
open InfoGeometry.Algebra
open InfoGeometry.Algebra.GellMann

noncomputable section

set_option linter.unusedSimpArgs false

namespace InfoGeometry.Algebra.GellMannTraceOrthogonality

/-!
# Gell-Mann Trace Orthogonality

This module proves the exact trace orthogonality relations for the 8 Gell-Mann generators
of $\mathfrak{su}(3)$:
$$\text{Tr}(\lambda_a \cdot \lambda_b) = -2 \delta_{ab}$$
-/

/-- Helper for complex square root reduction of $(\sqrt{3})^2 = 3$ in trace expressions. -/
theorem csqrt3_sq : (Real.sqrt 3 : ℂ) ^ 2 = (3 : ℂ) := by
  have h_r : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  exact_mod_cast h_r

theorem gellmann_trace_orthogonality (a b : Fin 8) :
    Matrix.trace ((gellMann a).val * (gellMann b).val) = -2 * (if a = b then 1 else 0 : ℂ) := by
  have h_sq3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = (3 : ℂ) := by
    have h_r : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    exact_mod_cast h_r
  have h_ne : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    norm_cast
    exact Real.sqrt_ne_zero'.mpr (by norm_num)
  fin_cases a <;> fin_cases b <;> dsimp [gellMann, gellMannArray] <;> simp [gellMann1, gellMann2, gellMann3, gellMann4, gellMann5, gellMann6, gellMann7, gellMann8, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three] <;> try ring_nf <;> (try field_simp [h_ne]; try rw [Complex.I_sq, h_sq3]; try ring_nf)

end InfoGeometry.Algebra.GellMannTraceOrthogonality
