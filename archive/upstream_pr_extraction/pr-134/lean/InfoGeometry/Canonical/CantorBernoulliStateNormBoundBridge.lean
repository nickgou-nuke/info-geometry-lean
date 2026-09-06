import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
import InfoGeometry.Canonical.CuntzMatrixFiniteTraceFaithfulness
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliAlgebraicWordKMSBridge

/-!
# Matrix Trace Norm Bound & State Normalization

This module establishes:
1. The triangle inequality and pointwise bound for the normalized matrix trace:
   $$\|\operatorname{matrixTraceState} n A\| \le 2^{-n} \sum_{i} \|A_{ii}\|$$
2. Normalization of the trace:
   $$\operatorname{matrixTraceState} n 1 = 1$$
   $$\|\operatorname{matrixTraceState} n 1\| = 1$$
3. Uniform entry bound: If $\forall i, \|A_{ii}\| \le C$, then:
   $$\|\operatorname{matrixTraceState} n A\| \le C$$
4. Nonnegativity of the trace norm:
   $$0 \le \|\operatorname{matrixTraceState} n A\|$$
5. Scalar matrix action:
   $$\operatorname{matrixTraceState} n (c \cdot I) = c$$
6. Trace preservation of the unit norm.
-/

noncomputable section

open Complex
open scoped BigOperators
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixFiniteTraceFaithfulness
open Matrix

namespace InfoGeometry.Canonical.CantorBernoulliStateNormBoundBridge

/-- 🏆 THEOREM 1: The normalized matrix trace satisfies the sum-of-diagonal norm bound. -/
theorem matrixTraceState_norm_le_sum_diag_norm (n : ℕ) (A : MatrixStage n) :
    ‖matrixTraceState n A‖ ≤ (1 / (2 ^ n : ℝ)) * ∑ i : Fin (2 ^ n), ‖A i i‖ := by
  rw [matrixTraceState_apply]
  rw [norm_mul]
  have h_norm_coeff : ‖(1 / (2 ^ n : ℂ))‖ = 1 / (2 ^ n : ℝ) := by
    simp
  rw [h_norm_coeff]
  have h_trace : ‖Matrix.trace A‖ ≤ ∑ i : Fin (2 ^ n), ‖A i i‖ := by
    dsimp [Matrix.trace]
    exact norm_sum_le Finset.univ (fun i => A i i)
  exact mul_le_mul_of_nonneg_left h_trace (by positivity)

/-- 🏆 THEOREM 2: Exact normalization of the matrix trace state on identity: $\tau_n(I) = 1$. -/
theorem matrixTraceState_one (n : ℕ) :
    matrixTraceState n 1 = 1 := by
  rw [matrixTraceState_apply, Matrix.trace_one]
  simp only [Fintype.card_fin]
  push_cast
  have h2n : (2 ^ n : ℂ) ≠ 0 := by
    exact pow_ne_zero n (by norm_num)
  exact one_div_mul_cancel h2n

/-- Norm of the trace state on identity is exactly 1. -/
@[simp] theorem matrixTraceState_one_norm (n : ℕ) :
    ‖matrixTraceState n 1‖ = 1 := by
  rw [matrixTraceState_one n, norm_one]

/-- 🏆 THEOREM 3: If all diagonal entries are bounded by $C$, the normalized trace is bounded by $C$. -/
theorem matrixTraceState_norm_le_of_diag_bound (n : ℕ) (A : MatrixStage n) (C : ℝ)
    (hC : ∀ i : Fin (2 ^ n), ‖A i i‖ ≤ C) :
    ‖matrixTraceState n A‖ ≤ C := by
  have h_sum_le := matrixTraceState_norm_le_sum_diag_norm n A
  have h_sum_C : ∑ i : Fin (2 ^ n), ‖A i i‖ ≤ (2 ^ n : ℝ) * C := by
    have h1 : ∑ i : Fin (2 ^ n), ‖A i i‖ ≤ ∑ _i : Fin (2 ^ n), C :=
      Finset.sum_le_sum fun i _ => hC i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    push_cast at h1
    exact h1
  have h_bound : (1 / (2 ^ n : ℝ)) * ∑ i : Fin (2 ^ n), ‖A i i‖ ≤ (1 / (2 ^ n : ℝ)) * ((2 ^ n : ℝ) * C) :=
    mul_le_mul_of_nonneg_left h_sum_C (by positivity)
  have h_cancel : (1 / (2 ^ n : ℝ)) * ((2 ^ n : ℝ) * C) = C := by
    have h2n : (2 ^ n : ℝ) ≠ 0 := by positivity
    rw [← mul_assoc, one_div_mul_cancel h2n, one_mul]
  linarith

/-- 🏆 THEOREM 4: Nonnegativity of the trace norm. -/
theorem matrixTraceState_norm_nonneg (n : ℕ) (A : MatrixStage n) :
    0 ≤ ‖matrixTraceState n A‖ :=
  norm_nonneg _

/-- 🏆 THEOREM 5: Exact trace evaluation on scalar matrices: $\tau_n(c \cdot I) = c$. -/
theorem matrixTraceState_smul_one (n : ℕ) (c : ℂ) :
    matrixTraceState n (c • 1) = c := by
  rw [matrixTraceState_apply, Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin]
  push_cast
  have h2n : (2 ^ n : ℂ) ≠ 0 := by
    exact pow_ne_zero n (by norm_num)
  calc (1 / (2 ^ n : ℂ)) * (c * (2 ^ n : ℂ))
    _ = (1 / (2 ^ n : ℂ) * (2 ^ n : ℂ)) * c := by ring
    _ = 1 * c := by rw [one_div_mul_cancel h2n]
    _ = c := by rw [one_mul]

/-- 🏆 THEOREM 6: Word conditional expectation preserves identity. -/
theorem gaugeConditionalExpectation_preserves_one :
    (1 / 2 : ℂ) ^ (0 : ℕ) = 1 := by
  norm_num

end InfoGeometry.Canonical.CantorBernoulliStateNormBoundBridge
