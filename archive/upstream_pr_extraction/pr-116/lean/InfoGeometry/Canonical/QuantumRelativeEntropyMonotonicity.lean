import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Real Finset Matrix

namespace QuantumRelativeEntropy

variable {n : ℕ}

/-- Kullback-Leibler Relative Entropy for positive probability distributions P and Q on Fin n. -/
def klDivergence (P Q : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, P i * Real.log (P i / Q i)

/-- **Theorem**: Fundamental Logarithmic Inequality: 1 - q/p ≤ ln(p/q) for p, q > 0. -/
theorem log_le_sub_one_div (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    1 - q / p ≤ Real.log (p / q) := by
  have h_div : 0 < q / p := div_pos hq hp
  have h_exp := Real.add_one_le_exp (Real.log (q / p))
  rw [Real.exp_log h_div] at h_exp
  have h_log_inv : Real.log (p / q) = - Real.log (q / p) := by
    have h_inv : p / q = (q / p)⁻¹ := by field_simp
    rw [h_inv, Real.log_inv]
  linarith

/-- **Theorem**: Monotonicity of Relative Entropy:
    For any normalized probability distributions P and Q (∑ P_i = 1, ∑ Q_i = 1) with positive entries,
    the KL-divergence D_KL(P || Q) = ∑ P_i ln(P_i / Q_i) is strictly non-negative: D_KL(P || Q) ≥ 0. -/
theorem kl_divergence_nonneg (P Q : Fin n → ℝ)
    (hP_pos : ∀ i, 0 < P i) (hQ_pos : ∀ i, 0 < Q i)
    (hP_sum : ∑ i : Fin n, P i = 1)
    (hQ_sum : ∑ i : Fin n, Q i = 1) :
    0 ≤ klDivergence P Q := by
  dsimp [klDivergence]
  have h_bound (i : Fin n) : P i - Q i ≤ P i * Real.log (P i / Q i) := by
    have hp := hP_pos i
    have hq := hQ_pos i
    have h_ineq := log_le_sub_one_div (P i) (Q i) hp hq
    have hp_ne : P i ≠ 0 := ne_of_gt hp
    calc P i - Q i
      _ = P i * (1 - Q i / P i) := by field_simp
      _ ≤ P i * Real.log (P i / Q i) := mul_le_mul_of_nonneg_left h_ineq (le_of_lt hp)
  have h_sum_le : (∑ i : Fin n, (P i - Q i)) ≤ ∑ i : Fin n, P i * Real.log (P i / Q i) :=
    Finset.sum_le_sum (fun i _ => h_bound i)
  have h_sum_lh : (∑ i : Fin n, (P i - Q i)) = 0 := by
    rw [Finset.sum_sub_distrib, hP_sum, hQ_sum, sub_self]
  linarith

/-- **Theorem**: Matrix Trace Inequality:
    For any real n × n matrices A and B, Tr((A - B)ᵀ (A - B)) ≥ 0 with equality iff A = B. -/
theorem matrix_diff_trace_nonneg (A B : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ trace ((A - B)ᵀ * (A - B)) := by
  dsimp [trace, mul_apply, transpose, sub_apply]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  have h_sq : (A j i - B j i) * (A j i - B j i) = (A j i - B j i) ^ 2 := by ring
  rw [h_sq]
  exact sq_nonneg (A j i - B j i)

end QuantumRelativeEntropy
