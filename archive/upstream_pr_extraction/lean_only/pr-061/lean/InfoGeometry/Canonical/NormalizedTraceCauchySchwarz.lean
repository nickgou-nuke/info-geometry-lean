import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option linter.unusedSectionVars false

open Matrix BigOperators

namespace NormalizedTraceCauchySchwarz

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Normalized trace operator for real n × n matrices with scale factor d -/
noncomputable def normalizedTrace (d : ℝ) (M : Matrix n n ℝ) : ℝ :=
  (1 / d) * trace M

/-- Lemma 1: Trace of Aᵀ * B as double sum of entrywise products ∑ i j, A j i * B j i -/
lemma trace_transpose_mul (A B : Matrix n n ℝ) :
    trace (A.transpose * B) = ∑ i : n, ∑ j : n, A j i * B j i := by
  dsimp [trace, mul_apply, transpose]

/-- Lemma 2: Non-negativity of trace(Aᵀ * A) ≥ 0 -/
lemma trace_transpose_mul_self_nonneg (A : Matrix n n ℝ) :
    0 ≤ trace (A.transpose * A) := by
  rw [trace_transpose_mul]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_self_nonneg (A j i)

/-- Lemma 3: Algebraic Discriminant Non-negativity
    If a t² - 2 b t + c ≥ 0 for all t ∈ ℝ and a ≥ 0, then b² ≤ a c. -/
lemma quadratic_nonneg_discrim {a b c : ℝ} (ha : 0 ≤ a)
    (h : ∀ t : ℝ, 0 ≤ a * t^2 - 2 * b * t + c) :
    b^2 ≤ a * c := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · have hb : b = 0 := by
      by_contra hb
      have h1 := h ((c + 1) / (2 * b))
      have hb_ne : 2 * b ≠ 0 := mul_ne_zero (by norm_num) hb
      have h_eval : 0 * ((c + 1) / (2 * b))^2 - 2 * b * ((c + 1) / (2 * b)) + c = -1 := by
        calc 0 * ((c + 1) / (2 * b))^2 - 2 * b * ((c + 1) / (2 * b)) + c
          _ = - (2 * b * (c + 1) / (2 * b)) + c := by ring
          _ = - (c + 1) + c := by rw [mul_div_cancel_left₀ (c + 1) hb_ne]
          _ = -1 := by ring
      rw [h_eval] at h1
      linarith
    subst hb
    simp
  · have h1 := h (b / a)
    have ha_ne : a ≠ 0 := ne_of_gt ha_pos
    have h2 : 0 ≤ (a * c - b^2) / a := by
      calc 0 ≤ a * (b / a)^2 - 2 * b * (b / a) + c := h1
        _ = (a * c - b^2) / a := by field_simp; ring
    have h_mul : 0 ≤ ((a * c - b^2) / a) * a := mul_nonneg h2 (le_of_lt ha_pos)
    rw [div_mul_cancel₀ _ ha_ne] at h_mul
    linarith

/-- Theorem: Standard Matrix Trace Cauchy-Schwarz (Tr(Aᵀ B))² ≤ Tr(Aᵀ A) * Tr(Bᵀ B) -/
theorem trace_cauchy_schwarz (A B : Matrix n n ℝ) :
    (trace (A.transpose * B))^2 ≤ trace (A.transpose * A) * trace (B.transpose * B) := by
  have ha : 0 ≤ trace (A.transpose * A) := trace_transpose_mul_self_nonneg A
  apply quadratic_nonneg_discrim ha
  intro t
  have h_nonneg := trace_transpose_mul_self_nonneg (t • A - B)
  have h_eq : trace (A.transpose * A) * t^2 - 2 * trace (A.transpose * B) * t + trace (B.transpose * B) =
      trace ((t • A - B).transpose * (t • A - B)) := by
    rw [trace_transpose_mul (t • A - B) (t • A - B), trace_transpose_mul A A, trace_transpose_mul A B, trace_transpose_mul B B]
    dsimp [sub_apply, smul_apply]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    congr 1
    ext i
    congr 1
    ext j
    ring
  rw [h_eq]
  exact h_nonneg

/-- 🏆 THEOREM: Tracial Cauchy-Schwarz Inequality for Normalized Trace
    Proves (τ_d(Aᵀ * B))² ≤ τ_d(Aᵀ * A) * τ_d(Bᵀ * B) for d > 0. -/
theorem normalizedTrace_cauchy_schwarz (d : ℝ) (hd : 0 < d) (A B : Matrix n n ℝ) :
    (normalizedTrace d (A.transpose * B))^2 ≤
    normalizedTrace d (A.transpose * A) * normalizedTrace d (B.transpose * B) := by
  dsimp [normalizedTrace]
  have h_cs := trace_cauchy_schwarz A B
  have hd_sq_pos : 0 ≤ (1 / d)^2 := sq_nonneg (1 / d)
  calc ((1 / d) * trace (A.transpose * B))^2
    _ = (1 / d)^2 * (trace (A.transpose * B))^2 := by ring
    _ ≤ (1 / d)^2 * (trace (A.transpose * A) * trace (B.transpose * B)) := mul_le_mul_of_nonneg_left h_cs hd_sq_pos
    _ = ((1 / d) * trace (A.transpose * A)) * ((1 / d) * trace (B.transpose * B)) := by ring

end NormalizedTraceCauchySchwarz
