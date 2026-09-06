import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

open Matrix

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

noncomputable section

def QuaternionicCoordinates := Fin 4 → ℝ

def FisherRaoMetric (q : QuaternionicCoordinates) : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 : Matrix (Fin 4) (Fin 4) ℝ)

theorem FisherRaoMetric_is_positive_definite (q : QuaternionicCoordinates) (v : Fin 4 → ℝ) :
    (v = 0) ∨ (dotProduct v (mulVec (FisherRaoMetric q) v) > 0) := by
  by_cases h : v = 0
  · left; exact h
  · right
    dsimp [FisherRaoMetric]
    rw [Matrix.one_mulVec]
    have h1 : dotProduct v v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by
      dsimp [dotProduct]
      rw [Fin.sum_univ_four]
      ring
    rw [h1]
    by_cases h0 : v 0 = 0
    · by_cases h1 : v 1 = 0
      · by_cases h2 : v 2 = 0
        · by_cases h3 : v 3 = 0
          · exfalso
            apply h
            ext i
            match i with
            | 0 => exact h0
            | 1 => exact h1
            | 2 => exact h2
            | 3 => exact h3
          · have hsq : 0 < v 3 ^ 2 := sq_pos_of_ne_zero h3
            rw [h0, h1, h2]; ring_nf; exact hsq
        · have hsq : 0 < v 2 ^ 2 := sq_pos_of_ne_zero h2
          have hn3 : 0 ≤ v 3 ^ 2 := sq_nonneg (v 3)
          rw [h0, h1]; ring_nf; linarith
      · have hsq : 0 < v 1 ^ 2 := sq_pos_of_ne_zero h1
        have hn2 : 0 ≤ v 2 ^ 2 := sq_nonneg (v 2)
        have hn3 : 0 ≤ v 3 ^ 2 := sq_nonneg (v 3)
        rw [h0]; ring_nf; linarith
    · have hsq : 0 < v 0 ^ 2 := sq_pos_of_ne_zero h0
      have hn1 : 0 ≤ v 1 ^ 2 := sq_nonneg (v 1)
      have hn2 : 0 ≤ v 2 ^ 2 := sq_nonneg (v 2)
      have hn3 : 0 ≤ v 3 ^ 2 := sq_nonneg (v 3)
      linarith

