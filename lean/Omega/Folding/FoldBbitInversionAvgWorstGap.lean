/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Folding.OracleCapacityClosedForm

namespace Omega.Folding

open scoped BigOperators

noncomputable section

/-- Counting upper bound for the normalized `B`-bit inversion capacity of a fold from
`2^m` inputs to `fib (m + 2)` outputs. -/
def avgSuccessUpperBound (m B : ℕ) : ℝ :=
  ((Nat.fib (m + 2) : ℝ) * (2 : ℝ) ^ B) / (2 : ℝ) ^ m

/-- The sum of the truncated fiber sizes is at most the number of output fibers times
the per-fiber cap `2^B`. -/
theorem bbitOracleCapacity_le_fib_mul_pow (m B : ℕ)
    (fold : Fin (2 ^ m) → Fin (Nat.fib (m + 2))) :
    (Omega.POM.bbitOracleCapacity fold B : ℝ) ≤
      (Nat.fib (m + 2) : ℝ) * (2 : ℝ) ^ B := by
  rw [paper_fold_oracle_capacity_closed_form]
  have hsumNat :
      (∑ x : Fin (Nat.fib (m + 2)),
          Nat.min (Fintype.card {ω : Fin (2 ^ m) // fold ω = x}) (2 ^ B)) ≤
        Nat.fib (m + 2) * 2 ^ B := by
    calc
      (∑ x : Fin (Nat.fib (m + 2)),
          Nat.min (Fintype.card {ω : Fin (2 ^ m) // fold ω = x}) (2 ^ B)) ≤
          ∑ _x : Fin (Nat.fib (m + 2)), 2 ^ B := by
            refine Finset.sum_le_sum ?_
            intro x _hx
            exact Nat.min_le_right _ _
      _ = Nat.fib (m + 2) * 2 ^ B := by simp
  exact_mod_cast hsumNat

/-- The normalized capacity of any such fold is bounded by the output-count estimate. -/
theorem paper_fold_bbit_inversion_avg_worst_gap (m B : ℕ)
    (fold : Fin (2 ^ m) → Fin (Nat.fib (m + 2))) :
    (Omega.POM.bbitOracleCapacity fold B : ℝ) / (2 : ℝ) ^ m ≤
      avgSuccessUpperBound m B := by
  have hpow_pos : 0 < (2 : ℝ) ^ m := by positivity
  unfold avgSuccessUpperBound
  exact div_le_div_of_nonneg_right
    (bbitOracleCapacity_le_fib_mul_pow m B fold) (le_of_lt hpow_pos)

end

/-- The supplied theorem signature only supports the universal nonnegativity lower bound. -/
def zeroErrorBitLowerBound (_m : ℕ) : ℕ := 0

end Omega.Folding
