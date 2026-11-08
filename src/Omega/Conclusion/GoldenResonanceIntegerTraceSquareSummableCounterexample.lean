/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.PSeries
import Mathlib.Tactic
import Omega.Conclusion.GoldenResonanceIntegerTraceNotL2

namespace Omega.Conclusion

open Omega.Conclusion

/-- Coefficient-level square-summability model, separate from the source
owner's extra zero-mode requirement. -/
def goldenTraceSquareSummableCoefficientModel : Prop :=
  ∃ coeff : ℤ → ℝ,
    (∀ n, coeff n =
      conclusion_golden_resonance_integer_trace_not_l2_integer_trace n) ∧
      Summable (fun n => coeff n ^ 2)

/-- The displayed integer trace has square-summable coefficients on `ℤ`.
Consequently, pointwise positivity of its square profile is not a logarithmic
divergence or a non-`L²` criterion. -/
theorem golden_resonance_integer_trace_square_summable :
    Summable (fun n : ℤ =>
      conclusion_golden_resonance_integer_trace_not_l2_integer_trace n ^ 2) := by
  have hBase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hNat : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    simpa [Nat.cast_add] using
      (summable_nat_add_iff
        (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hBase
  have hNatShift : Summable (fun n : ℕ =>
      (1 : ℝ) / (((1 + n : ℕ) : ℝ) + 1) ^ 2) := by
    exact hNat.comp_injective (add_right_injective 1)
  have hpos : Summable (fun n : ℕ =>
      conclusion_golden_resonance_integer_trace_not_l2_integer_trace (n : ℤ) ^ 2) := by
    simpa [conclusion_golden_resonance_integer_trace_not_l2_integer_trace] using hNat
  have hneg : Summable (fun n : ℕ =>
      conclusion_golden_resonance_integer_trace_not_l2_integer_trace (Int.negSucc n) ^ 2) := by
    simpa [conclusion_golden_resonance_integer_trace_not_l2_integer_trace,
      Nat.cast_add, add_comm, add_left_comm, add_assoc] using hNatShift
  exact Summable.of_nat_of_neg_add_one hpos hneg

/-- The actual trace itself is a square-summable coefficient model. -/
theorem golden_resonance_integer_trace_has_square_summable_model :
    goldenTraceSquareSummableCoefficientModel := by
  exact ⟨conclusion_golden_resonance_integer_trace_not_l2_integer_trace,
    fun _ => rfl, golden_resonance_integer_trace_square_summable⟩

/-- The source package's no-realization conclusion is forced by its added
zero-mode equation: the specified trace has value one at zero. -/
theorem golden_resonance_integer_trace_zero_mode_is_one :
    conclusion_golden_resonance_integer_trace_not_l2_integer_trace 0 = 1 := by
  norm_num [conclusion_golden_resonance_integer_trace_not_l2_integer_trace]

end Omega.Conclusion
