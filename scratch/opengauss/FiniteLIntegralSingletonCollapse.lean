/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Finite-carrier lintegral collapse

If a nonnegative function on a finite measurable-singleton carrier vanishes
away from one point, its lintegral is its value at that point times the
measure of the singleton.
-/

namespace OpenGaussScratch.FiniteLIntegralSingletonCollapse

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype α] (μ : Measure α)

/-- Collapse a finite-carrier lintegral supported at one point to its singleton
mass. -/
theorem lintegral_eq_singleton_of_eq_zero_off
    (f : α → ℝ≥0∞) (a : α) (hzero : ∀ x : α, x ≠ a → f x = 0) :
    ∫⁻ x, f x ∂μ = f a * μ {a} := by
  rw [lintegral_fintype]
  exact Finset.sum_eq_single_of_mem a (Finset.mem_univ a) (by
    intro x _ hxa
    simp [hzero x hxa])

end OpenGaussScratch.FiniteLIntegralSingletonCollapse

#print axioms OpenGaussScratch.FiniteLIntegralSingletonCollapse.lintegral_eq_singleton_of_eq_zero_off
