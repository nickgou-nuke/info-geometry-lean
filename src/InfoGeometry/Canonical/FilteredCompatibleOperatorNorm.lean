/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredCompatibleOperatorColimit

/-!
# Norm bounds for the existing completed compatible operator

The actual algebraic pointwise bound persists under completion by density.
A nonnegative family bound then bounds the operator norm. No new operator,
carrier, or stagewise bound premise is introduced.
-/
noncomputable section

namespace InfoGeometry.Canonical.FilteredCompatibleOperatorColimit

open FilteredIsometricInnerProductColimit
open FilteredIsometricInnerProductDirectLimit
open FilteredIsometricHilbertCompletion

universe u
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
variable (E : I → Type u) [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, InnerProductSpace ℂ (E i)]
variable (sys : IsometricDirectSystem E) (T : CompatibleOperatorFamily E sys)

/-- The family pointwise bound extends to every vector of the existing completion. -/
theorem completedOperator_norm_apply_le (x : HilbertDirectLimit E sys) :
    ‖completedOperator E sys T x‖ ≤ T.bound * ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le (completedOperator E sys T).continuous.norm
      (continuous_const.mul continuous_norm)
  | ih x =>
    simpa only [completedOperator, ContinuousLinearMap.completion_apply_coe,
      UniformSpace.Completion.norm_coe, algebraicOperatorCLM_apply] using
      algebraicOperator_norm_le E sys T x

/-- Nonnegativity is explicit: the native family stores an unrestricted real bound. -/
theorem completedOperator_norm_le (hbound : 0 ≤ T.bound) :
    ‖completedOperator E sys T‖ ≤ T.bound :=
  ContinuousLinearMap.opNorm_le_bound _ hbound (completedOperator_norm_apply_le E sys T)

end InfoGeometry.Canonical.FilteredCompatibleOperatorColimit
