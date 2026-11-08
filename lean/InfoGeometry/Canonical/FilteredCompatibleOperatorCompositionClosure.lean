/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.FilteredCompatibleOperatorColimit

noncomputable section

namespace InfoGeometry.Canonical.FilteredCompatibleOperatorColimit

open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit
open InfoGeometry.Canonical.FilteredIsometricInnerProductDirectLimit
open InfoGeometry.Canonical.FilteredIsometricHilbertCompletion

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (E : I → Type u)
variable [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, InnerProductSpace ℂ (E i)]
variable (sys : IsometricDirectSystem E)

/-- Composition of compatible bounded stage operators, under the explicit
nonnegativity hypothesis needed to propagate the stated bound. -/
def composeFamilies
    (S T : CompatibleOperatorFamily E sys)
    (hS : 0 ≤ S.bound) :
    CompatibleOperatorFamily E sys where
  op := fun i => (S.op i).comp (T.op i)
  intertwines := by
    intro i j hij x
    change sys.map hij (S.op i (T.op i x)) = S.op j (T.op j (sys.map hij x))
    rw [S.intertwines hij (T.op i x), T.intertwines hij x]
  bound := S.bound * T.bound
  norm_le := by
    intro i x
    calc
      ‖(S.op i) ((T.op i) x)‖ ≤ S.bound * ‖(T.op i x)‖ :=
        S.norm_le i (T.op i x)
      _ ≤ S.bound * (T.bound * ‖x‖) := by
        exact mul_le_mul_of_nonneg_left (T.norm_le i x) hS
      _ = (S.bound * T.bound) * ‖x‖ := by ring

/-- The descended algebraic operator of a composed compatible family is the
composition of the two descended algebraic operators. -/
theorem algebraicOperator_composeFamilies
    (S T : CompatibleOperatorFamily E sys)
    (hS : 0 ≤ S.bound) (z : RealDirectLimit E sys) :
    algebraicOperator E sys (composeFamilies E sys S T hS) z =
      algebraicOperator E sys S (algebraicOperator E sys T z) := by
  induction z using Module.DirectLimit.induction_on with
  | ih i x =>
      change
        algebraicOperator E sys (composeFamilies E sys S T hS)
            (stageToDirectLimitLinearMap E sys i x) =
          algebraicOperator E sys S
            (algebraicOperator E sys T
              (stageToDirectLimitLinearMap E sys i x))
      rw [algebraicOperator_of, algebraicOperator_of, algebraicOperator_of]
      rfl

end InfoGeometry.Canonical.FilteredCompatibleOperatorColimit
