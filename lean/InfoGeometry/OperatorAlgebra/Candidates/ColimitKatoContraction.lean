/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
import Mathlib

/-!
# Operator algebra on the algebraic Clifford-Fock colimit

The algebraic Fock colimit is a module, not a normed ring.  Accordingly this
file works in its genuine operator algebra `Module.End ℝ FockInfinity` and
states only algebraic composition laws.  Analytic Kato or operator-norm
estimates require a separately constructed topology or completion.
-/

namespace InfoGeometry.OperatorAlgebra.Candidates.ColimitKatoContraction

open InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

noncomputable section

/-- The noncommutative ring of linear operators on the algebraic Fock colimit. -/
abbrev ColimitOperator := Module.End ℝ FockInfinity

/-- Composition in the operator algebra, written as multiplication. -/
def compose (S T : ColimitOperator) : ColimitOperator := S * T

@[simp]
theorem compose_apply (S T : ColimitOperator) (x : FockInfinity) :
    compose S T x = S (T x) := rfl

theorem compose_assoc (R S T : ColimitOperator) :
    compose (compose R S) T = compose R (compose S T) := by
  exact mul_assoc R S T

theorem compose_one_left (T : ColimitOperator) : compose 1 T = T := by
  exact one_mul T

theorem compose_one_right (T : ColimitOperator) : compose T 1 = T := by
  exact mul_one T

end
end InfoGeometry.OperatorAlgebra.Candidates.ColimitKatoContraction
