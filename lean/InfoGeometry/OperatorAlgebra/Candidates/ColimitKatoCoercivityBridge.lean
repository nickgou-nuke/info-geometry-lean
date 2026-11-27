/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.Candidates.ColimitKatoContraction

/-!
# Left regular action of the algebraic Fock-colimit operator ring

`FockInfinity` is an algebraic direct limit. Its endomorphism ring is a genuine
noncommutative operator algebra, but the carrier has no normed Hilbert
completion in this development. This file records the algebraic left regular
representation; it does not infer analytic coercivity or operator-norm bounds.
-/

namespace InfoGeometry.OperatorAlgebra.Candidates.ColimitKatoCoercivityBridge

open InfoGeometry.OperatorAlgebra.Candidates.ColimitKatoContraction
open InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

noncomputable section

/-- Left multiplication by an operator in the algebraic Fock-colimit
endomorphism ring, acting on that noncommutative operator ring. -/
def leftRegular (a : ColimitOperator) : ColimitOperator →ₗ[ℝ] ColimitOperator :=
  LinearMap.mulLeft ℝ a

@[simp]
theorem leftRegular_apply (a x : ColimitOperator) : leftRegular a x = a * x := rfl

/-- The left regular action preserves the order of noncommutative composition. -/
theorem leftRegular_mul (a b : ColimitOperator) :
    leftRegular (a * b) = (leftRegular a).comp (leftRegular b) := by
  ext x
  simp [leftRegular]

@[simp]
theorem leftRegular_one :
    leftRegular (1 : ColimitOperator) = LinearMap.id := by
  ext x
  simp [leftRegular]

end
end InfoGeometry.OperatorAlgebra.Candidates.ColimitKatoCoercivityBridge
