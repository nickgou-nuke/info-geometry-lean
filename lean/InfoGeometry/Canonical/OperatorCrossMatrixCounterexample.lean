/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness

/-!
# Matrix witness for the non-alternating operator-valued cross product

The canonical self-cross theorem identifies its three coordinates with
coefficient commutators. This file instantiates the criterion with noncommuting
off-diagonal operators in `M₂(ℝ)`.
-/

namespace InfoGeometry.Canonical.OperatorCrossMatrixCounterexample

open InfoGeometry.Canonical
open InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness

abbrev OperatorCoeff := Matrix (Fin 2) (Fin 2) ℝ

def operatorVector : OperatorVector OperatorCoeff := fun i =>
  if i = 1 then matrixUnit01 else if i = 2 then matrixUnit10 else 0

/-- The self-cross is nonzero because its first component is the commutator
of the two off-diagonal matrix operators. -/
theorem operatorCross_self_ne_zero :
    operatorCross operatorVector operatorVector ≠ 0 := by
  intro h
  have hcomm := (operatorCross_self_eq_zero_iff operatorVector).mp h
  apply matrix_units_noncommute
  simpa [operatorVector] using hcomm.1

end InfoGeometry.Canonical.OperatorCrossMatrixCounterexample
