/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.MatrixSquareNegOne
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Clifford.Cl55InternalComplex
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Three-by-three roots of minus one over native real coefficient algebras

The existing `Krein.clockAxis` acts on the actual real Hilbert product
`DoubledSpace E = WithLp 2 (E × E)` by `(x, y) ↦ (-y, x)`.
Its owner proves both its square law and norm preservation in
`Krein.clockAxis_sq` and `Krein.clockAxis_norm`. We use that operator directly
as a coefficient of a three-by-three matrix.

An actual continuous linear equivalence transports this bounded operator by
Mathlib's endomorphism-algebra conjugation. This transport preserves the square
law; it need not preserve the fixed Hilbert norm. The equivalence is an explicit
hypothesis. Constructing a self-doubling equivalence for every infinite-dimensional
real Hilbert space remains a separate analytic target.

The final example uses the existing native even `Cl(5,5)` phase bivector as the
coefficient root. Neither construction introduces an external complex scalar.
-/

noncomputable section

namespace InfoGeometry.Quantum.OperatorRingSquareNegOne

open InfoGeometry.Algebra.MatrixSquareNegOne
open InfoGeometry.Krein

section DoubledOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The existing doubled-space square law in its endomorphism-ring form. -/
theorem clockAxis_mul_self :
    clockAxis (E := E) * clockAxis (E := E) =
      -(1 : DoubledSpace E →L[ℝ] DoubledSpace E) := by
  change (clockAxis (E := E)).comp (clockAxis (E := E)) =
    -(ContinuousLinearMap.id ℝ (DoubledSpace E))
  exact clockAxis_sq E

/-- Odd outer size is compatible with a native bounded-operator coefficient root. -/
theorem clockAxis_scalar_three_square_eq_neg_one :
    Matrix.scalar (Fin 3) (clockAxis (E := E)) *
        Matrix.scalar (Fin 3) (clockAxis (E := E)) = -1 :=
  scalar_square_eq_neg_one (n := Fin 3) (clockAxis (E := E)) clockAxis_mul_self

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Transport of the concrete doubled clock axis along an actual equivalence. -/
def transportedClockAxis (e : H ≃L[ℝ] DoubledSpace E) : H →L[ℝ] H :=
  e.symm.conjContinuousAlgEquiv (clockAxis (E := E))

omit [CompleteSpace E] in
@[simp] theorem transportedClockAxis_apply
    (e : H ≃L[ℝ] DoubledSpace E) (x : H) :
    transportedClockAxis e x = e.symm (clockAxis (E := E) (e x)) := by
  simp [transportedClockAxis]

/-- Conjugation transports the square law in the actual continuous endomorphism ring. -/
theorem transportedClockAxis_mul_self (e : H ≃L[ℝ] DoubledSpace E) :
    transportedClockAxis e * transportedClockAxis e = -(1 : H →L[ℝ] H) := by
  simpa only [transportedClockAxis, map_mul, map_neg, map_one] using
    congrArg (fun T => e.symm.conjContinuousAlgEquiv T)
      (clockAxis_mul_self (E := E))

/-- The three-by-three solution on `H` is conditional on the supplied equivalence. -/
theorem transportedClockAxis_scalar_three_square_eq_neg_one
    (e : H ≃L[ℝ] DoubledSpace E) :
    Matrix.scalar (Fin 3) (transportedClockAxis e) *
        Matrix.scalar (Fin 3) (transportedClockAxis e) = -1 :=
  scalar_square_eq_neg_one (n := Fin 3)
    (transportedClockAxis e) (transportedClockAxis_mul_self e)

end DoubledOperators

open InfoGeometry.Clifford.Cl55InternalComplex

/-- A three-by-three solution with coefficients in the actual native even Clifford algebra. -/
theorem phaseBivector55_scalar_three_square_eq_neg_one :
    Matrix.scalar (Fin 3) phaseBivector55 *
        Matrix.scalar (Fin 3) phaseBivector55 = -1 :=
  scalar_square_eq_neg_one (n := Fin 3) phaseBivector55 phaseBivector55_sq

end InfoGeometry.Quantum.OperatorRingSquareNegOne
