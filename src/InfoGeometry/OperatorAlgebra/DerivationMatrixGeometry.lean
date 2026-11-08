/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import InfoGeometry.Geometry.AssociativeGaugeConnection
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Derivation geometry of the full matrix algebra

All Leibniz endomorphisms of the full matrix algebra form the direction Lie
algebra. The action is the identity inclusion, so its faithfulness is proved
without any restriction to diagonal or commuting coefficients. Inner matrix
derivations are the restriction of Mathlib's native adjoint Lie homomorphism.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R n : Type*) [CommRing R] [Fintype n] [DecidableEq n]

/-- The full native derivation Lie algebra of a matrix algebra, acting on
that algebra by evaluation. -/
abbrev matrixDerivationsLane : DerivationLieLane R (Matrix n n R) where
  L := NonAssocDerivation.derivations R (Matrix n n R)
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := LieHom.id
  faithful := fun _ _ h => h

/-- The native adjoint endomorphism is a genuine associative derivation. -/
theorem matrix_ad_mem_derivations (X : Matrix n n R) :
    LieAlgebra.ad R (Matrix n n R) X ∈
      NonAssocDerivation.derivations R (Matrix n n R) := by
  intro Y Z
  change X * (Y * Z) - (Y * Z) * X =
    (X * Y - Y * X) * Z + Y * (X * Z - Z * X)
  exact InfoGeometry.Geometry.AssociativeGaugeConnection.innerDerivative_isLeibniz
    (R := R) X Y Z

/-- Inner derivations bundled as a native Lie homomorphism into the full
Leibniz derivation Lie subalgebra. -/
def matrixInnerLieHom :
    Matrix n n R →ₗ⁅R⁆ NonAssocDerivation.derivations R (Matrix n n R) where
  toFun X := ⟨LieAlgebra.ad R (Matrix n n R) X,
    matrix_ad_mem_derivations R n X⟩
  map_add' X Y := by
    apply Subtype.ext
    exact (LieAlgebra.ad R (Matrix n n R)).map_add X Y
  map_smul' r X := by
    apply Subtype.ext
    exact (LieAlgebra.ad R (Matrix n n R)).map_smul r X
  map_lie' := by
    intro X Y
    apply Subtype.ext
    exact (LieAlgebra.ad R (Matrix n n R)).map_lie X Y

@[simp] theorem matrixInnerLieHom_apply (X Y : Matrix n n R) :
    (matrixInnerLieHom R n X : Module.End R (Matrix n n R)) Y =
      X * Y - Y * X :=
  rfl

/-- The native adjoint realization agrees with the repository's original
left-minus-right multiplication operator. -/
theorem matrixInnerLieHom_toEnd_eq_innerDerivative (X : Matrix n n R) :
    (matrixInnerLieHom R n X : Module.End R (Matrix n n R)) =
      InfoGeometry.Geometry.AssociativeGaugeConnection.innerDerivative (R := R) X := by
  apply LinearMap.ext
  intro Y
  rfl

/-- Matrix commutators map to commutators of the actual derivation operators. -/
theorem matrixInnerLieHom_commutator (X Y : Matrix n n R) :
    matrixInnerLieHom R n (X * Y - Y * X) =
      ⁅matrixInnerLieHom R n X, matrixInnerLieHom R n Y⁆ :=
  (matrixInnerLieHom R n).map_lie X Y

/-- An exact one-cochain need not be a flat noncommutative connection:
its exterior derivative vanishes, but the quadratic commutator remains. -/
theorem matrixExactOneForm_curvature (P : Matrix n n R)
    (D E : NonAssocDerivation.derivations R (Matrix n n R)) :
    connectionCurvature (matrixDerivationsLane R n)
        (exteriorDerivativeZero (matrixDerivationsLane R n) P) D E =
      (D : Module.End R (Matrix n n R)) P *
          (E : Module.End R (Matrix n n R)) P -
        (E : Module.End R (Matrix n n R)) P *
          (D : Module.End R (Matrix n n R)) P := by
  rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add,
    connectionWedgeSquare_apply]
  rfl

end InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
