/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorStageExactConnection

/-!
# Inner derivations and exact CE curvature on the algebraic tensor colimit

The colimit carries its native algebraic derivation lane.  Its inner
Leibniz directions and exact connection are compared with finite stages.
No norm or continuity on the colimit is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorLimitExactConnection

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.TensorStageExactConnection

attribute [local instance 100] LieRing.ofAssociativeRing

/-- All real-linear Leibniz derivations of the actual algebraic colimit. -/
abbrev limitDerivationsLane : DerivationLieLane ℝ Limit where
  L := NonAssocDerivation.derivations ℝ Limit
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := LieHom.id
  faithful := fun _ _ h => h

/-- Inner adjoint directions satisfy the Leibniz identity on the colimit. -/
theorem limit_ad_mem_derivations (X : Limit) :
    LieAlgebra.ad ℝ Limit X ∈ NonAssocDerivation.derivations ℝ Limit := by
  intro Y Z
  change X * (Y * Z) - (Y * Z) * X =
    (X * Y - Y * X) * Z + Y * (X * Z - Z * X)
  exact InfoGeometry.Geometry.AssociativeGaugeConnection.innerDerivative_isLeibniz
    (R := ℝ) X Y Z

/-- The inner-direction Lie homomorphism of the algebraic colimit. -/
def limitInnerLieHom : Limit →ₗ⁅ℝ⁆ NonAssocDerivation.derivations ℝ Limit where
  toFun X := ⟨LieAlgebra.ad ℝ Limit X, limit_ad_mem_derivations X⟩
  map_add' X Y := by
    apply Subtype.ext
    exact (LieAlgebra.ad ℝ Limit).map_add X Y
  map_smul' r X := by
    apply Subtype.ext
    exact (LieAlgebra.ad ℝ Limit).map_smul r X
  map_lie' := by
    intro X Y
    apply Subtype.ext
    exact (LieAlgebra.ad ℝ Limit).map_lie X Y

@[simp] theorem limitInnerLieHom_apply (X Y : Limit) :
    (limitInnerLieHom X : Module.End ℝ Limit) Y = X * Y - Y * X := rfl

/-- The colimit inner derivation restricts to the finite inner derivation
on every represented element of the same stage. -/
theorem ofStage_inner_action (n : ℕ) (X T : Stage n) :
    (limitInnerLieHom (ofStage n X) : Module.End ℝ Limit) (ofStage n T) =
      ofStage n ((matrixInnerLieHom ℝ _ X : Module.End ℝ (Stage n)) T) := by
  simp only [limitInnerLieHom_apply, matrixInnerLieHom_apply, map_sub, map_mul]

/-- The actual colimit CE connection restricts to the finite-stage exact
connection on its embedded inner directions and coefficients. -/
theorem ofStage_exactCovariantDerivative (n : ℕ) (P X T : Stage n) :
    covariantDerivative limitDerivationsLane
      (exteriorDerivativeZero limitDerivationsLane (ofStage n P))
      (limitInnerLieHom (ofStage n X)) (ofStage n T) =
    ofStage n (covariantDerivative (matrixDerivationsLane ℝ _)
      (exteriorDerivativeZero (matrixDerivationsLane ℝ _) P)
      (matrixInnerLieHom ℝ _ X) T) := by
  change (ofStage n X * ofStage n T - ofStage n T * ofStage n X) +
    (ofStage n X * ofStage n P - ofStage n P * ofStage n X) * ofStage n T -
    ofStage n T * (ofStage n X * ofStage n P - ofStage n P * ofStage n X) =
    ofStage n ((X * T - T * X) + (X * P - P * X) * T - T * (X * P - P * X))
  simp only [map_sub, map_add, map_mul]

/-- The CE curvature of the exact one-form associated to a colimit element. -/
def limitExactCurvature (P X Y : Limit) : Limit :=
  connectionCurvature limitDerivationsLane
    (exteriorDerivativeZero limitDerivationsLane P)
    (limitInnerLieHom X) (limitInnerLieHom Y)

theorem limitExactCurvature_apply (P X Y : Limit) :
    limitExactCurvature P X Y =
      (X * P - P * X) * (Y * P - P * Y) -
        (Y * P - P * Y) * (X * P - P * X) := by
  unfold limitExactCurvature
  rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add,
    connectionWedgeSquare_apply]
  rfl

/-- For arbitrary algebraic Leibniz directions, exact CE curvature is the
commutator of their actions on the coefficient `P`. -/
theorem limit_exactCurvature_all_directions (P : Limit)
    (D E : limitDerivationsLane.L) :
    connectionCurvature limitDerivationsLane
        (exteriorDerivativeZero limitDerivationsLane P) D E =
      limitDerivationsLane.operatorAction D P * limitDerivationsLane.operatorAction E P -
        limitDerivationsLane.operatorAction E P * limitDerivationsLane.operatorAction D P := by
  rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add,
    connectionWedgeSquare_apply]
  rfl

/-- The commutator of covariant Leibniz derivations has the exact curvature
as its inner defect for arbitrary directions on the colimit. -/
theorem limit_exactConnection_commutator (P a : Limit)
    (D E : limitDerivationsLane.L) :
    covariantDerivative limitDerivationsLane (exteriorDerivativeZero limitDerivationsLane P) D
        (covariantDerivative limitDerivationsLane (exteriorDerivativeZero limitDerivationsLane P) E a) -
      covariantDerivative limitDerivationsLane (exteriorDerivativeZero limitDerivationsLane P) E
        (covariantDerivative limitDerivationsLane (exteriorDerivativeZero limitDerivationsLane P) D a) -
      covariantDerivative limitDerivationsLane (exteriorDerivativeZero limitDerivationsLane P)
        ⁅D, E⁆ a =
    (limitDerivationsLane.operatorAction D P * limitDerivationsLane.operatorAction E P -
      limitDerivationsLane.operatorAction E P * limitDerivationsLane.operatorAction D P) * a -
    a * (limitDerivationsLane.operatorAction D P * limitDerivationsLane.operatorAction E P -
      limitDerivationsLane.operatorAction E P * limitDerivationsLane.operatorAction D P) := by
  rw [covariantDerivative_commutator, limit_exactCurvature_all_directions]

/-- Bianchi's identity holds on all derivation directions of the actual
algebraic colimit, without requiring them to be inner. -/
theorem limit_exactConnection_bianchi (P : Limit) (D E F : limitDerivationsLane.L) :
    covariantExteriorDerivativeTwo limitDerivationsLane
      (exteriorDerivativeZero limitDerivationsLane P)
      (connectionCurvature limitDerivationsLane (exteriorDerivativeZero limitDerivationsLane P))
      D E F = 0 := by
  exact connectionCurvature_bianchi limitDerivationsLane _ D E F

/-- Finite exact CE curvature is the restriction of the colimit CE curvature
on the images of the finite inner directions. -/
theorem ofStage_exactCurvature (n : ℕ) (P X Y : Stage n) :
    ofStage n (exactCutCurvature n P X Y) =
      limitExactCurvature (ofStage n P) (ofStage n X) (ofStage n Y) := by
  rw [exactCutCurvature_apply, limitExactCurvature_apply]
  simp only [map_sub, map_mul]

end InfoGeometry.Canonical.TensorLimitExactConnection

end
