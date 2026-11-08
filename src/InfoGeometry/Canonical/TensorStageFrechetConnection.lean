/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorLimitExactConnection
import InfoGeometry.Canonical.FrechetCECovariantConnection
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Continuous Leibniz derivations on tensor matrix stages

The finite matrix stages use their operator norm. Their inner Fréchet–Leibniz
operators realize the exact Chevalley–Eilenberg connection, and their
covariant actions map to the algebraic tensor colimit. No topology on the
colimit is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorStageFrechetConnection

open scoped Matrix Matrix.Norms.Operator
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Canonical.OperatorFrechetDerivationJet
open InfoGeometry.Canonical.OperatorFrechetDerivationJet.FrechetBridge
open InfoGeometry.Canonical.FrechetCECovariantConnection
open InfoGeometry.Canonical.TensorStageExactConnection
open InfoGeometry.Canonical.TensorLimitExactConnection

/-- The actual matrix-stage inner derivation as a continuous linear
Leibniz operator. -/
def stageInnerFrechet (n : ℕ) (X : Stage n) : FrechetOperatorDerivation ℝ (Stage n) :=
  FrechetOperatorDerivation.ofInner X

/-- The continuous derivation direction agrees with the native algebraic
matrix adjoint direction. -/
theorem stageInnerFrechet_toRealDerivation (n : ℕ) (X : Stage n) :
    toRealDerivation (stageInnerFrechet n X) = matrixInnerLieHom ℝ (Idx n) X := by
  apply Subtype.ext
  apply LinearMap.ext
  intro T
  change X * T - T * X = X * T - T * X
  rfl

/-- The Fréchet–Leibniz covariant action realizes the finite CE connection. -/
theorem stageFrechetCovariant_eq_ce (n : ℕ) (P X T : Stage n) :
    covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage n)) P)
      (stageInnerFrechet n X) T =
    covariantDerivative (matrixDerivationsLane ℝ (Idx n))
      (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx n)) P)
      (matrixInnerLieHom ℝ (Idx n) X) T := by
  rw [covariantFrechet_eq_ce, stageInnerFrechet_toRealDerivation]
  rfl

/-- The continuous finite-stage Fréchet–Leibniz covariant action is compatible
with every iterated tensor-tower bonding map. -/
theorem bondMap_frechetCovariant {n m : ℕ} (hnm : n ≤ m) (P X T : Stage n) :
    bondMap stageBond n m hnm
        (covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage n)) P)
          (stageInnerFrechet n X) T) =
      covariantFrechet
        (exteriorDerivativeZero (realDerivationsLane (Stage m))
          (bondMap stageBond n m hnm P))
        (stageInnerFrechet m (bondMap stageBond n m hnm X))
        (bondMap stageBond n m hnm T) := by
  calc
    _ = bondMap stageBond n m hnm
        (covariantDerivative (matrixDerivationsLane ℝ (Idx n))
          (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx n)) P)
          (matrixInnerLieHom ℝ (Idx n) X) T) := by
          rw [stageFrechetCovariant_eq_ce]
    _ = covariantDerivative (matrixDerivationsLane ℝ (Idx m))
        (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx m))
          (bondMap stageBond n m hnm P))
        (matrixInnerLieHom ℝ (Idx m) (bondMap stageBond n m hnm X))
        (bondMap stageBond n m hnm T) := by
          symm
          exact bondMap_exactCovariantDerivative hnm P X T
    _ = _ := by
          symm
          exact stageFrechetCovariant_eq_ce m
            (bondMap stageBond n m hnm P)
            (bondMap stageBond n m hnm X)
            (bondMap stageBond n m hnm T)

/-- The image of the continuous finite covariant action agrees with the
algebraic CE covariant action on the actual tensor colimit. -/
theorem ofStage_frechetCovariant (n : ℕ) (P X T : Stage n) :
    ofStage n (covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage n)) P)
      (stageInnerFrechet n X) T) =
    covariantDerivative limitDerivationsLane
      (exteriorDerivativeZero limitDerivationsLane (ofStage n P))
      (limitInnerLieHom (ofStage n X)) (ofStage n T) := by
  rw [stageFrechetCovariant_eq_ce, ofStage_exactCovariantDerivative]

/-- The curvature defect of the continuous finite-stage Leibniz operators
maps to the inner action of the actual colimit CE curvature. -/
theorem ofStage_frechetCovariant_curvature (n : ℕ) (P X Y T : Stage n) :
    ofStage n
      (covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage n)) P)
          (stageInnerFrechet n X)
          (covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage n)) P)
            (stageInnerFrechet n Y) T) -
       covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage n)) P)
          (stageInnerFrechet n Y)
          (covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage n)) P)
            (stageInnerFrechet n X) T) -
       covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage n)) P)
          (FrechetOperatorDerivation.commutator (stageInnerFrechet n X)
            (stageInnerFrechet n Y)) T) =
    limitExactCurvature (ofStage n P) (ofStage n X) (ofStage n Y) * ofStage n T -
      ofStage n T * limitExactCurvature (ofStage n P) (ofStage n X) (ofStage n Y) := by
  rw [covariantFrechet_curvature, stageInnerFrechet_toRealDerivation,
    stageInnerFrechet_toRealDerivation]
  change ofStage n (exactCutCurvature n P X Y * T - T * exactCutCurvature n P X Y) = _
  simp only [map_sub, map_mul, ofStage_exactCurvature]

/-- The finite continuous covariant operator satisfies the Leibniz law and
is Fréchet differentiable as a continuous linear map. -/
theorem stageFrechetCovariant_differentiable_leibniz (n : ℕ) (P X T U V : Stage n) :
    HasFDerivAt
      (covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage n)) P)
        (stageInnerFrechet n X) : Stage n → Stage n)
      (covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage n)) P)
        (stageInnerFrechet n X)).toContinuousLinearMap T ∧
    covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage n)) P)
        (stageInnerFrechet n X) (U * V) =
      covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage n)) P)
        (stageInnerFrechet n X) U * V + U *
      covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage n)) P)
        (stageInnerFrechet n X) V := by
  exact covariantFrechet_differentiable_leibniz _ _ T U V

end InfoGeometry.Canonical.TensorStageFrechetConnection

end
