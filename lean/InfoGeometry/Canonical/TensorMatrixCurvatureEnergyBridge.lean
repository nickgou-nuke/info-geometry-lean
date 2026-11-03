/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorColimitCurvatureEnergy
import InfoGeometry.OperatorAlgebra.DerivationMatrixEnergy
import InfoGeometry.Canonical.Cl11StarAlgebraColimit

/-!
# Normalized tensor-stage and full-matrix curvature energies

The tensor stage is the existing full real matrix algebra. The finite
curvature energy is the existing full-matrix energy divided by the binary
matrix size, and therefore agrees with the colimit energy on represented
inner derivation directions.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorMatrixCurvatureEnergyBridge

open scoped BigOperators
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Canonical.TensorColimitCurvatureEnergy
open InfoGeometry.Canonical.TensorStageExactConnection
open InfoGeometry.Canonical.TensorLimitExactConnection
open InfoGeometry.Canonical.Cl11StarAlgebraColimit

variable {ι : Type*} [Fintype ι]

/-- Exact relation between the normalized tower functional and the existing
full-matrix trace energy, for arbitrary noncommuting matrix coefficients. -/
theorem stageEnergy_eq_normalized_matrixEnergy
    (n : ℕ) (P : Stage n) (frame : ι → Stage n) :
    stageCurvatureEnergy n P frame =
      matrixCurvatureEnergy (matrixDerivationsLane ℝ (Idx n))
        (fun i => matrixInnerLieHom ℝ (Idx n) (frame i))
        (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx n)) P) / (2 : ℝ) ^ n := by
  unfold stageCurvatureEnergy matrixCurvatureEnergy matrixTraceNormSq normalizedTrace
  simp only [Finset.sum_div, exactCutCurvature, RCLike.re_to_real]

/-- The same normalized full-matrix energy is the actual colimit readout. -/
theorem colimitEnergy_eq_normalized_matrixEnergy
    (n : ℕ) (P : Stage n) (frame : ι → Stage n) :
    curvatureEnergy (fun i => limitInnerLieHom (ofStage n (frame i)))
      (exteriorDerivativeZero limitDerivationsLane (ofStage n P)) =
      matrixCurvatureEnergy (matrixDerivationsLane ℝ (Idx n))
        (fun i => matrixInnerLieHom ℝ (Idx n) (frame i))
        (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx n)) P) / (2 : ℝ) ^ n := by
  rw [curvatureEnergy_ofStage, stageEnergy_eq_normalized_matrixEnergy]

/-- A finite-stage unitary maps to a unitary of the actual algebraic colimit
through the existing star-algebra inclusion. -/
def stageUnitaryToLimit (n : ℕ) (u : unitary (Stage n)) : unitary Limit :=
  Unitary.map
    { toFun := ofStage n
      map_one' := map_one (ofStage n)
      map_mul' := map_mul (ofStage n)
      map_star' := ofStage_star n } u

@[simp] theorem stageUnitaryToLimit_coe (n : ℕ) (u : unitary (Stage n)) :
    (stageUnitaryToLimit n u : Limit) = ofStage n (u : Stage n) := rfl

/-- The gauge-transformed exact CE one-form itself commutes with the
stage inclusion on all represented inner derivation directions. -/
theorem ofStage_gaugeExactOneForm (n : ℕ) (P X : Stage n) (u : unitary (Stage n)) :
    gaugeOneForm limitDerivationsLane
      (exteriorDerivativeZero limitDerivationsLane (ofStage n P))
      (Unitary.toUnits (stageUnitaryToLimit n u))
      (limitInnerLieHom (ofStage n X)) =
    ofStage n (gaugeOneForm (matrixDerivationsLane ℝ (Idx n))
      (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx n)) P)
      (Unitary.toUnits u) (matrixInnerLieHom ℝ (Idx n) X)) := by
  rw [gaugeOneForm_apply, gaugeOneForm_apply]
  change ofStage n (u : Stage n) * (ofStage n X * ofStage n P - ofStage n P * ofStage n X) *
      star (ofStage n (u : Stage n)) -
    (ofStage n X * ofStage n (u : Stage n) - ofStage n (u : Stage n) * ofStage n X) *
      star (ofStage n (u : Stage n)) =
    ofStage n ((u : Stage n) * (X * P - P * X) * star (u : Stage n) -
      (X * (u : Stage n) - (u : Stage n) * X) * star (u : Stage n))
  simp only [← ofStage_star, ← map_mul, ← map_sub]

/-- The gauge-transformed curvature itself is transported by the stage
inclusion on represented inner directions. -/
theorem ofStage_gaugeExactCurvature (n : ℕ) (P X Y : Stage n) (u : unitary (Stage n)) :
    connectionCurvature limitDerivationsLane
      (gaugeOneForm limitDerivationsLane
        (exteriorDerivativeZero limitDerivationsLane (ofStage n P))
        (Unitary.toUnits (stageUnitaryToLimit n u)))
      (limitInnerLieHom (ofStage n X)) (limitInnerLieHom (ofStage n Y)) =
    ofStage n (connectionCurvature (matrixDerivationsLane ℝ (Idx n))
      (gaugeOneForm (matrixDerivationsLane ℝ (Idx n))
        (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx n)) P)
        (Unitary.toUnits u))
      (matrixInnerLieHom ℝ (Idx n) X) (matrixInnerLieHom ℝ (Idx n) Y)) := by
  rw [connectionCurvature_gaugeOneForm, connectionCurvature_gaugeOneForm]
  change ofStage n (u : Stage n) *
      limitExactCurvature (ofStage n P) (ofStage n X) (ofStage n Y) *
      star (ofStage n (u : Stage n)) =
    ofStage n ((u : Stage n) * exactCutCurvature n P X Y * star (u : Stage n))
  rw [← ofStage_exactCurvature]
  simp only [← ofStage_star, ← map_mul]

/-- The normalized full-matrix energy and the colimit energy agree even
after the same finite-stage unitary gauge transformation. -/
theorem gauge_colimitEnergy_eq_normalized_matrixEnergy
    (n : ℕ) (P : Stage n) (frame : ι → Stage n) (u : unitary (Stage n)) :
    curvatureEnergy (fun i => limitInnerLieHom (ofStage n (frame i)))
      (gaugeOneForm limitDerivationsLane
        (exteriorDerivativeZero limitDerivationsLane (ofStage n P))
        (Unitary.toUnits (stageUnitaryToLimit n u))) =
      matrixCurvatureEnergy (matrixDerivationsLane ℝ (Idx n))
        (fun i => matrixInnerLieHom ℝ (Idx n) (frame i))
        (gaugeOneForm (matrixDerivationsLane ℝ (Idx n))
          (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx n)) P)
          (Unitary.toUnits u)) / (2 : ℝ) ^ n := by
  rw [curvatureEnergy_gauge, matrixCurvatureEnergy_gaugeOneForm,
    colimitEnergy_eq_normalized_matrixEnergy]

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Examples.RealMatrixModeWitness

/-- The explicit noncommuting matrix witness has positive curvature energy at
all later stages and after every finite-stage unitary gauge transformation;
the transported colimit energy is positive as well. -/
theorem denseMode_tail_gauge_energy_positive
    (m : ℕ) (h : 2 ≤ m) (u : unitary (Stage m)) :
    let P := bondMap stageBond 2 m h p
    let frame : Fin 2 → Stage m := fun i => bondMap stageBond 2 m h (![x, star x] i)
    0 < matrixCurvatureEnergy (matrixDerivationsLane ℝ (Idx m))
       (fun i => matrixInnerLieHom ℝ (Idx m) (frame i))
       (gaugeOneForm (matrixDerivationsLane ℝ (Idx m))
         (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx m)) P) (Unitary.toUnits u)) ∧
    0 < curvatureEnergy (fun i => limitInnerLieHom (ofStage m (frame i)))
       (gaugeOneForm limitDerivationsLane
         (exteriorDerivativeZero limitDerivationsLane (ofStage m P))
         (Unitary.toUnits (stageUnitaryToLimit m u))) := by
  dsimp only
  have hs := denseMode_stageCurvatureEnergy_positive m h
  rw [stageEnergy_eq_normalized_matrixEnergy] at hs
  have hn : 0 < (2 : ℝ) ^ m := by positivity
  have hm := (div_pos_iff_of_pos_right hn).mp hs
  constructor
  · rw [matrixCurvatureEnergy_gaugeOneForm]
    exact hm
  · rw [curvatureEnergy_gauge, curvatureEnergy_ofStage]
    exact denseMode_stageCurvatureEnergy_positive m h

end InfoGeometry.Canonical.TensorMatrixCurvatureEnergyBridge

end
