/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CoarseGrainingComposition
import InfoGeometry.OperatorAlgebra.CoisometricCoarseGraining
import InfoGeometry.OperatorAlgebra.FiniteParametrix
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms

/-!
# Noncommuting rectangular regression and axiom audit

The general theorems are checked on a three-dimensional fine space and a
two-dimensional coarse space. Both precision operators have nonzero
off-diagonal entries. The fine precision fails to commute with the retained
projection, and the coarse weight fails to commute with transported fine
precision. Exact rational covariance entries detect incorrect factor order.
-/

noncomputable section

namespace BalabanOperatorTests

open Matrix
open scoped ComplexOrder
open InfoGeometry.OperatorAlgebra.PositiveCoarseGraining

def fineSeed : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 0; 0, 1, 1; 0, 0, 1]
def coarseSeed : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 0]
def fineMatrix : Matrix (Fin 3) (Fin 3) ℝ := 1 + fineSeedᴴ * fineSeed
def coarseWeight : Matrix (Fin 2) (Fin 2) ℝ := 1 + coarseSeedᴴ * coarseSeed
def observation : Matrix (Fin 2) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0]

theorem fineMatrix_posDef : fineMatrix.PosDef :=
  Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self fineSeed)

theorem coarseWeight_posDef : coarseWeight.PosDef :=
  Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self coarseSeed)

theorem observation_coisometry : observation * observationᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [observation, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem fineMatrix_not_commuting_with_projection :
    fineMatrix * (observationᴴ * observation) ≠ (observationᴴ * observation) * fineMatrix := by
  intro h
  have hentry := congrArg (fun M => M 1 2) h
  norm_num [fineMatrix, fineSeed, observation, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, Fin.sum_univ_succ] at hentry

theorem coarseWeight_not_commuting_with_transport :
    coarseWeight * (observation * fineMatrix * observationᴴ) ≠
      (observation * fineMatrix * observationᴴ) * coarseWeight := by
  intro h
  have hentry := congrArg (fun M => M 0 1) h
  norm_num [coarseWeight, coarseSeed, fineMatrix, fineSeed, observation, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, Fin.sum_univ_succ,
    Matrix.vecMul, dotProduct] at hentry

/-- The same operators act on the complexified fine and coarse spaces. -/
def complexFineMatrix : Matrix (Fin 3) (Fin 3) ℂ := fineMatrix.map Complex.ofRealHom
def complexRetainedProjection : Matrix (Fin 3) (Fin 3) ℂ :=
  (observationᴴ * observation).map Complex.ofRealHom
def complexCoarseWeight : Matrix (Fin 2) (Fin 2) ℂ := coarseWeight.map Complex.ofRealHom
def complexTransportedFine : Matrix (Fin 2) (Fin 2) ℂ :=
  (observation * fineMatrix * observationᴴ).map Complex.ofRealHom

theorem complexFineMatrix_not_commuting_with_projection :
    complexFineMatrix * complexRetainedProjection ≠
      complexRetainedProjection * complexFineMatrix := by
  intro h
  apply fineMatrix_not_commuting_with_projection
  apply Matrix.map_injective (f := Complex.ofRealHom) Complex.ofReal_injective
  simpa only [complexFineMatrix, complexRetainedProjection, Matrix.map_mul] using h

theorem complexCoarseWeight_not_commuting_with_transport :
    complexCoarseWeight * complexTransportedFine ≠
      complexTransportedFine * complexCoarseWeight := by
  intro h
  apply coarseWeight_not_commuting_with_transport
  apply Matrix.map_injective (f := Complex.ofRealHom) Complex.ofReal_injective
  simpa only [complexCoarseWeight, complexTransportedFine, Matrix.map_mul] using h

theorem fineMatrix_inv :
    fineMatrix⁻¹ = !![(8 / 13 : ℝ), -3 / 13, 1 / 13;
      -3 / 13, 6 / 13, -2 / 13; 1 / 13, -2 / 13, 5 / 13] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fineMatrix, fineSeed, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem coarseWeight_inv : coarseWeight⁻¹ = !![(2 / 5 : ℝ), -1 / 5; -1 / 5, 3 / 5] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coarseWeight, coarseSeed, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem explicit_coarse_covariance :
    coarseCovariance fineMatrix coarseWeight observation =
      !![(66 / 65 : ℝ), -28 / 65; -28 / 65, 69 / 65] := by
  rw [coarseCovariance, fineMatrix_inv, coarseWeight_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [observation, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.vecMul, dotProduct]

theorem explicit_coarse_precision :
    coarsePrecision fineMatrix coarseWeight observation =
      !![(69 / 58 : ℝ), 28 / 58; 28 / 58, 66 / 58] := by
  rw [← coarseCovariance_inv observation fineMatrix_posDef coarseWeight_posDef,
    explicit_coarse_covariance]
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

example (y : Fin 2 → ℝ) (x : Fin 3 → ℝ) :
    (∀ z, quadraticEnergy fineMatrix coarseWeight observation y x ≤
      quadraticEnergy fineMatrix coarseWeight observation y z) ↔
      x = harmonicExtension fineMatrix coarseWeight observation *ᵥ y :=
  is_minimizer_iff observation fineMatrix_posDef coarseWeight_posDef y x

/-- Complex specialization checks the conjugate-transpose and real-energy carrier. -/
example {A : Matrix (Fin 3) (Fin 3) ℂ} {R : Matrix (Fin 2) (Fin 2) ℂ}
    (Q : Matrix (Fin 2) (Fin 3) ℂ) (hA : A.PosDef) (hR : R.PosDef)
    (y : Fin 2 → ℂ) (x : Fin 3 → ℂ) :
    quadraticEnergy A R Q y x =
      (star y ⬝ᵥ (coarsePrecision A R Q *ᵥ y)).re +
        (star (x - harmonicExtension A R Q *ᵥ y) ⬝ᵥ
          (finePrecision A R Q *ᵥ (x - harmonicExtension A R Q *ᵥ y))).re :=
  quadraticEnergy_completion Q hA hR y x

#print axioms fineMatrix_not_commuting_with_projection
#print axioms coarseWeight_not_commuting_with_transport
#print axioms explicit_coarse_precision
#print axioms coarseCovariance_inv
#print axioms coarsePrecision_posDef
#print axioms finePrecision_inv
#print axioms quadratic_completion
#print axioms is_minimizer_iff
#print axioms twoStage_coarsePrecision_inv
#print axioms is_joint_minimizer_iff
#print axioms InfoGeometry.OperatorAlgebra.CoisometricCoarseGraining.projection_isStarProjection
#print axioms InfoGeometry.OperatorAlgebra.CoisometricCoarseGraining.range_complement_eq_ker
#print axioms InfoGeometry.OperatorAlgebra.FiniteParametrix.mul_partialParametrix
#print axioms InfoGeometry.OperatorAlgebra.FiniteParametrix.inverse_remainder

end BalabanOperatorTests

/- The test fails on any additional axiom in any named theorem of the new
owners or the concrete regression, including transitively imported axioms. -/
run_cmd do
  let prefixes : Array Lean.Name := #[
    `InfoGeometry.OperatorAlgebra.PositiveCoarseGraining,
    `InfoGeometry.OperatorAlgebra.CoisometricCoarseGraining,
    `InfoGeometry.OperatorAlgebra.FiniteParametrix,
    `BalabanOperatorTests]
  let env ← Lean.getEnv
  let names := env.constants.fold (init := #[]) fun acc name info =>
    if name.isInternal || name.hasMacroScopes || !prefixes.any (·.isPrefixOf name) then acc
    else match info with
      | .thmInfo _ => acc.push name
      | _ => acc
  if names.size < 44 then
    throwError "Expected at least 44 named library and regression theorems, found {names.size}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  Lean.logInfo m!"Balaban operator axiom audit passed for {names.size} named theorems."
