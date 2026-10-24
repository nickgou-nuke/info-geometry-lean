/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.SplitDerivation
import InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge

/-! # Complete real sl3 plus two vector coordinates for Zorn derivations

This is a linear decomposition, not a direct product of Lie algebras. The
nontrivial cross-sector brackets are `ZornVectorMatrix.splitDerivation_bracket`.
Surjectivity reuses the existing fourteen-parameter classification.
-/

noncomputable section
namespace InfoGeometry.Lie.SplitDerivationCoordinates

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge

/-- Regroup the existing fourteen coordinates; signs follow the actual Zorn product. -/
def parameterToSplit (t : Params) :
    LieAlgebra.SpecialLinear.sl (Fin 3) ℝ × ZornVec3 ℝ × ZornVec3 ℝ :=
  (⟨parameterMatrix t, parameterMatrix_trace_zero t⟩,
    ![-t 10, t 9, -t 4], ![-t 0, -t 3, -t 8])

theorem splitParameterMap_parameterToSplit (t : Params) :
    splitParameterMap (parameterToSplit t) = parameterLinearEquiv t := by
  apply Derivation.ext
  intro X
  change add (matrixAction (parameterMatrix t) X)
    (offDiagonalAction ![-t 10, t 9, -t 4] ![-t 0, -t 3, -t 8] X) = parameterAction t X
  ext i
  all_goals try fin_cases i
  all_goals simp [parameterMatrix, matrixAction, offDiagonalAction, parameterAction,
    add, Matrix.mulVec, Matrix.transpose, dotProduct, ZornVec3.dot, ZornVec3.cross,
    Fin.sum_univ_three]
  all_goals ring

theorem splitParameterMap_surjective :
    Function.Surjective (splitParameterMap (R := ℝ)) := by
  intro D
  refine ⟨parameterToSplit (parameterLinearEquiv.symm D), ?_⟩
  rw [splitParameterMap_parameterToSplit, parameterLinearEquiv.apply_symm_apply]

/-- Every real derivation has unique traceless-matrix and two-vector coordinates. -/
def splitDerivationLinearEquiv :
    (LieAlgebra.SpecialLinear.sl (Fin 3) ℝ × ZornVec3 ℝ × ZornVec3 ℝ) ≃ₗ[ℝ] VDer :=
  LinearEquiv.ofBijective splitParameterMap
    ⟨splitDerivation_injective, splitParameterMap_surjective⟩

/-- Norm skew-symmetry is a consequence for every derivation, not an input socket. -/
theorem every_derivation_norm_skew (D : VDer) (X Y : VZ) :
    QuadraticMap.polar ZornVectorMatrix.norm (D X) Y +
      QuadraticMap.polar ZornVectorMatrix.norm X (D Y) = 0 := by
  obtain ⟨⟨M, p, q⟩, rfl⟩ := splitParameterMap_surjective D
  exact splitDerivation_norm_skew M p q X Y

theorem every_derivation_trace_zero (D : VDer) (X : VZ) : trace (D X) = 0 := by
  obtain ⟨⟨M, p, q⟩, rfl⟩ := splitParameterMap_surjective D
  exact trace_splitDerivation M p q X

end InfoGeometry.Lie.SplitDerivationCoordinates
