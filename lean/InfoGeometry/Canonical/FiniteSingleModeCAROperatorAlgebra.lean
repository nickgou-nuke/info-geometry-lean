import InfoGeometry.Canonical.FiniteSingleModeCARTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Finite one-mode CAR as a native operator ring

The concrete functions from `FiniteSingleModeCAR` are bundled as elements of
`Module.End ℂ OneModeVec`.  Since the domain is finite-dimensional, Mathlib
also supplies their continuous-linear realizations.  No star operation is
introduced here: an adjoint requires the inner-product structure to be chosen
and proved separately.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteSingleModeCAROperatorAlgebra

open InfoGeometry.Algebra.FiniteSingleModeCAR
open CategoryTheory

def annLinearMap : OneModeVec →ₗ[ℂ] OneModeVec :=
  { toFun := ann
    map_add' := by
      intro ψ φ
      funext occ
      cases occ <;> simp [ann]
    map_smul' := by
      intro a ψ
      funext occ
      cases occ <;> simp [ann] }

def creLinearMap : OneModeVec →ₗ[ℂ] OneModeVec :=
  { toFun := cre
    map_add' := by
      intro ψ φ
      funext occ
      cases occ <;> simp [cre]
    map_smul' := by
      intro a ψ
      funext occ
      cases occ <;> simp [cre] }

abbrev annOperator : Module.End ℂ OneModeVec := annLinearMap
abbrev creOperator : Module.End ℂ OneModeVec := creLinearMap

theorem ann_cre_operator_CAR :
    annOperator * creOperator + creOperator * annOperator =
      (1 : Module.End ℂ OneModeVec) := by
  ext ψ occ
  cases occ <;>
    simp [annOperator, creOperator, annLinearMap, creLinearMap,
      Module.End.mul_eq_comp, ann, cre]

theorem ann_operator_nilpotent :
    annOperator * annOperator = 0 := by
  ext ψ occ
  cases occ <;>
    simp [annOperator, annLinearMap, Module.End.mul_eq_comp, ann]

theorem cre_operator_nilpotent :
    creOperator * creOperator = 0 := by
  ext ψ occ
  cases occ <;>
    simp [creOperator, creLinearMap, Module.End.mul_eq_comp, cre]

def annContinuousLinearMap : OneModeVec →L[ℂ] OneModeVec :=
  LinearMap.toContinuousLinearMap annLinearMap

def creContinuousLinearMap : OneModeVec →L[ℂ] OneModeVec :=
  LinearMap.toContinuousLinearMap creLinearMap

theorem annContinuousLinearMap_apply (ψ : OneModeVec) :
    annContinuousLinearMap ψ = ann ψ :=
  rfl

theorem creContinuousLinearMap_apply (ψ : OneModeVec) :
    creContinuousLinearMap ψ = cre ψ :=
  rfl

def annOperatorTopCatHom :
    TopCat.of OneModeVec ⟶ TopCat.of OneModeVec :=
  TopCat.ofHom
    { toFun := annContinuousLinearMap
      continuous_toFun := annContinuousLinearMap.continuous }

def creOperatorTopCatHom :
    TopCat.of OneModeVec ⟶ TopCat.of OneModeVec :=
  TopCat.ofHom
    { toFun := creContinuousLinearMap
      continuous_toFun := creContinuousLinearMap.continuous }

end InfoGeometry.Canonical.FiniteSingleModeCAROperatorAlgebra
