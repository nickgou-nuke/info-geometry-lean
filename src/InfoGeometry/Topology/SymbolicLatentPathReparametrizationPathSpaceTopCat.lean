import InfoGeometry.Topology.SymbolicLatentPathReparametrizationComposition
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathEvaluationTopCat
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Reparametrization of symbolic-latent path spaces in `TopCat`

This owner exposes the continuous precomposition action on the genuine path
space.  The quotient action has a separate owner; the two carriers are kept
distinct so that no quotient or homotopy claim is hidden in this morphism.
-/

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable def symbolicLatentPathReparametrizationPathSpaceTopCatHom
    {X : Type} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization) :
    TopCat.of (SymbolicLatentPath X) ⟶ TopCat.of (SymbolicLatentPath X) :=
  TopCat.ofHom
    { toFun := reparametrizeSymbolicLatentPath R
      continuous_toFun := ContinuousMap.continuous_precomp R.parameter }

@[simp] theorem symbolicLatentPathReparametrizationPathSpaceTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (γ : SymbolicLatentPath X) :
    symbolicLatentPathReparametrizationPathSpaceTopCatHom R γ =
      reparametrizeSymbolicLatentPath R γ :=
  rfl

theorem symbolicLatentPathReparametrizationPathSpaceTopCatHom_comp
    {X : Type} [TopologicalSpace X]
    (R S : SymbolicLatentPathReparametrization) :
    symbolicLatentPathReparametrizationPathSpaceTopCatHom
        (X := X) (composeSymbolicLatentPathReparametrization R S) =
      symbolicLatentPathReparametrizationPathSpaceTopCatHom
        (X := X) S ≫
      symbolicLatentPathReparametrizationPathSpaceTopCatHom
          (X := X) R := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro γ
  change reparametrizeSymbolicLatentPath
      (composeSymbolicLatentPathReparametrization R S) γ =
    reparametrizeSymbolicLatentPath R
      (reparametrizeSymbolicLatentPath S γ)
  exact (reparametrizeSymbolicLatentPath_comp R S γ).symm

theorem symbolicLatentPathReparametrizationPathSpaceTopCatHom_comp_apply
    {X : Type} [TopologicalSpace X]
    (R S : SymbolicLatentPathReparametrization)
    (γ : SymbolicLatentPath X) :
    symbolicLatentPathReparametrizationPathSpaceTopCatHom
        (X := X) (composeSymbolicLatentPathReparametrization R S) γ =
      (symbolicLatentPathReparametrizationPathSpaceTopCatHom
        (X := X) S ≫
       symbolicLatentPathReparametrizationPathSpaceTopCatHom
         (X := X) R) γ := by
  exact congrArg (fun m => m γ)
    (symbolicLatentPathReparametrizationPathSpaceTopCatHom_comp
      (X := X) R S)

theorem symbolicLatentPathReparametrizationPathSpaceTopCatHom_start
    {X : Type} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization) :
    symbolicLatentPathReparametrizationPathSpaceTopCatHom
        (X := X) R ≫
        symbolicLatentPathStartEvaluationTopCatHom =
      symbolicLatentPathStartEvaluationTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro γ
  change (reparametrizeSymbolicLatentPath R γ).start = γ.start
  change γ (R.parameter 0) = γ 0
  rw [R.at_zero]

theorem symbolicLatentPathReparametrizationPathSpaceTopCatHom_finish
    {X : Type} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization) :
    symbolicLatentPathReparametrizationPathSpaceTopCatHom
        (X := X) R ≫
        symbolicLatentPathFinishEvaluationTopCatHom =
      symbolicLatentPathFinishEvaluationTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro γ
  change (reparametrizeSymbolicLatentPath R γ).finish = γ.finish
  change γ (R.parameter 1) = γ 1
  rw [R.at_one]

end InfoGeometry.Topology
