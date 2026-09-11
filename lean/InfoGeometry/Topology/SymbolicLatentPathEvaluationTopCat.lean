import InfoGeometry.Topology.SymbolicLatentPathFunctoriality
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Evaluation of symbolic-latent paths in `TopCat`

The path space is a genuine `ContinuousMap` space.  This owner exposes its
evaluation-at-parameter map as a `TopCat` morphism and records naturality with
the existing continuous path transport.  It does not add a path homotopy or a
quotient claim.
-/

namespace InfoGeometry.Topology

open CategoryTheory

def symbolicLatentPathParameterEvaluationTopCatHom
    {X : Type} [TopologicalSpace X]
    (t : SymbolicPathDomain) :
    TopCat.of (SymbolicLatentPath X) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := fun γ => γ t
      continuous_toFun := ContinuousEvalConst.continuous_eval_const t }

@[simp] theorem symbolicLatentPathParameterEvaluationTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    (t : SymbolicPathDomain) (γ : SymbolicLatentPath X) :
    symbolicLatentPathParameterEvaluationTopCatHom t γ = γ t :=
  rfl

def symbolicLatentPathStartEvaluationTopCatHom
    {X : Type} [TopologicalSpace X] :
    TopCat.of (SymbolicLatentPath X) ⟶ TopCat.of X :=
  symbolicLatentPathParameterEvaluationTopCatHom (0 : SymbolicPathDomain)

def symbolicLatentPathFinishEvaluationTopCatHom
    {X : Type} [TopologicalSpace X] :
    TopCat.of (SymbolicLatentPath X) ⟶ TopCat.of X :=
  symbolicLatentPathParameterEvaluationTopCatHom (1 : SymbolicPathDomain)

@[simp] theorem symbolicLatentPathStartEvaluationTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    symbolicLatentPathStartEvaluationTopCatHom γ = γ.start :=
  rfl

@[simp] theorem symbolicLatentPathFinishEvaluationTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    symbolicLatentPathFinishEvaluationTopCatHom γ = γ.finish :=
  rfl

def symbolicLatentPathEndpointsTopCatHom
    {X : Type} [TopologicalSpace X] :
    TopCat.of (SymbolicLatentPath X) ⟶ TopCat.of (X × X) :=
  let start : C(SymbolicLatentPath X, X) :=
    { toFun := fun γ => γ (0 : SymbolicPathDomain)
      continuous_toFun := ContinuousEvalConst.continuous_eval_const 0 }
  let finish : C(SymbolicLatentPath X, X) :=
    { toFun := fun γ => γ (1 : SymbolicPathDomain)
      continuous_toFun := ContinuousEvalConst.continuous_eval_const 1 }
  TopCat.ofHom (start.prodMk finish)

@[simp] theorem symbolicLatentPathEndpointsTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    symbolicLatentPathEndpointsTopCatHom γ = γ.endpoints :=
  rfl

theorem symbolicLatentPathParameterEvaluationTopCatHom_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f)
    (t : SymbolicPathDomain) :
    symbolicLatentPathTopCatHom f hf ≫
        symbolicLatentPathParameterEvaluationTopCatHom t =
      symbolicLatentPathParameterEvaluationTopCatHom t ≫ TopCat.ofHom
        { toFun := f
          continuous_toFun := hf } := by
  ext γ
  rfl

end InfoGeometry.Topology
