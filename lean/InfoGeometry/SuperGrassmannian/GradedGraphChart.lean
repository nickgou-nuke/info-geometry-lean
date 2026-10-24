/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.ProjectorGraphChart
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Graded graph charts over arbitrary associative rings

The chart consists of actual submodules transverse to the second summand,
not projectors with an unspecified complement. Gradings use native direct-sum
components over a commutative base; the module scalar ring may be noncommutative.
This is one algebraic chart, not a supermanifold atlas or representability result.
-/

namespace InfoGeometry.SuperGrassmannian.GradedGraphChart

open DirectSum

variable {A U W : Type*} [Ring A]
  [AddCommGroup U] [Module A U] [AddCommGroup W] [Module A W]

/-- The graph has a bijective first projection, without finite-rank assumptions. -/
theorem graph_fst_bijective (f : U →ₗ[A] W) :
    Function.Bijective (Prod.fst ∘ f.graph.subtype) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact Prod.ext h (x.property.trans ((congrArg f h).trans y.property.symm))
  · intro x
    exact ⟨⟨(x, f x), rfl⟩, rfl⟩

theorem graph_injective : Function.Injective (LinearMap.graph (R := A) (M := U) (M₂ := W)) := by
  intro f g h
  ext x
  have hx : (x, f x) ∈ g.graph := h ▸ (show (x, f x) ∈ f.graph from rfl)
  exact hx

/-- A graph is complemented by the fixed vertical submodule. -/
theorem graph_isCompl (f : U →ₗ[A] W) :
    IsCompl f.graph (LinearMap.ker (LinearMap.fst A U W)) := by
  simpa only [ProjectorGraphChart.range_graphProjector,
    ProjectorGraphChart.ker_graphProjector] using
    LinearMap.IsIdempotentElem.isCompl (ProjectorGraphChart.graphProjector_idempotent f)

/-- The first projection identifies the graph with its source module. -/
noncomputable def graphSourceEquiv (f : U →ₗ[A] W) : f.graph ≃ₗ[A] U :=
  LinearEquiv.ofBijective ((LinearMap.fst A U W).comp f.graph.subtype)
    (graph_fst_bijective f)

/-- The quotient by a graph is the complementary module, not an extra
assumed rank witness. -/
noncomputable def graphQuotientEquiv (f : U →ₗ[A] W) :
    ((U × W) ⧸ f.graph) ≃ₗ[A] W :=
  (Submodule.quotEquivOfEq _ _ (LinearMap.graph_eq_ker_coprod f)).trans
    (((-f).coprod LinearMap.id).quotKerEquivOfSurjective (by
      intro y
      exact ⟨(0, y), by simp⟩))

section Grading

variable {k ι : Type*} [CommRing k] [DecidableEq ι]
  [Module k U] [Module k W]
  (GU : ι → Submodule k U) (GW : ι → Submodule k W)
  [Decomposition GU] [Decomposition GW]

/-- Degree-preserving module maps. Components are base-ring submodules, not
`A`-submodules: odd scalars may change degree. -/
def PreservesDegree (f : U →ₗ[A] W) : Prop :=
  ∀ i, ∀ x ∈ GU i, f x ∈ GW i

/-- Homogeneity for the product grading, expressed by its canonical components. -/
def IsGraded (S : Submodule A (U × W)) : Prop :=
  ∀ i, ∀ z ∈ S, ((decompose GU z.1 i : U), (decompose GW z.2 i : W)) ∈ S

/-- A degree-preserving map commutes with all native homogeneous projections. -/
theorem map_component (f : U →ₗ[A] W) (hf : PreservesDegree GU GW f)
    (i : ι) (x : U) :
    f (decompose GU x i : U) = (decompose GW (f x) i : W) := by
  induction x using Decomposition.inductionOn GU with
  | zero => simp
  | @homogeneous j x =>
    by_cases h : j = i
    · subst j
      rw [decompose_of_mem_same GU x.property,
        decompose_of_mem_same GW (hf i x x.property)]
    · rw [decompose_of_mem_ne GU x.property h,
        decompose_of_mem_ne GW (hf j x x.property) h, map_zero]
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

/-- Graph homogeneity is equivalent to degree preservation; neither is assumed
as an opaque certificate for the other. -/
theorem graph_isGraded_iff (f : U →ₗ[A] W) :
    IsGraded GU GW f.graph ↔ PreservesDegree GU GW f := by
  constructor
  · intro h i x hx
    have he := h i (x, f x) rfl
    change (decompose GW (f x) i : W) = f (decompose GU x i : U) at he
    rw [decompose_of_mem_same GU hx] at he
    exact he ▸ (decompose GW (f x) i).property
  · intro h i z hz
    change z.2 = f z.1 at hz
    change (decompose GW z.2 i : W) = f (decompose GU z.1 i : U)
    rw [hz, map_component GU GW f h]

/-- The transverse homogeneous-submodule chart. No choice of projector is
included in a point. -/
def Chart := {S : Submodule A (U × W) //
  Function.Bijective (Prod.fst ∘ S.subtype) ∧ IsGraded GU GW S}

/-- Even linear maps are exactly the homogeneous submodules in the graph chart. -/
noncomputable def graphChartEquiv :
    {f : U →ₗ[A] W // PreservesDegree GU GW f} ≃ Chart (A := A) GU GW where
  toFun f := ⟨f.val.graph, graph_fst_bijective f.val,
    (graph_isGraded_iff GU GW f.val).mpr f.property⟩
  invFun S := ⟨(Submodule.exists_eq_graph S.property.1).choose, by
    apply (graph_isGraded_iff GU GW _).mp
    rw [← (Submodule.exists_eq_graph S.property.1).choose_spec]
    exact S.property.2⟩
  left_inv f := by
    apply Subtype.ext
    apply graph_injective
    exact (Submodule.exists_eq_graph (graph_fst_bijective f.val)).choose_spec.symm
  right_inv S := by
    apply Subtype.ext
    exact (Submodule.exists_eq_graph S.property.1).choose_spec.symm

@[simp] theorem graphChartEquiv_submodule
    (f : {f : U →ₗ[A] W // PreservesDegree GU GW f}) :
    (graphChartEquiv GU GW f).val = f.val.graph := rfl

/-- Every point of this chart is an actual complemented submodule. -/
theorem chart_isCompl (S : Chart (A := A) GU GW) :
    IsCompl S.val (LinearMap.ker (LinearMap.fst A U W)) := by
  obtain ⟨f, hf⟩ := Submodule.exists_eq_graph S.property.1
  rw [hf]
  exact graph_isCompl f

end Grading
end InfoGeometry.SuperGrassmannian.GradedGraphChart
