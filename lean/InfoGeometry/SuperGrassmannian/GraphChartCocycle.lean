/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.GraphChartTransition
import InfoGeometry.SuperGrassmannian.GradedGraphChart

/-!
# Graph transitions, inverse overlap domains and cocycles

All operators act on arbitrary modules over an associative ring. The overlap
condition is actual bijectivity, not a determinant condition or an assumed
fractional formula. The existing exact graph-image criterion is the owner.
-/

namespace InfoGeometry.SuperGrassmannian.GraphChartCocycle

open GradedGraphChart GraphChartTransition

variable {A U W : Type*} [Ring A]
  [AddCommGroup U] [Module A U] [AddCommGroup W] [Module A W]

/-- First coordinate of the transformed graph inclusion: the denominator. -/
def denominator (G : Module.End A (U × W)) (f : U →ₗ[A] W) : Module.End A U :=
  (LinearMap.fst A U W).comp (G.comp (LinearMap.id.prod f))

/-- Second coordinate of the transformed graph inclusion: the numerator. -/
def numerator (G : Module.End A (U × W)) (f : U →ₗ[A] W) : U →ₗ[A] W :=
  (LinearMap.snd A U W).comp (G.comp (LinearMap.id.prod f))

/-- Exact overlap domain for an invertible ambient change of coordinates. -/
def Overlap (G : Module.End A (U × W)) (f : U →ₗ[A] W) : Prop :=
  Function.Bijective (denominator G f)

/-- Ordered fractional transition, with a genuine inverse of the denominator. -/
noncomputable def transition (G : Module.End A (U × W)) (f : U →ₗ[A] W)
    (h : Overlap G f) : U →ₗ[A] W :=
  (numerator G f).comp (LinearEquiv.ofBijective (denominator G f) h).symm.toLinearMap

@[simp] theorem transition_denominator (G : Module.End A (U × W)) (f : U →ₗ[A] W)
    (h : Overlap G f) (x : U) :
    transition G f h (denominator G f x) = numerator G f x := by
  exact congrArg (numerator G f)
    ((LinearEquiv.ofBijective (denominator G f) h).symm_apply_apply x)

/-- The formula denotes exactly the transformed submodule. -/
theorem transition_graph (G : Module.End A (U × W)) (f : U →ₗ[A] W)
    (h : Overlap G f) : f.graph.map G = (transition G f h).graph := by
  apply (map_graph_eq_iff G f _).mpr
  exact ⟨fun x => (transition_denominator G f h x).symm, h.surjective⟩

/-- Identity changes are defined on every graph. -/
theorem overlap_id (f : U →ₗ[A] W) : Overlap LinearMap.id f :=
  Function.bijective_id

@[simp] theorem transition_id (f : U →ₗ[A] W) :
    transition LinearMap.id f (overlap_id f) = f := by
  apply graph_injective
  rw [← transition_graph, Submodule.map_id]

/-- Successive graph images agree with the composite coordinate change. -/
theorem composite_graph (G H : Module.End A (U × W)) (f : U →ₗ[A] W)
    (hG : Overlap G f) (hH : Overlap H (transition G f hG)) :
    f.graph.map (H.comp G) = (transition H (transition G f hG) hH).graph := by
  rw [Submodule.map_comp, transition_graph G f hG, transition_graph H _ hH]

/-- The exact triple-overlap condition; no extra inverse is postulated. -/
theorem overlap_comp_iff (G H : (U × W) ≃ₗ[A] (U × W)) (f : U →ₗ[A] W)
    (hG : Overlap G.toLinearMap f) :
    Overlap (H.toLinearMap.comp G.toLinearMap) f ↔
      Overlap H.toLinearMap (transition G.toLinearMap f hG) := by
  calc
    _ ↔ ∃ g : U →ₗ[A] W, f.graph.map (H.toLinearMap.comp G.toLinearMap) = g.graph :=
      (exists_map_graph_iff (H.toLinearMap.comp G.toLinearMap)
        (H.injective.comp G.injective) f).symm
    _ ↔ ∃ g : U →ₗ[A] W, (transition G.toLinearMap f hG).graph.map H.toLinearMap = g.graph := by
      simp only [Submodule.map_comp, transition_graph G.toLinearMap f hG]
    _ ↔ _ := exists_map_graph_iff H.toLinearMap H.injective _

/-- Cocycle law with the overlap of the composite derived from the two overlaps. -/
theorem transition_cocycle (G H : (U × W) ≃ₗ[A] (U × W)) (f : U →ₗ[A] W)
    (hG : Overlap G.toLinearMap f)
    (hH : Overlap H.toLinearMap (transition G.toLinearMap f hG)) :
    transition (H.toLinearMap.comp G.toLinearMap) f ((overlap_comp_iff G H f hG).mpr hH) =
      transition H.toLinearMap (transition G.toLinearMap f hG) hH := by
  apply graph_injective
  rw [← transition_graph]
  exact composite_graph _ _ _ hG hH

/-- Pulling a transformed graph back by the inverse recovers the original submodule. -/
theorem inverse_graph (G : (U × W) ≃ₗ[A] (U × W)) (f : U →ₗ[A] W)
    (h : Overlap G.toLinearMap f) :
    (transition G.toLinearMap f h).graph.map G.symm.toLinearMap = f.graph := by
  rw [← transition_graph, ← Submodule.map_comp]
  simp

/-- Every overlap point maps into the inverse overlap domain. -/
theorem overlap_inverse (G : (U × W) ≃ₗ[A] (U × W)) (f : U →ₗ[A] W)
    (h : Overlap G.toLinearMap f) :
    Overlap G.symm.toLinearMap (transition G.toLinearMap f h) :=
  (exists_map_graph_iff G.symm.toLinearMap G.symm.injective _).mp
    ⟨f, inverse_graph G f h⟩

@[simp] theorem transition_inverse (G : (U × W) ≃ₗ[A] (U × W)) (f : U →ₗ[A] W)
    (h : Overlap G.toLinearMap f) :
    transition G.symm.toLinearMap (transition G.toLinearMap f h) (overlap_inverse G f h) = f := by
  apply graph_injective
  rw [← transition_graph]
  exact inverse_graph G f h

/-- Actual equivalence between the two overlap subtypes. -/
noncomputable def overlapEquiv (G : (U × W) ≃ₗ[A] (U × W)) :
    {f : U →ₗ[A] W // Overlap G.toLinearMap f} ≃
      {f : U →ₗ[A] W // Overlap G.symm.toLinearMap f} where
  toFun f := ⟨transition G.toLinearMap f.val f.property, overlap_inverse G f.val f.property⟩
  invFun f := ⟨transition G.symm.toLinearMap f.val f.property,
    overlap_inverse G.symm f.val f.property⟩
  left_inv f := Subtype.ext (transition_inverse G f.val f.property)
  right_inv f := Subtype.ext (transition_inverse G.symm f.val f.property)

end InfoGeometry.SuperGrassmannian.GraphChartCocycle
