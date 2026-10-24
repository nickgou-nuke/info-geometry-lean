/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.GraphChartCocycle
import InfoGeometry.SuperGrassmannian.FiniteFreeCoefficientChange

/-!
# Graph transition naturality under arbitrary coefficient change

The target overlap is proved by transporting the actual denominator inverse.
No target inverse, flatness, or surjectivity of the ring homomorphism is assumed.
These finite-free statements supplement, rather than restrict, the arbitrary-
module transition and cocycle owners.
-/

namespace InfoGeometry.SuperGrassmannian.GraphTransitionScalarExtension

open GraphChartBaseChange GraphChartCocycle FiniteFreeCoefficientChange FreeSupermoduleChart

variable {A B I J : Type*} [Ring A] [Ring B]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Denominators commute with coefficient extension. -/
theorem denominator_map (φ : A →+* B) (G : Module.End A ((I → A) × (J → A)))
    (f : (I → A) →ₗ[A] (J → A)) :
    denominator (mapPairHom φ G) (mapHom φ f) = mapHom φ (denominator G f) := by
  apply mapHom_unique
  intro x
  have h := congrArg Prod.fst (mapPairHom_natural φ G (x, f x))
  change (mapPairHom φ G (fun i => φ (x i), mapHom φ f (fun i => φ (x i)))).1 = _
  rw [mapHom_natural]
  exact h

/-- Numerators commute with coefficient extension. -/
theorem numerator_map (φ : A →+* B) (G : Module.End A ((I → A) × (J → A)))
    (f : (I → A) →ₗ[A] (J → A)) :
    numerator (mapPairHom φ G) (mapHom φ f) = mapHom φ (numerator G f) := by
  apply mapHom_unique
  intro x
  have h := congrArg Prod.snd (mapPairHom_natural φ G (x, f x))
  change (mapPairHom φ G (fun i => φ (x i), mapHom φ f (fun i => φ (x i)))).2 = _
  rw [mapHom_natural]
  exact h

/-- The overlap condition survives any change of coefficient ring. -/
theorem overlap_map (φ : A →+* B) (G : Module.End A ((I → A) × (J → A)))
    (f : (I → A) →ₗ[A] (J → A)) (h : Overlap G f) :
    Overlap (mapPairHom φ G) (mapHom φ f) := by
  unfold Overlap
  rw [denominator_map]
  exact (mapEquiv φ (LinearEquiv.ofBijective (denominator G f) h)).bijective

/-- The fractional transition commutes with coefficient change, including its inverse. -/
theorem transition_natural (φ : A →+* B) (G : Module.End A ((I → A) × (J → A)))
    (f : (I → A) →ₗ[A] (J → A)) (h : Overlap G f) :
    mapHom φ (transition G f h) =
      transition (mapPairHom φ G) (mapHom φ f) (overlap_map φ G f h) := by
  have he : (transition G f h).comp (denominator G f) = numerator G f :=
    LinearMap.ext (transition_denominator G f h)
  have hb := congrArg (mapHom φ) he
  rw [mapHom_comp, ← denominator_map, ← numerator_map] at hb
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (overlap_map φ G f h).surjective y
  exact (LinearMap.congr_fun hb x).trans
    (transition_denominator _ _ (overlap_map φ G f h) x).symm

omit [Fintype J] [DecidableEq J] in
/-- Scalar extension of the graph of an arbitrary finite-free linear map. -/
theorem extend_graph_hom (φ : A →+* B) (f : (I → A) →ₗ[A] (J → A)) :
    extend φ f.graph = (mapHom φ f).graph := by
  have hf : coordinateLinearMap (fun i j => f (Pi.single i 1) j) = f := by
    rw [coordinateLinearMap_eq_piRing]
    exact (LinearEquiv.piRing A (J → A) I ℤ).symm_apply_apply f
  calc
    _ = extend φ (coordinateLinearMap (fun i j => f (Pi.single i 1) j)).graph := by rw [hf]
    _ = _ := extend_graph φ _

/-- Naturality on the actual transformed submodules, not only their coordinates. -/
theorem extend_transformed_graph (φ : A →+* B)
    (G : Module.End A ((I → A) × (J → A))) (f : (I → A) →ₗ[A] (J → A))
    (h : Overlap G f) :
    extend φ (f.graph.map G) = (extend φ f.graph).map (mapPairHom φ G) := by
  rw [transition_graph G f h, extend_graph_hom, transition_natural,
    extend_graph_hom, transition_graph _ _ (overlap_map φ G f h)]

end InfoGeometry.SuperGrassmannian.GraphTransitionScalarExtension
