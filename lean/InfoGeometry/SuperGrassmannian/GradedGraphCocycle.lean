/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.GraphChartCocycle
import InfoGeometry.SuperGrassmannian.GradedGraphTransition

/-!
# Graded overlap equivalences

An even ambient equivalence has an even inverse, proved using the componentwise
native decomposition. Its graph transition therefore restricts to an actual
equivalence of graded overlap domains. No inverse-grading axiom is supplied.
-/

namespace InfoGeometry.SuperGrassmannian.GradedGraphCocycle

open DirectSum GradedGraphChart GraphChartCocycle GradedGraphTransition

variable {A k ι U W : Type*} [Ring A] [CommRing k] [DecidableEq ι]
  [AddCommGroup U] [Module A U] [Module k U]
  [AddCommGroup W] [Module A W] [Module k W]
  (GU : ι → Submodule k U) (GW : ι → Submodule k W)
  [Decomposition GU] [Decomposition GW]

/-- An even ambient map commutes with the componentwise product projections. -/
theorem product_map_component (G : Module.End A (U × W))
    (hG : PreservesDegree (fun i => (GU i).prod (GW i))
      (fun i => (GU i).prod (GW i)) G) (i : ι) (z : U × W) :
    G ((decompose GU z.1 i : U), (decompose GW z.2 i : W)) =
      ((decompose GU (G z).1 i : U), (decompose GW (G z).2 i : W)) := by
  have h11 := map_component GU GU
    ((LinearMap.fst A U W).comp (G.comp (LinearMap.inl A U W)))
    (fun j x hx => (hG j (x, 0) ⟨hx, (GW j).zero_mem⟩).1) i z.1
  have h12 := map_component GW GU
    ((LinearMap.fst A U W).comp (G.comp (LinearMap.inr A U W)))
    (fun j y hy => (hG j (0, y) ⟨(GU j).zero_mem, hy⟩).1) i z.2
  have h21 := map_component GU GW
    ((LinearMap.snd A U W).comp (G.comp (LinearMap.inl A U W)))
    (fun j x hx => (hG j (x, 0) ⟨hx, (GW j).zero_mem⟩).2) i z.1
  have h22 := map_component GW GW
    ((LinearMap.snd A U W).comp (G.comp (LinearMap.inr A U W)))
    (fun j y hy => (hG j (0, y) ⟨(GU j).zero_mem, hy⟩).2) i z.2
  have hs (v : U × W) : G v = G (v.1, 0) + G (0, v.2) := by
    rw [← map_add]
    simp
  rw [hs (↑(decompose GU z.1 i), ↑(decompose GW z.2 i)), hs z]
  apply Prod.ext
  · simpa using congrArg₂ (· + ·) h11 h12
  · simpa using congrArg₂ (· + ·) h21 h22

/-- Inverse evenness on the product is derived, with no inverse-grading hypothesis. -/
theorem product_inverse_preservesDegree (G : (U × W) ≃ₗ[A] (U × W))
    (hG : PreservesDegree (fun i => (GU i).prod (GW i))
      (fun i => (GU i).prod (GW i)) G.toLinearMap) :
    PreservesDegree (fun i => (GU i).prod (GW i))
      (fun i => (GU i).prod (GW i)) G.symm.toLinearMap := by
  intro i z hz
  have he := product_map_component GU GW G.toLinearMap hG i (G.symm z)
  simp only [LinearEquiv.coe_coe, G.apply_symm_apply,
    decompose_of_mem_same GU hz.1, decompose_of_mem_same GW hz.2] at he
  have hx := G.injective (he.trans (G.apply_symm_apply z).symm)
  have hm : ((decompose GU (G.symm z).1 i : U), (decompose GW (G.symm z).2 i : W)) ∈
      (GU i).prod (GW i) :=
    ⟨(decompose GU (G.symm z).1 i).property, (decompose GW (G.symm z).2 i).property⟩
  exact hx ▸ hm

omit [Decomposition GW] in
/-- Evenness of a graph transition follows from evenness of the ambient map. -/
theorem transition_preservesDegree (G : Module.End A (U × W))
    (hG : PreservesDegree (fun i => (GU i).prod (GW i))
      (fun i => (GU i).prod (GW i)) G)
    (f : U →ₗ[A] W) (hf : PreservesDegree GU GW f) (h : Overlap G f) :
    PreservesDegree GU GW (transition G f h) := by
  have hd : PreservesDegree GU GU (denominator G f) :=
    fun i x hx => (hG i (x, f x) ⟨hx, hf i x hx⟩).1
  have hn : PreservesDegree GU GW (numerator G f) :=
    fun i x hx => (hG i (x, f x) ⟨hx, hf i x hx⟩).2
  have hi := preservesDegree_symm GU GU
    (LinearEquiv.ofBijective (denominator G f) h) hd
  exact fun i x hx => hn i _ (hi i x hx)

/-- The overlap equivalence restricts to genuine even graph coordinates. -/
noncomputable def gradedOverlapEquiv (G : (U × W) ≃ₗ[A] (U × W))
    (hG : PreservesDegree (fun i => (GU i).prod (GW i))
      (fun i => (GU i).prod (GW i)) G.toLinearMap) :
    {f : U →ₗ[A] W // Overlap G.toLinearMap f ∧ PreservesDegree GU GW f} ≃
      {f : U →ₗ[A] W // Overlap G.symm.toLinearMap f ∧ PreservesDegree GU GW f} where
  toFun f := ⟨transition G.toLinearMap f.val f.property.1,
    overlap_inverse G f.val f.property.1,
    transition_preservesDegree GU GW G.toLinearMap hG f.val f.property.2 f.property.1⟩
  invFun f := ⟨transition G.symm.toLinearMap f.val f.property.1,
    overlap_inverse G.symm f.val f.property.1,
    transition_preservesDegree GU GW G.symm.toLinearMap
      (product_inverse_preservesDegree GU GW G hG) f.val f.property.2 f.property.1⟩
  left_inv f := Subtype.ext (transition_inverse G f.val f.property.1)
  right_inv f := Subtype.ext (transition_inverse G.symm f.val f.property.1)

end InfoGeometry.SuperGrassmannian.GradedGraphCocycle
