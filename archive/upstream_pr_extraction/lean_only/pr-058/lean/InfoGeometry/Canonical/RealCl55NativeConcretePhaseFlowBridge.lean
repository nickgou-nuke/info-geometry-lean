import Mathlib
import InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge

/-!
# Native real phase flow on the concrete Hestenes image

The concrete Hestenes phase is already an automorphism of the native range
submodule.  This owner packages its elementary trigonometric rotation flow
there, including the group law.  It is an algebraic real rotation law only:
no operator exponential, norm completion, or Tomita--Takesaki flow is claimed.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55NativeConcretePhaseFlowBridge

open InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge
open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

def nativeConcretePhaseFlowOnImage (t : ℝ) :
    nativeConcreteHestenesImage →ₗ[ℝ] nativeConcreteHestenesImage where
  toFun x :=
    Real.cos t • x + Real.sin t • nativeConcretePhaseOnImage x
  map_add' x y := by
    simp only [map_add, smul_add]
    abel
  map_smul' c x := by
    apply Subtype.ext
    change Real.cos t • (c • x.1) + Real.sin t •
        (nativeConcretePhaseOnImage (c • x)).1 =
      c • (Real.cos t • x.1 + Real.sin t •
        (nativeConcretePhaseOnImage x).1)
    have hphase := congrArg Subtype.val
      (nativeConcretePhaseOnImage.map_smul c x)
    have hphase' :
        (nativeConcretePhaseOnImage (c • x)).1 =
          c • (nativeConcretePhaseOnImage x).1 := by
      exact hphase
    rw [hphase', smul_add, smul_smul, smul_smul]
    module

noncomputable def nativeConcreteDiracActionOnImage
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeConcreteHestenesImage →ₗ[ℝ] nativeConcreteHestenesImage where
  toFun z :=
    ⟨nativeConcreteDiracAction v φ z.1, by
      rcases z.2 with ⟨x, hx⟩
      refine ⟨concreteDirac3 v φ x, ?_⟩
      rw [← hx]
      exact (nativeConcreteDiracAction_intertwines v φ x).symm⟩
  map_add' x y := by
    apply Subtype.ext
    simp [map_add]
  map_smul' c x := by
    apply Subtype.ext
    simp [map_smul]

theorem nativeConcreteDiracActionOnImage_intertwines_embeddingEquiv
    (v : V3) (φ : Module.Dual ℝ V3) (x : DoubledExterior3) :
    nativeConcreteDiracActionOnImage v φ
        (nativeConcreteHestenesEmbeddingEquiv x) =
      nativeConcreteHestenesEmbeddingEquiv (concreteDirac3 v φ x) := by
  apply Subtype.ext
  change nativeConcreteDiracAction v φ
      (nativeConcreteHestenesEmbedding x) =
    nativeConcreteHestenesEmbedding (concreteDirac3 v φ x)
  exact nativeConcreteDiracAction_intertwines v φ x

@[simp] theorem nativeConcretePhaseFlowOnImage_zero :
    nativeConcretePhaseFlowOnImage 0 =
      (1 : nativeConcreteHestenesImage →ₗ[ℝ] nativeConcreteHestenesImage) := by
  apply LinearMap.ext
  intro x
  simp [nativeConcretePhaseFlowOnImage]

theorem nativeConcretePhaseFlowOnImage_add (s t : ℝ) :
    nativeConcretePhaseFlowOnImage (s + t) =
      (nativeConcretePhaseFlowOnImage s).comp
        (nativeConcretePhaseFlowOnImage t) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change Real.cos (s + t) • x + Real.sin (s + t) •
      (nativeConcretePhaseOnImage x).1 =
    Real.cos s •
        (Real.cos t • x.1 + Real.sin t •
          (nativeConcretePhaseOnImage x).1) +
      Real.sin s •
        (nativeConcretePhaseOnImage
          (Real.cos t • x + Real.sin t • nativeConcretePhaseOnImage x)).1
  rw [Real.cos_add, Real.sin_add]
  have hphase := congrArg Subtype.val
    (nativeConcretePhaseOnImage.map_add
      (Real.cos t • x) (Real.sin t • nativeConcretePhaseOnImage x))
  have hphase' :
      (nativeConcretePhaseOnImage
        (Real.cos t • x + Real.sin t • nativeConcretePhaseOnImage x)).1 =
        Real.cos t • (nativeConcretePhaseOnImage x).1 +
          Real.sin t •
            (nativeConcretePhaseOnImage
              (nativeConcretePhaseOnImage x)).1 := by
    simp only [map_smul] at hphase
    exact hphase
  rw [hphase', nativeConcretePhaseOnImage_sq_apply]
  have hneg : ((-x : nativeConcreteHestenesImage).1) = -x.1 := rfl
  rw [hneg]
  simp only [smul_add, smul_smul]
  module

theorem nativeConcretePhaseFlowOnImage_intertwines_embeddingEquiv
    (t : ℝ) (x : DoubledExterior3) :
    nativeConcretePhaseFlowOnImage t
        (nativeConcreteHestenesEmbeddingEquiv x) =
      nativeConcreteHestenesEmbeddingEquiv
        (concreteHestenesPhaseFlow t x) := by
  apply Subtype.ext
  change Real.cos t • nativeConcreteHestenesEmbedding x +
      Real.sin t • nativeConcretePhaseAction
        (nativeConcreteHestenesEmbedding x) =
    nativeConcreteHestenesEmbedding (concreteHestenesPhaseFlow t x)
  rw [nativeConcretePhaseAction_intertwines]
  rw [concreteHestenesPhaseFlow_eq_linear_combination t]
  simp only [LinearMap.add_apply, LinearMap.smul_apply,
    map_add, map_smul, Module.End.one_apply]

theorem nativeConcretePhaseFlowOnImage_intertwines_dirac
    (t : ℝ)
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3)
    (x : DoubledExterior3) :
    nativeConcretePhaseFlowOnImage t
        (nativeConcreteDiracActionOnImage v φ
          (nativeConcreteHestenesEmbeddingEquiv x)) =
      nativeConcreteDiracActionOnImage v φ
        (nativeConcretePhaseFlowOnImage t
          (nativeConcreteHestenesEmbeddingEquiv x)) := by
  rw [nativeConcreteDiracActionOnImage_intertwines_embeddingEquiv,
    nativeConcretePhaseFlowOnImage_intertwines_embeddingEquiv,
    nativeConcretePhaseFlowOnImage_intertwines_embeddingEquiv,
    nativeConcreteDiracActionOnImage_intertwines_embeddingEquiv]
  have h := congrArg
    (fun T : DoubledExterior3End => T x)
    (concreteHestenesPhaseFlow_commutes_dirac t v φ)
  apply Subtype.ext
  change nativeConcreteHestenesEmbedding
      (concreteHestenesPhaseFlow t (concreteDirac3 v φ x)) =
    nativeConcreteHestenesEmbedding
      (concreteDirac3 v φ (concreteHestenesPhaseFlow t x))
  simpa only [Module.End.mul_apply] using
    congrArg nativeConcreteHestenesEmbedding h

noncomputable def nativeConcreteLaplacianActionOnImage
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeConcreteHestenesImage →ₗ[ℝ] nativeConcreteHestenesImage where
  toFun z :=
    ⟨nativeConcreteLaplacianAction v φ z.1, by
      rcases z.2 with ⟨x, hx⟩
      refine ⟨concreteLaplacian3 v φ x, ?_⟩
      rw [← hx]
      exact (nativeConcreteLaplacianAction_intertwines v φ x).symm⟩
  map_add' x y := by
    apply Subtype.ext
    simp [map_add]
  map_smul' c x := by
    apply Subtype.ext
    simp [map_smul]

theorem nativeConcreteLaplacianActionOnImage_intertwines_embeddingEquiv
    (v : V3) (φ : Module.Dual ℝ V3) (x : DoubledExterior3) :
    nativeConcreteLaplacianActionOnImage v φ
        (nativeConcreteHestenesEmbeddingEquiv x) =
      nativeConcreteHestenesEmbeddingEquiv (concreteLaplacian3 v φ x) := by
  apply Subtype.ext
  change nativeConcreteLaplacianAction v φ
      (nativeConcreteHestenesEmbedding x) =
    nativeConcreteHestenesEmbedding (concreteLaplacian3 v φ x)
  exact nativeConcreteLaplacianAction_intertwines v φ x

theorem concreteHestenesPhaseFlow_commutes_laplacian
    (t : ℝ) (v : V3) (φ : Module.Dual ℝ V3) :
    concreteHestenesPhaseFlow t ∘ₗ concreteLaplacian3 v φ =
      concreteLaplacian3 v φ ∘ₗ concreteHestenesPhaseFlow t := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  have hsqx :
      concreteDirac3 v φ (concreteDirac3 v φ x) =
        concreteLaplacian3 v φ x := by
    simpa only [Module.End.mul_apply] using
      congrArg (fun T : DoubledExterior3End => T x)
        (concreteDirac3_sq v φ)
  have hsqflow :
      concreteDirac3 v φ (concreteDirac3 v φ
        (concreteHestenesPhaseFlow t x)) =
        concreteLaplacian3 v φ (concreteHestenesPhaseFlow t x) := by
    simpa only [Module.End.mul_apply] using
      congrArg (fun T : DoubledExterior3End =>
        T (concreteHestenesPhaseFlow t x)) (concreteDirac3_sq v φ)
  rw [← hsqx, ← hsqflow]
  have hdirac (y : DoubledExterior3) :
      concreteHestenesPhaseFlow t (concreteDirac3 v φ y) =
        concreteDirac3 v φ (concreteHestenesPhaseFlow t y) := by
    simpa only [LinearMap.comp_apply] using congrArg
      (fun T : DoubledExterior3End => T y)
      (concreteHestenesPhaseFlow_commutes_dirac t v φ)
  calc
    concreteHestenesPhaseFlow t
        (concreteDirac3 v φ (concreteDirac3 v φ x)) =
        concreteDirac3 v φ
          (concreteHestenesPhaseFlow t (concreteDirac3 v φ x)) :=
      hdirac (concreteDirac3 v φ x)
    _ = concreteDirac3 v φ
        (concreteDirac3 v φ (concreteHestenesPhaseFlow t x)) := by
      rw [hdirac x]

theorem nativeConcretePhaseFlowOnImage_intertwines_laplacian
    (t : ℝ) (v : V3) (φ : Module.Dual ℝ V3) (x : DoubledExterior3) :
    nativeConcretePhaseFlowOnImage t
        (nativeConcreteLaplacianActionOnImage v φ
          (nativeConcreteHestenesEmbeddingEquiv x)) =
      nativeConcreteLaplacianActionOnImage v φ
        (nativeConcretePhaseFlowOnImage t
          (nativeConcreteHestenesEmbeddingEquiv x)) := by
  rw [nativeConcreteLaplacianActionOnImage_intertwines_embeddingEquiv,
    nativeConcretePhaseFlowOnImage_intertwines_embeddingEquiv,
    nativeConcretePhaseFlowOnImage_intertwines_embeddingEquiv,
    nativeConcreteLaplacianActionOnImage_intertwines_embeddingEquiv]
  have h := congrArg
    (fun T : DoubledExterior3End => T x)
    (concreteHestenesPhaseFlow_commutes_laplacian t v φ)
  apply Subtype.ext
  change nativeConcreteHestenesEmbedding
      (concreteHestenesPhaseFlow t (concreteLaplacian3 v φ x)) =
    nativeConcreteHestenesEmbedding
      (concreteLaplacian3 v φ (concreteHestenesPhaseFlow t x))
  simpa only [Module.End.mul_apply] using
    congrArg nativeConcreteHestenesEmbedding h

end InfoGeometry.Canonical.RealCl55NativeConcretePhaseFlowBridge
