import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge
import InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
import InfoGeometry.Canonical.RealCl55NativeConcretePhaseFlowBridge
import InfoGeometry.Canonical.ChiralHodgeDiracBlockBridge

/-!
# Native Cl(5,5) embedding of the doubled intrinsic Witt carrier

The intrinsic split-octonion Witt carrier is eight-dimensional.  The concrete
Hestenes phase acts on its real doubling, so this owner first transports two
copies of the Witt carrier to the existing exterior-algebra carrier and only
then uses the native 32-dimensional Cl(5,5) embedding.  The result is an
explicit linear embedding and phase intertwiner; no 8-to-32 dimensional
equivalence or Clifford representation claim is made.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55NativeWittHestenesDoublingBridge

open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
open InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge
open InfoGeometry.Canonical.RealCl55NativeConcretePhaseFlowBridge
open InfoGeometry.Canonical.ChiralHodgeDiracBlockBridge

abbrev WittCarrier := PeirceCarrier
abbrev DoubledWittCarrier := WittCarrier × WittCarrier

noncomputable def wittToExterior3 : WittCarrier ≃ₗ[ℝ] Exterior3 :=
  exterior3SplitOctonionCoordinateEquiv.symm

noncomputable def doubledWittToExterior3 :
    DoubledWittCarrier ≃ₗ[ℝ] DoubledExterior3 :=
  LinearEquiv.prodCongr wittToExterior3 wittToExterior3

def doubledWittHestenesPhase :
    DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier where
  toFun x := (-x.2, x.1)
  map_add' x y := by
    ext <;> simp [add_comm]
  map_smul' c x := by
    ext <;> simp

@[simp] theorem doubledWittHestenesPhase_apply
    (x : DoubledWittCarrier) :
    doubledWittHestenesPhase x = (-x.2, x.1) := rfl

theorem doubledWittHestenesPhase_sq :
    doubledWittHestenesPhase * doubledWittHestenesPhase =
      -(1 : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier) := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  simp [doubledWittHestenesPhase]

theorem doubledWittToExterior3_intertwines_phase
    (x : DoubledWittCarrier) :
    doubledWittToExterior3 (doubledWittHestenesPhase x) =
      hestenesPhase3 (doubledWittToExterior3 x) := by
  rcases x with ⟨x, y⟩
  simp [doubledWittToExterior3, doubledWittHestenesPhase,
    wittToExterior3, hestenesPhase3]

noncomputable def doubledWittDirac
    (v : V3) (φ : Module.Dual ℝ V3) :
    DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier :=
  doubledWittToExterior3.symm.toLinearMap.comp
    ((concreteDirac3 v φ).comp doubledWittToExterior3.toLinearMap)

noncomputable def doubledWittLaplacian
    (v : V3) (φ : Module.Dual ℝ V3) :
    DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier :=
  doubledWittToExterior3.symm.toLinearMap.comp
    ((concreteLaplacian3 v φ).comp doubledWittToExterior3.toLinearMap)

theorem doubledWittDirac_intertwines
    (v : V3) (φ : Module.Dual ℝ V3) (x : DoubledWittCarrier) :
    doubledWittToExterior3 (doubledWittDirac v φ x) =
      concreteDirac3 v φ (doubledWittToExterior3 x) := by
  simp [doubledWittDirac]

theorem doubledWittLaplacian_intertwines
    (v : V3) (φ : Module.Dual ℝ V3) (x : DoubledWittCarrier) :
    doubledWittToExterior3 (doubledWittLaplacian v φ x) =
      concreteLaplacian3 v φ (doubledWittToExterior3 x) := by
  simp [doubledWittLaplacian]

theorem doubledWittDirac_sq
    (v : V3) (φ : Module.Dual ℝ V3) :
    doubledWittDirac v φ * doubledWittDirac v φ =
      doubledWittLaplacian v φ := by
  apply LinearMap.ext
  intro x
  apply doubledWittToExterior3.injective
  change doubledWittToExterior3
      (doubledWittDirac v φ (doubledWittDirac v φ x)) =
    doubledWittToExterior3 (doubledWittLaplacian v φ x)
  rw [doubledWittDirac_intertwines, doubledWittDirac_intertwines,
    doubledWittLaplacian_intertwines]
  simpa only [Module.End.mul_apply] using
    congrArg (fun T : DoubledExterior3End =>
      T (doubledWittToExterior3 x)) (concreteDirac3_sq v φ)

theorem doubledWittHestenesPhase_commutes_dirac
    (v : V3) (φ : Module.Dual ℝ V3) :
    doubledWittHestenesPhase.comp (doubledWittDirac v φ) =
      (doubledWittDirac v φ).comp doubledWittHestenesPhase := by
  apply LinearMap.ext
  intro x
  apply doubledWittToExterior3.injective
  change doubledWittToExterior3
      (doubledWittHestenesPhase (doubledWittDirac v φ x)) =
    doubledWittToExterior3
      (doubledWittDirac v φ (doubledWittHestenesPhase x))
  rw [doubledWittToExterior3_intertwines_phase,
    doubledWittDirac_intertwines,
    doubledWittDirac_intertwines,
    doubledWittToExterior3_intertwines_phase]
  simpa only [LinearMap.comp_apply] using congrArg
    (fun T : DoubledExterior3End => T (doubledWittToExterior3 x))
    (concreteDirac3_phase v φ)

noncomputable def doubledWittChirality :
    DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier :=
  doubledWittToExterior3.symm.toLinearMap.comp
    (concreteChirality3.comp doubledWittToExterior3.toLinearMap)

theorem doubledWittChirality_intertwines
    (x : DoubledWittCarrier) :
    doubledWittToExterior3 (doubledWittChirality x) =
      concreteChirality3 (doubledWittToExterior3 x) := by
  simp [doubledWittChirality]

theorem doubledWittChirality_sq :
    doubledWittChirality * doubledWittChirality =
      (1 : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier) := by
  apply LinearMap.ext
  intro x
  apply doubledWittToExterior3.injective
  change doubledWittToExterior3
      (doubledWittChirality (doubledWittChirality x)) =
    doubledWittToExterior3 x
  rw [doubledWittChirality_intertwines,
    doubledWittChirality_intertwines]
  simpa only [Module.End.mul_apply] using
    congrArg (fun T : DoubledExterior3End =>
      T (doubledWittToExterior3 x)) (concreteChirality3_sq)

theorem doubledWittChirality_dirac_odd
    (v : V3) (φ : Module.Dual ℝ V3) :
    doubledWittChirality.comp (doubledWittDirac v φ) =
      -(doubledWittDirac v φ).comp doubledWittChirality := by
  apply LinearMap.ext
  intro x
  apply doubledWittToExterior3.injective
  change doubledWittToExterior3
      (doubledWittChirality (doubledWittDirac v φ x)) =
    doubledWittToExterior3
      (-(doubledWittDirac v φ (doubledWittChirality x)))
  rw [doubledWittChirality_intertwines,
    doubledWittDirac_intertwines]
  have hright :
      doubledWittToExterior3
          (-(doubledWittDirac v φ (doubledWittChirality x))) =
        -(concreteDirac3 v φ
          (concreteChirality3 (doubledWittToExterior3 x))) := by
    rw [map_neg, doubledWittDirac_intertwines,
      doubledWittChirality_intertwines]
  rw [hright]
  have h := congrArg (fun T : DoubledExterior3End =>
      T (doubledWittToExterior3 x))
    (concreteChirality3_odd v φ)
  simpa only [map_neg, LinearMap.comp_apply] using h

theorem doubledWittHestenesPhase_commutes_chirality :
    doubledWittHestenesPhase.comp doubledWittChirality =
      doubledWittChirality.comp doubledWittHestenesPhase := by
  apply LinearMap.ext
  intro x
  apply doubledWittToExterior3.injective
  change doubledWittToExterior3
      (doubledWittHestenesPhase (doubledWittChirality x)) =
    doubledWittToExterior3
      (doubledWittChirality (doubledWittHestenesPhase x))
  rw [doubledWittToExterior3_intertwines_phase,
    doubledWittChirality_intertwines,
    doubledWittChirality_intertwines,
    doubledWittToExterior3_intertwines_phase]
  simpa only [LinearMap.comp_apply] using congrArg
    (fun T : DoubledExterior3End => T (doubledWittToExterior3 x))
    concreteHestenesPhase_chirality_commutes

noncomputable def doubledWittChiralProjectorPlus :
    DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier :=
  (1 / 2 : ℝ) •
    ((1 : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier) +
      doubledWittChirality)

noncomputable def doubledWittChiralProjectorMinus :
    DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier :=
  (1 / 2 : ℝ) •
    ((1 : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier) -
      doubledWittChirality)

theorem doubledWittChiralProjectors_sum :
    doubledWittChiralProjectorPlus + doubledWittChiralProjectorMinus =
      (1 : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier) := by
  unfold doubledWittChiralProjectorPlus doubledWittChiralProjectorMinus
  module

theorem doubledWittChiralProjectors_orthogonal :
    doubledWittChiralProjectorPlus.comp doubledWittChiralProjectorMinus =
      0 := by
  apply LinearMap.ext
  intro x
  have hγ : doubledWittChirality (doubledWittChirality x) = x := by
    have h := congrArg
      (fun T : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier => T x)
      doubledWittChirality_sq
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  change doubledWittChiralProjectorPlus
      (doubledWittChiralProjectorMinus x) = 0
  unfold doubledWittChiralProjectorPlus doubledWittChiralProjectorMinus
  change (1 / 2 : ℝ) •
      ((1 : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier) +
        doubledWittChirality)
        ((1 / 2 : ℝ) •
          ((1 : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier) -
            doubledWittChirality) x) = 0
  rw [map_smul]
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    Module.End.one_apply, map_sub, hγ]
  module

theorem doubledWittChiralProjectorPlus_sq :
    doubledWittChiralProjectorPlus.comp
        doubledWittChiralProjectorPlus =
      doubledWittChiralProjectorPlus := by
  apply LinearMap.ext
  intro x
  have hγ : doubledWittChirality (doubledWittChirality x) = x := by
    have h := congrArg
      (fun T : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier => T x)
      doubledWittChirality_sq
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  change doubledWittChiralProjectorPlus
      (doubledWittChiralProjectorPlus x) =
    doubledWittChiralProjectorPlus x
  unfold doubledWittChiralProjectorPlus
  simp [LinearMap.smul_apply, hγ]
  module

theorem doubledWittChiralProjectorMinus_sq :
    doubledWittChiralProjectorMinus.comp
        doubledWittChiralProjectorMinus =
      doubledWittChiralProjectorMinus := by
  apply LinearMap.ext
  intro x
  have hγ : doubledWittChirality (doubledWittChirality x) = x := by
    have h := congrArg
      (fun T : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier => T x)
      doubledWittChirality_sq
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  change doubledWittChiralProjectorMinus
      (doubledWittChiralProjectorMinus x) =
    doubledWittChiralProjectorMinus x
  unfold doubledWittChiralProjectorMinus
  simp [LinearMap.smul_apply, hγ]
  module

theorem doubledWittChiralProjectors_orthogonal_reverse :
    doubledWittChiralProjectorMinus.comp doubledWittChiralProjectorPlus =
      0 := by
  apply LinearMap.ext
  intro x
  have hγ : doubledWittChirality (doubledWittChirality x) = x := by
    have h := congrArg
      (fun T : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier => T x)
      doubledWittChirality_sq
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  change doubledWittChiralProjectorMinus
      (doubledWittChiralProjectorPlus x) = 0
  unfold doubledWittChiralProjectorPlus doubledWittChiralProjectorMinus
  simp [LinearMap.smul_apply, hγ]
  module

noncomputable def doubledWittChiralDiracPlus
    (v : V3) (φ : Module.Dual ℝ V3) :
    DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier :=
  chiralDiracPlus (doubledWittDirac v φ) doubledWittChirality

noncomputable def doubledWittChiralDiracMinus
    (v : V3) (φ : Module.Dual ℝ V3) :
    DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier :=
  chiralDiracMinus (doubledWittDirac v φ) doubledWittChirality

theorem doubledWittChiralDiracPlus_sq_zero
    (v : V3) (φ : Module.Dual ℝ V3) :
    doubledWittChiralDiracPlus v φ * doubledWittChiralDiracPlus v φ = 0 := by
  exact chiralDiracPlus_sq_zero doubledWittChirality
    (doubledWittDirac v φ) doubledWittChirality_sq
    (doubledWittChirality_dirac_odd v φ)

theorem doubledWittChiralDiracMinus_sq_zero
    (v : V3) (φ : Module.Dual ℝ V3) :
    doubledWittChiralDiracMinus v φ * doubledWittChiralDiracMinus v φ = 0 := by
  exact chiralDiracMinus_sq_zero doubledWittChirality
    (doubledWittDirac v φ) doubledWittChirality_sq
    (doubledWittChirality_dirac_odd v φ)

theorem doubledWittChiralDirac_decomposition
    (v : V3) (φ : Module.Dual ℝ V3) :
    doubledWittDirac v φ =
      doubledWittChiralDiracPlus v φ + doubledWittChiralDiracMinus v φ := by
  exact chiralDirac_decomposition doubledWittChirality
    (doubledWittDirac v φ) doubledWittChirality_sq
    (doubledWittChirality_dirac_odd v φ)

noncomputable def nativeWittHestenesEmbedding :
    DoubledWittCarrier →ₗ[ℝ] NativeSpinorCarrier :=
  nativeConcreteHestenesEmbedding.comp
    doubledWittToExterior3.toLinearMap

theorem nativeWittHestenesEmbedding_injective :
    Function.Injective nativeWittHestenesEmbedding := by
  intro x y hxy
  apply doubledWittToExterior3.injective
  apply nativeConcreteHestenesEmbedding_injective
  exact hxy

noncomputable def nativeWittHestenesImage :
    Submodule ℝ NativeSpinorCarrier :=
  LinearMap.range nativeWittHestenesEmbedding

noncomputable def nativeWittHestenesEmbeddingToImage :
    DoubledWittCarrier →ₗ[ℝ] nativeWittHestenesImage :=
  nativeWittHestenesEmbedding.codRestrict
    nativeWittHestenesImage (fun x => ⟨x, rfl⟩)

theorem nativeWittHestenesEmbeddingToImage_bijective :
    Function.Bijective nativeWittHestenesEmbeddingToImage := by
  constructor
  · intro x y hxy
    apply nativeWittHestenesEmbedding_injective
    exact congrArg Subtype.val hxy
  · intro y
    rcases y.2 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

noncomputable def nativeWittHestenesEmbeddingEquiv :
    DoubledWittCarrier ≃ₗ[ℝ] nativeWittHestenesImage :=
  LinearEquiv.ofBijective nativeWittHestenesEmbeddingToImage
    nativeWittHestenesEmbeddingToImage_bijective

noncomputable def nativeWittChiralityOnImage :
    nativeWittHestenesImage →ₗ[ℝ] nativeWittHestenesImage :=
  nativeWittHestenesEmbeddingEquiv.toLinearMap.comp
    (doubledWittChirality.comp
      nativeWittHestenesEmbeddingEquiv.symm.toLinearMap)

theorem nativeWittChiralityOnImage_intertwines
    (x : DoubledWittCarrier) :
    nativeWittChiralityOnImage
        (nativeWittHestenesEmbeddingEquiv x) =
      nativeWittHestenesEmbeddingEquiv (doubledWittChirality x) := by
  simp [nativeWittChiralityOnImage]

theorem nativeWittChiralityOnImage_sq :
    nativeWittChiralityOnImage.comp nativeWittChiralityOnImage =
      (1 : nativeWittHestenesImage →ₗ[ℝ] nativeWittHestenesImage) := by
  apply LinearMap.ext
  intro z
  let x := nativeWittHestenesEmbeddingEquiv.symm z
  have hγ : doubledWittChirality (doubledWittChirality x) = x := by
    have h := congrArg
      (fun T : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier => T x)
      doubledWittChirality_sq
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  dsimp [nativeWittChiralityOnImage]
  rw [nativeWittHestenesEmbeddingEquiv.symm_apply_apply]
  change nativeWittHestenesEmbeddingEquiv
      (doubledWittChirality
        (doubledWittChirality
          (nativeWittHestenesEmbeddingEquiv.symm z))) = z
  rw [hγ]
  exact nativeWittHestenesEmbeddingEquiv.apply_symm_apply z

noncomputable def nativeWittPhaseOnImage :
    nativeWittHestenesImage →ₗ[ℝ] nativeWittHestenesImage :=
  nativeWittHestenesEmbeddingEquiv.toLinearMap.comp
    (doubledWittHestenesPhase.comp
      nativeWittHestenesEmbeddingEquiv.symm.toLinearMap)

theorem nativeWittPhaseOnImage_intertwines
    (x : DoubledWittCarrier) :
    nativeWittPhaseOnImage
        (nativeWittHestenesEmbeddingEquiv x) =
      nativeWittHestenesEmbeddingEquiv (doubledWittHestenesPhase x) := by
  simp [nativeWittPhaseOnImage]

theorem nativeWittPhaseOnImage_chirality_commutes :
    nativeWittPhaseOnImage.comp nativeWittChiralityOnImage =
      nativeWittChiralityOnImage.comp nativeWittPhaseOnImage := by
  apply LinearMap.ext
  intro z
  let x := nativeWittHestenesEmbeddingEquiv.symm z
  change nativeWittPhaseOnImage
      (nativeWittChiralityOnImage z) =
    nativeWittChiralityOnImage (nativeWittPhaseOnImage z)
  rw [show z = nativeWittHestenesEmbeddingEquiv x by
    exact (nativeWittHestenesEmbeddingEquiv.apply_symm_apply z).symm,
    nativeWittChiralityOnImage_intertwines,
    nativeWittPhaseOnImage_intertwines,
    nativeWittPhaseOnImage_intertwines,
    nativeWittChiralityOnImage_intertwines]
  simpa only [LinearMap.comp_apply] using congrArg
    nativeWittHestenesEmbeddingEquiv
    (congrArg
      (fun T : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier => T x)
      doubledWittHestenesPhase_commutes_chirality)

theorem nativeWittPhaseOnImage_sq :
    nativeWittPhaseOnImage.comp nativeWittPhaseOnImage =
      -(1 : nativeWittHestenesImage →ₗ[ℝ] nativeWittHestenesImage) := by
  apply LinearMap.ext
  intro z
  let x := nativeWittHestenesEmbeddingEquiv.symm z
  change nativeWittPhaseOnImage
      (nativeWittPhaseOnImage z) = -z
  rw [show z = nativeWittHestenesEmbeddingEquiv x by
    exact (nativeWittHestenesEmbeddingEquiv.apply_symm_apply z).symm,
    nativeWittPhaseOnImage_intertwines,
    nativeWittPhaseOnImage_intertwines]
  have hphase : doubledWittHestenesPhase
      (doubledWittHestenesPhase x) = -x := by
    have h := congrArg
      (fun T : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier => T x)
      doubledWittHestenesPhase_sq
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  rw [hphase]
  exact map_neg nativeWittHestenesEmbeddingEquiv x

noncomputable def nativeWittChiralProjectorPlusOnImage :
    nativeWittHestenesImage →ₗ[ℝ] nativeWittHestenesImage :=
  chiralProjectorPlus nativeWittChiralityOnImage

noncomputable def nativeWittChiralProjectorMinusOnImage :
    nativeWittHestenesImage →ₗ[ℝ] nativeWittHestenesImage :=
  chiralProjectorMinus nativeWittChiralityOnImage

theorem nativeWittChiralProjectorPlusOnImage_sq :
    nativeWittChiralProjectorPlusOnImage.comp
        nativeWittChiralProjectorPlusOnImage =
      nativeWittChiralProjectorPlusOnImage := by
  exact chiralProjectorPlus_sq nativeWittChiralityOnImage
    nativeWittChiralityOnImage_sq

theorem nativeWittChiralProjectorMinusOnImage_sq :
    nativeWittChiralProjectorMinusOnImage.comp
        nativeWittChiralProjectorMinusOnImage =
      nativeWittChiralProjectorMinusOnImage := by
  exact chiralProjectorMinus_sq nativeWittChiralityOnImage
    nativeWittChiralityOnImage_sq

theorem nativeWittChiralProjectorsOnImage_orthogonal :
    nativeWittChiralProjectorPlusOnImage.comp
        nativeWittChiralProjectorMinusOnImage = 0 ∧
    nativeWittChiralProjectorMinusOnImage.comp
        nativeWittChiralProjectorPlusOnImage = 0 := by
  exact chiralProjector_orthogonal nativeWittChiralityOnImage
    nativeWittChiralityOnImage_sq

theorem nativeWittChiralProjectorsOnImage_sum :
    nativeWittChiralProjectorPlusOnImage +
        nativeWittChiralProjectorMinusOnImage =
      (1 : nativeWittHestenesImage →ₗ[ℝ] nativeWittHestenesImage) := by
  exact chiralProjector_sum nativeWittChiralityOnImage

/-- The explicit basis-compatibility datum needed to identify the global
Cl(5,5) parity matrix with the transported Witt chirality on the embedded
sector.  This is deliberately a datum rather than an unproved identification:
the native matrix carrier uses a separate finite-index reindexing. -/
structure NativeWittChiralBasisCompatibility : Prop where
  native_chirality_intertwines :
    ∀ x : DoubledWittCarrier,
      RealCl55FiniteModuleEndBridge.nativeChirality
          (nativeWittHestenesEmbedding x) =
        nativeWittHestenesEmbedding (doubledWittChirality x)

noncomputable def globalNativeChiralityOnWittImage
    (h : NativeWittChiralBasisCompatibility) :
    nativeWittHestenesImage →ₗ[ℝ] nativeWittHestenesImage where
  toFun z :=
    ⟨RealCl55FiniteModuleEndBridge.nativeChirality z.1, by
      rcases z.2 with ⟨x, hx⟩
      refine ⟨doubledWittChirality x, ?_⟩
      rw [← hx, h.native_chirality_intertwines]⟩
  map_add' x y := by
    apply Subtype.ext
    simp [map_add]
  map_smul' c x := by
    apply Subtype.ext
    simp [map_smul]

theorem globalNativeChiralityOnWittImage_intertwines
    (h : NativeWittChiralBasisCompatibility) (x : DoubledWittCarrier) :
    globalNativeChiralityOnWittImage h
        (nativeWittHestenesEmbeddingEquiv x) =
      nativeWittHestenesEmbeddingEquiv (doubledWittChirality x) := by
  apply Subtype.ext
  change RealCl55FiniteModuleEndBridge.nativeChirality
      (nativeWittHestenesEmbedding x) =
    nativeWittHestenesEmbedding (doubledWittChirality x)
  exact h.native_chirality_intertwines x

theorem globalNativeChiralityOnWittImage_eq_transported
    (h : NativeWittChiralBasisCompatibility) :
    globalNativeChiralityOnWittImage h =
      nativeWittChiralityOnImage := by
  apply LinearMap.ext
  intro z
  rcases z.2 with ⟨x, hx⟩
  apply Subtype.ext
  change RealCl55FiniteModuleEndBridge.nativeChirality z.1 =
    nativeWittHestenesEmbedding
      (doubledWittChirality (nativeWittHestenesEmbeddingEquiv.symm z))
  rw [← hx, h.native_chirality_intertwines]
  have hxe : x = nativeWittHestenesEmbeddingEquiv.symm z := by
    apply nativeWittHestenesEmbeddingEquiv.injective
    calc
      nativeWittHestenesEmbeddingEquiv x = z := by
        apply Subtype.ext
        exact hx
      _ = nativeWittHestenesEmbeddingEquiv
          (nativeWittHestenesEmbeddingEquiv.symm z) :=
        (nativeWittHestenesEmbeddingEquiv.apply_symm_apply z).symm
  rw [hxe]

noncomputable def nativeWittDiracOnImage
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeWittHestenesImage →ₗ[ℝ] nativeWittHestenesImage :=
  nativeWittHestenesEmbeddingEquiv.toLinearMap.comp
    ((doubledWittDirac v φ).comp
      nativeWittHestenesEmbeddingEquiv.symm.toLinearMap)

noncomputable def nativeWittLaplacianOnImage
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeWittHestenesImage →ₗ[ℝ] nativeWittHestenesImage :=
  nativeWittHestenesEmbeddingEquiv.toLinearMap.comp
    ((doubledWittLaplacian v φ).comp
      nativeWittHestenesEmbeddingEquiv.symm.toLinearMap)

theorem nativeWittDiracOnImage_intertwines
    (v : V3) (φ : Module.Dual ℝ V3) (x : DoubledWittCarrier) :
    nativeWittDiracOnImage v φ
        (nativeWittHestenesEmbeddingEquiv x) =
      nativeWittHestenesEmbeddingEquiv (doubledWittDirac v φ x) := by
  simp [nativeWittDiracOnImage]

theorem nativeWittPhaseOnImage_dirac_commutes
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeWittPhaseOnImage.comp (nativeWittDiracOnImage v φ) =
      (nativeWittDiracOnImage v φ).comp nativeWittPhaseOnImage := by
  apply LinearMap.ext
  intro z
  let x := nativeWittHestenesEmbeddingEquiv.symm z
  change nativeWittPhaseOnImage
      (nativeWittDiracOnImage v φ z) =
    nativeWittDiracOnImage v φ (nativeWittPhaseOnImage z)
  rw [show z = nativeWittHestenesEmbeddingEquiv x by
    exact (nativeWittHestenesEmbeddingEquiv.apply_symm_apply z).symm,
    nativeWittDiracOnImage_intertwines,
    nativeWittPhaseOnImage_intertwines,
    nativeWittPhaseOnImage_intertwines,
    nativeWittDiracOnImage_intertwines]
  simpa only [LinearMap.comp_apply] using congrArg
    nativeWittHestenesEmbeddingEquiv
    (congrArg
      (fun T : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier => T x)
      (doubledWittHestenesPhase_commutes_dirac v φ))

theorem nativeWittLaplacianOnImage_intertwines
    (v : V3) (φ : Module.Dual ℝ V3) (x : DoubledWittCarrier) :
    nativeWittLaplacianOnImage v φ
        (nativeWittHestenesEmbeddingEquiv x) =
      nativeWittHestenesEmbeddingEquiv (doubledWittLaplacian v φ x) := by
  simp [nativeWittLaplacianOnImage]

theorem nativeWittDiracOnImage_sq
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeWittDiracOnImage v φ * nativeWittDiracOnImage v φ =
      nativeWittLaplacianOnImage v φ := by
  apply LinearMap.ext
  intro z
  let x := nativeWittHestenesEmbeddingEquiv.symm z
  change nativeWittDiracOnImage v φ
      (nativeWittDiracOnImage v φ z) =
    nativeWittLaplacianOnImage v φ z
  rw [show z = nativeWittHestenesEmbeddingEquiv x by
    exact (nativeWittHestenesEmbeddingEquiv.apply_symm_apply z).symm,
    nativeWittDiracOnImage_intertwines,
    nativeWittDiracOnImage_intertwines,
    nativeWittLaplacianOnImage_intertwines]
  simpa only [Module.End.mul_apply] using
    congrArg nativeWittHestenesEmbeddingEquiv
      (congrArg (fun T : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier => T x)
        (doubledWittDirac_sq v φ))

theorem nativeWittChiralityOnImage_dirac_odd
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeWittChiralityOnImage.comp (nativeWittDiracOnImage v φ) =
      -(nativeWittDiracOnImage v φ).comp nativeWittChiralityOnImage := by
  apply LinearMap.ext
  intro z
  let x := nativeWittHestenesEmbeddingEquiv.symm z
  change nativeWittChiralityOnImage
      (nativeWittDiracOnImage v φ z) =
    -(nativeWittDiracOnImage v φ
      (nativeWittChiralityOnImage z))
  rw [show z = nativeWittHestenesEmbeddingEquiv x by
    exact (nativeWittHestenesEmbeddingEquiv.apply_symm_apply z).symm,
    nativeWittDiracOnImage_intertwines,
    nativeWittChiralityOnImage_intertwines,
    nativeWittChiralityOnImage_intertwines,
    nativeWittDiracOnImage_intertwines]
  simpa using congrArg nativeWittHestenesEmbeddingEquiv
    (congrArg
      (fun T : DoubledWittCarrier →ₗ[ℝ] DoubledWittCarrier => T x)
      (doubledWittChirality_dirac_odd v φ))

noncomputable def nativeWittChiralDiracPlusOnImage
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeWittHestenesImage →ₗ[ℝ] nativeWittHestenesImage :=
  chiralDiracPlus (nativeWittDiracOnImage v φ) nativeWittChiralityOnImage

noncomputable def nativeWittChiralDiracMinusOnImage
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeWittHestenesImage →ₗ[ℝ] nativeWittHestenesImage :=
  chiralDiracMinus (nativeWittDiracOnImage v φ) nativeWittChiralityOnImage

theorem nativeWittPhaseOnImage_chiral_blocks_commute
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeWittPhaseOnImage.comp
        (nativeWittChiralDiracPlusOnImage v φ) =
      (nativeWittChiralDiracPlusOnImage v φ).comp nativeWittPhaseOnImage ∧
    nativeWittPhaseOnImage.comp
        (nativeWittChiralDiracMinusOnImage v φ) =
      (nativeWittChiralDiracMinusOnImage v φ).comp nativeWittPhaseOnImage := by
  exact hestenes_phase_commutes_chiral_blocks
    (K := nativeWittPhaseOnImage)
    (Γ := nativeWittChiralityOnImage)
    (D := nativeWittDiracOnImage v φ)
    nativeWittPhaseOnImage_chirality_commutes
    (nativeWittPhaseOnImage_dirac_commutes v φ)
    nativeWittChiralityOnImage_sq
    (nativeWittChiralityOnImage_dirac_odd v φ)

theorem nativeWittChiralDiracPlusOnImage_sq_zero
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeWittChiralDiracPlusOnImage v φ *
        nativeWittChiralDiracPlusOnImage v φ = 0 := by
  exact chiralDiracPlus_sq_zero nativeWittChiralityOnImage
    (nativeWittDiracOnImage v φ) nativeWittChiralityOnImage_sq
    (nativeWittChiralityOnImage_dirac_odd v φ)

theorem nativeWittChiralDiracMinusOnImage_sq_zero
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeWittChiralDiracMinusOnImage v φ *
        nativeWittChiralDiracMinusOnImage v φ = 0 := by
  exact chiralDiracMinus_sq_zero nativeWittChiralityOnImage
    (nativeWittDiracOnImage v φ) nativeWittChiralityOnImage_sq
    (nativeWittChiralityOnImage_dirac_odd v φ)

theorem nativeWittChiralDiracOnImage_decomposition
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeWittDiracOnImage v φ =
      nativeWittChiralDiracPlusOnImage v φ +
        nativeWittChiralDiracMinusOnImage v φ := by
  exact chiralDirac_decomposition nativeWittChiralityOnImage
    (nativeWittDiracOnImage v φ) nativeWittChiralityOnImage_sq
    (nativeWittChiralityOnImage_dirac_odd v φ)

theorem nativeWittLaplacianOnImage_chiral_factorization
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeWittLaplacianOnImage v φ =
      nativeWittChiralDiracMinusOnImage v φ *
          nativeWittChiralDiracPlusOnImage v φ +
        nativeWittChiralDiracPlusOnImage v φ *
          nativeWittChiralDiracMinusOnImage v φ := by
  rw [← nativeWittDiracOnImage_sq v φ]
  calc
    nativeWittDiracOnImage v φ * nativeWittDiracOnImage v φ =
        (nativeWittChiralDiracPlusOnImage v φ +
          nativeWittChiralDiracMinusOnImage v φ) *
          (nativeWittChiralDiracPlusOnImage v φ +
            nativeWittChiralDiracMinusOnImage v φ) := by
      rw [← nativeWittChiralDiracOnImage_decomposition v φ]
    _ = nativeWittChiralDiracMinusOnImage v φ *
          nativeWittChiralDiracPlusOnImage v φ +
        nativeWittChiralDiracPlusOnImage v φ *
          nativeWittChiralDiracMinusOnImage v φ := by
      calc
        (nativeWittChiralDiracPlusOnImage v φ +
            nativeWittChiralDiracMinusOnImage v φ) *
            (nativeWittChiralDiracPlusOnImage v φ +
              nativeWittChiralDiracMinusOnImage v φ) =
          nativeWittChiralDiracPlusOnImage v φ *
              nativeWittChiralDiracPlusOnImage v φ +
            nativeWittChiralDiracPlusOnImage v φ *
              nativeWittChiralDiracMinusOnImage v φ +
            nativeWittChiralDiracMinusOnImage v φ *
              nativeWittChiralDiracPlusOnImage v φ +
            nativeWittChiralDiracMinusOnImage v φ *
              nativeWittChiralDiracMinusOnImage v φ := by noncomm_ring
        _ = 0 + nativeWittChiralDiracPlusOnImage v φ *
              nativeWittChiralDiracMinusOnImage v φ +
            nativeWittChiralDiracMinusOnImage v φ *
              nativeWittChiralDiracPlusOnImage v φ + 0 := by
          rw [nativeWittChiralDiracPlusOnImage_sq_zero,
            nativeWittChiralDiracMinusOnImage_sq_zero]
        _ = nativeWittChiralDiracMinusOnImage v φ *
              nativeWittChiralDiracPlusOnImage v φ +
            nativeWittChiralDiracPlusOnImage v φ *
              nativeWittChiralDiracMinusOnImage v φ := by noncomm_ring

/-- The chiral factorization is the anticommutator identity for the two odd
blocks. -/
theorem nativeWittLaplacianOnImage_chiral_anticommutator
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeWittLaplacianOnImage v φ =
      nativeWittChiralDiracMinusOnImage v φ *
          nativeWittChiralDiracPlusOnImage v φ +
        nativeWittChiralDiracPlusOnImage v φ *
          nativeWittChiralDiracMinusOnImage v φ :=
  nativeWittLaplacianOnImage_chiral_factorization v φ

theorem nativeWittPhaseOnImage_laplacian_commutes
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeWittPhaseOnImage.comp (nativeWittLaplacianOnImage v φ) =
      (nativeWittLaplacianOnImage v φ).comp nativeWittPhaseOnImage := by
  have h_sq : nativeWittLaplacianOnImage v φ =
      nativeWittDiracOnImage v φ * nativeWittDiracOnImage v φ :=
    (nativeWittDiracOnImage_sq v φ).symm
  have hD : nativeWittPhaseOnImage * nativeWittDiracOnImage v φ =
      nativeWittDiracOnImage v φ * nativeWittPhaseOnImage :=
    nativeWittPhaseOnImage_dirac_commutes v φ
  change nativeWittPhaseOnImage * nativeWittLaplacianOnImage v φ =
    nativeWittLaplacianOnImage v φ * nativeWittPhaseOnImage
  rw [h_sq]
  calc
    nativeWittPhaseOnImage * (nativeWittDiracOnImage v φ * nativeWittDiracOnImage v φ) =
      (nativeWittPhaseOnImage * nativeWittDiracOnImage v φ) * nativeWittDiracOnImage v φ := by rw [mul_assoc]
    _ = (nativeWittDiracOnImage v φ * nativeWittPhaseOnImage) * nativeWittDiracOnImage v φ := by rw [hD]
    _ = nativeWittDiracOnImage v φ * (nativeWittPhaseOnImage * nativeWittDiracOnImage v φ) := by rw [← mul_assoc]
    _ = nativeWittDiracOnImage v φ * (nativeWittDiracOnImage v φ * nativeWittPhaseOnImage) := by rw [hD]
    _ = (nativeWittDiracOnImage v φ * nativeWittDiracOnImage v φ) * nativeWittPhaseOnImage := by rw [mul_assoc]

theorem nativeWittHestenesEmbedding_dirac_intertwines
    (v : V3) (φ : Module.Dual ℝ V3) (x : DoubledWittCarrier) :
    nativeConcreteDiracAction v φ (nativeWittHestenesEmbedding x) =
      nativeWittHestenesEmbedding (doubledWittDirac v φ x) := by
  rw [nativeWittHestenesEmbedding, LinearMap.comp_apply,
    nativeConcreteDiracAction_intertwines]
  change nativeConcreteHestenesEmbedding
      (concreteDirac3 v φ (doubledWittToExterior3 x)) =
    nativeConcreteHestenesEmbedding
      (doubledWittToExterior3 (doubledWittDirac v φ x))
  rw [doubledWittDirac_intertwines]

theorem nativeWittHestenesEmbedding_laplacian_intertwines
    (v : V3) (φ : Module.Dual ℝ V3) (x : DoubledWittCarrier) :
    nativeConcreteLaplacianAction v φ (nativeWittHestenesEmbedding x) =
      nativeWittHestenesEmbedding (doubledWittLaplacian v φ x) := by
  rw [nativeWittHestenesEmbedding, LinearMap.comp_apply,
    nativeConcreteLaplacianAction_intertwines]
  change nativeConcreteHestenesEmbedding
      (concreteLaplacian3 v φ (doubledWittToExterior3 x)) =
    nativeConcreteHestenesEmbedding
      (doubledWittToExterior3 (doubledWittLaplacian v φ x))
  rw [doubledWittLaplacian_intertwines]

theorem nativeWittHestenesEmbedding_phase_intertwines
    (x : DoubledWittCarrier) :
    nativeConcretePhaseAction (nativeWittHestenesEmbedding x) =
      nativeWittHestenesEmbedding (doubledWittHestenesPhase x) := by
  rw [nativeWittHestenesEmbedding, LinearMap.comp_apply,
    nativeConcretePhaseAction_intertwines]
  change nativeConcreteHestenesEmbedding
      (hestenesPhase3 (doubledWittToExterior3 x)) =
    nativeConcreteHestenesEmbedding
      (doubledWittToExterior3 (doubledWittHestenesPhase x))
  rw [doubledWittToExterior3_intertwines_phase]

theorem nativeWittHestenesEmbedding_phase_sq
    (x : DoubledWittCarrier) :
    nativeConcretePhaseAction
        (nativeConcretePhaseAction (nativeWittHestenesEmbedding x)) =
      -nativeWittHestenesEmbedding x := by
  rw [nativeWittHestenesEmbedding_phase_intertwines,
    nativeWittHestenesEmbedding_phase_intertwines]
  change nativeWittHestenesEmbedding (-x) =
    -nativeWittHestenesEmbedding x
  exact map_neg nativeWittHestenesEmbedding x

theorem nativeWittHestenesEmbedding_phaseFlow_intertwines
    (t : ℝ) (x : DoubledWittCarrier) :
    nativeConcretePhaseFlowOnImage t
        ⟨nativeWittHestenesEmbedding x,
          ⟨doubledWittToExterior3 x, rfl⟩⟩ =
      ⟨nativeWittHestenesEmbedding
          (Real.cos t • x + Real.sin t • doubledWittHestenesPhase x),
        ⟨doubledWittToExterior3
            (Real.cos t • x + Real.sin t • doubledWittHestenesPhase x), by
          simp [nativeWittHestenesEmbedding, doubledWittToExterior3]⟩⟩ := by
  apply Subtype.ext
  change nativeConcretePhaseFlowOnImage t
      ⟨nativeConcreteHestenesEmbedding (doubledWittToExterior3 x), _⟩ =
    nativeConcreteHestenesEmbedding
      (doubledWittToExterior3
        (Real.cos t • x + Real.sin t • doubledWittHestenesPhase x))
  change Real.cos t • nativeConcreteHestenesEmbedding
        (doubledWittToExterior3 x) +
      Real.sin t •
        (nativeConcretePhaseOnImage
          ⟨nativeConcreteHestenesEmbedding (doubledWittToExterior3 x), _⟩).1 =
    nativeConcreteHestenesEmbedding
      (doubledWittToExterior3
        (Real.cos t • x + Real.sin t • doubledWittHestenesPhase x))
  change Real.cos t • nativeConcreteHestenesEmbedding
        (doubledWittToExterior3 x) +
      Real.sin t • nativeConcretePhaseAction
        (nativeConcreteHestenesEmbedding (doubledWittToExterior3 x)) = _
  rw [nativeConcretePhaseAction_intertwines]
  rw [← doubledWittToExterior3_intertwines_phase]
  simp only [map_add, map_smul]

end InfoGeometry.Canonical.RealCl55NativeWittHestenesDoublingBridge
