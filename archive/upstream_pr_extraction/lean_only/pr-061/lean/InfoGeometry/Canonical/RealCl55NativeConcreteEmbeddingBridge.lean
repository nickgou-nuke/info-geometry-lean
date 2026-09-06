import Mathlib
import InfoGeometry.Canonical.Cl55ConcreteHestenesCarrierEmbeddingBridge
import InfoGeometry.Canonical.Cl55ConcreteHestenesPhaseEmbeddingBridge
import InfoGeometry.Canonical.DoubledChiralHodgeBlocksBridge
import InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
import InfoGeometry.Canonical.Cl55MasterCoordinateVectorActionBridge

/-!
# Native carrier embedding for the concrete Hestenes packet

This owner packages the existing coordinate `DoubledExterior3 → Spinor32`
embedding as a native Mathlib linear map into the `EuclideanSpace` carrier
used by the finite Cl(5,5) operators.  It proves injectivity only.  Operator
intertwining remains conditional on an explicit basis-compatibility theorem;
no coordinate reindexing is silently identified with the native matrix basis.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge

open InfoGeometry.Canonical.Cl55ConcreteHestenesCarrierEmbeddingBridge
open InfoGeometry.Canonical.Cl55ConcreteHestenesPhaseEmbeddingBridge
open InfoGeometry.Canonical.DoubledChiralHodgeBlocksBridge
open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
open InfoGeometry.Canonical.HodgeFockEmbeddingBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
open InfoGeometry.Canonical.Cl55MasterCoordinateVectorActionBridge
open InfoGeometry.Canonical.Cl55MasterCoordinateReindexBridge
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Clifford.TowerMatrix

abbrev NativeSpinorCarrier :=
  RealCl55FiniteModuleEndBridge.NativeSpinorCarrier

abbrev CoordinateMat32 := Matrix (Fin 32) (Fin 32) ℝ

local instance nativeSpinorT2Space : T2Space NativeSpinorCarrier :=
  TopologicalSpace.t2Space_of_metrizableSpace

noncomputable def coordinateToNative :
    Cl55ConcreteHestenesCarrierEmbeddingBridge.Spinor32 ≃ₗ[ℝ]
      NativeSpinorCarrier :=
  (EuclideanSpace.equiv (Fin 32) ℝ).symm

noncomputable def doubledCoordinateEquiv :
    DoubledExterior3 ≃ₗ[ℝ] DoubledSpinor8 :=
  LinearEquiv.prodCongr exteriorToSpinor8 exteriorToSpinor8

noncomputable def nativeCoordinateAction
    (A : CoordinateMat32) :
    NativeSpinorCarrier →L[ℝ] NativeSpinorCarrier :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)

@[simp] theorem nativeCoordinateAction_apply
    (A : CoordinateMat32) (z : NativeSpinorCarrier) :
    nativeCoordinateAction A z = Matrix.toEuclideanLin A z := by
  change Matrix.toEuclideanLin A z = _
  rfl

theorem nativeCoordinateAction_on_coordinate
    (A : CoordinateMat32)
    (z : Cl55ConcreteHestenesCarrierEmbeddingBridge.Spinor32) :
    nativeCoordinateAction A (coordinateToNative z) =
      coordinateToNative (Matrix.mulVec A z) := by
  change Matrix.toEuclideanLin A (coordinateToNative z) =
    coordinateToNative (Matrix.mulVec A z)
  exact Matrix.toLpLin_apply (p := (2 : ENNReal)) (q := (2 : ENNReal))
    A (coordinateToNative z)

theorem nativeCoordinateAction_mul (A B : CoordinateMat32) :
    nativeCoordinateAction (A * B) =
      (nativeCoordinateAction A).comp (nativeCoordinateAction B) := by
  apply ContinuousLinearMap.ext
  intro z
  rw [← coordinateToNative.apply_symm_apply z]
  simp only [ContinuousLinearMap.comp_apply]
  rw [nativeCoordinateAction_on_coordinate,
    nativeCoordinateAction_on_coordinate,
    nativeCoordinateAction_on_coordinate,
    Matrix.mulVec_mulVec]

theorem nativeCoordinateAction_add (A B : CoordinateMat32) :
    nativeCoordinateAction (A + B) =
      nativeCoordinateAction A + nativeCoordinateAction B := by
  apply ContinuousLinearMap.ext
  intro z
  rw [← coordinateToNative.apply_symm_apply z]
  simp only [ContinuousLinearMap.add_apply]
  rw [nativeCoordinateAction_on_coordinate,
    nativeCoordinateAction_on_coordinate,
    nativeCoordinateAction_on_coordinate,
    Matrix.add_mulVec, map_add]

theorem nativeCoordinateAction_one :
    nativeCoordinateAction (1 : CoordinateMat32) =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  apply ContinuousLinearMap.ext
  intro z
  rw [← coordinateToNative.apply_symm_apply z]
  rw [nativeCoordinateAction_on_coordinate]
  simp [Matrix.one_mulVec]

/-!
The recursive master carrier also has an explicit native realization.  This
is a transport theorem through the chosen `towerIndexEquivFin32`; it does not
assert that this equivalence is definitionally the arithmetic `fin32Equiv`
used by the concrete Fock embedding.
-/

noncomputable def towerToNative :
    TowerSpinor32 ≃ₗ[ℝ]
      NativeSpinorCarrier :=
  towerToCoordinateVector.trans coordinateToNative

noncomputable def nativeMasterHodgeDirac :
    NativeSpinorCarrier →L[ℝ] NativeSpinorCarrier :=
  nativeCoordinateAction masterHodgeDiracFin32

theorem nativeMatrix_eq_towerMatrixReindex
    (A : Cl55MasterWittSpinorEnvelopeBridge.Mat32) :
    nativeMatrix A = towerMatrixReindex A := by
  rfl

theorem nativeMasterHodgeDirac_eq_nativeHodgeDirac :
    nativeMasterHodgeDirac = nativeHodgeDirac := by
  apply ContinuousLinearMap.ext
  intro z
  change Matrix.toEuclideanLin (towerMatrixReindex embeddedSplitOctonionHodgeDirac) z =
    Matrix.toEuclideanLin (nativeMatrix embeddedSplitOctonionHodgeDirac) z
  rw [nativeMatrix_eq_towerMatrixReindex]

theorem nativeMasterHodgeDirac_sq :
    nativeMasterHodgeDirac.comp nativeMasterHodgeDirac =
      (3 : ℝ) • ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  rw [nativeMasterHodgeDirac_eq_nativeHodgeDirac]
  exact nativeHodgeDirac_sq

theorem nativeMasterHodgeDirac_intertwines_tower
    (v : TowerSpinor32) :
    nativeMasterHodgeDirac (towerToNative v) =
      towerToNative (Matrix.mulVec
        embeddedSplitOctonionHodgeDirac v) := by
  change nativeCoordinateAction masterHodgeDiracFin32
      (coordinateToNative (towerToCoordinateVector v)) =
    coordinateToNative (towerToCoordinateVector
      (Matrix.mulVec embeddedSplitOctonionHodgeDirac v))
  rw [nativeCoordinateAction_on_coordinate]
  rw [← masterHodgeDirac_vector_intertwine]

noncomputable def nativeMasterChirality :
    NativeSpinorCarrier →L[ℝ] NativeSpinorCarrier :=
  nativeCoordinateAction masterChiralityFin32

theorem nativeMasterChirality_eq_nativeChirality :
    nativeMasterChirality = nativeChirality := by
  apply ContinuousLinearMap.ext
  intro z
  change Matrix.toEuclideanLin
      (towerMatrixReindex Cl55MasterParityOddnessBridge.MasterChirality) z =
    Matrix.toEuclideanLin
      (nativeMatrix Cl55MasterParityOddnessBridge.MasterChirality) z
  rw [nativeMatrix_eq_towerMatrixReindex]

theorem nativeMasterChirality_sq :
    nativeMasterChirality.comp nativeMasterChirality =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  unfold nativeMasterChirality
  rw [← nativeCoordinateAction_mul, masterChiralityFin32_sq,
    nativeCoordinateAction_one]

theorem nativeMasterChirality_anticommutes_hodge :
    nativeMasterChirality.comp nativeMasterHodgeDirac +
        nativeMasterHodgeDirac.comp nativeMasterChirality = 0 := by
  unfold nativeMasterChirality nativeMasterHodgeDirac
  rw [← nativeCoordinateAction_mul, ← nativeCoordinateAction_mul,
    ← nativeCoordinateAction_add, masterChiralityFin32_anticomm_hodge]
  apply ContinuousLinearMap.ext
  intro z
  simp

theorem nativeMasterHodgeDirac_anticommutes_masterChirality :
    nativeMasterHodgeDirac.comp nativeMasterChirality +
        nativeMasterChirality.comp nativeMasterHodgeDirac = 0 := by
  rw [add_comm, nativeMasterChirality_anticommutes_hodge]

noncomputable def nativeConcreteHestenesEmbedding :
    DoubledExterior3 →ₗ[ℝ] NativeSpinorCarrier where
  toFun :=
      (coordinateToNative.toLinearMap.comp
      (doubledFockEmbedding.comp
        doubledCoordinateEquiv.toLinearMap))
  map_add' := by
    intro x y
    simp
  map_smul' := by
    intro c x
    simp

@[simp] theorem nativeConcreteHestenesEmbedding_apply
    (x : DoubledExterior3) :
    nativeConcreteHestenesEmbedding x =
      coordinateToNative
        (doubledFockEmbedding
          (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)) := by
  simp [nativeConcreteHestenesEmbedding, doubledCoordinateEquiv]

theorem nativeConcreteHestenesEmbedding_injective :
    Function.Injective nativeConcreteHestenesEmbedding := by
  intro x y hxy
  have hcoordinate := congrArg
    (fun z : NativeSpinorCarrier => z.ofLp) hxy
  have hcoordinate' :
      doubledFockEmbedding (doubledCoordinateEquiv x) =
        doubledFockEmbedding (doubledCoordinateEquiv y) := by
    simpa [nativeConcreteHestenesEmbedding, doubledCoordinateEquiv,
      LinearMap.comp_apply] using hcoordinate
  have hspinor := doubledFockEmbedding_injective hcoordinate'
  exact doubledCoordinateEquiv.injective hspinor

theorem nativeConcreteHestenesEmbedding_eq_zero_iff
    (x : DoubledExterior3) :
    nativeConcreteHestenesEmbedding x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hzero :
        doubledFockEmbedding
            (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2) =
          doubledFockEmbedding (0, 0) := by
      calc
        doubledFockEmbedding
              (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2) = 0 := by
          simpa [nativeConcreteHestenesEmbedding,
            doubledCoordinateEquiv] using hx
        _ = doubledFockEmbedding (0, 0) :=
          (map_zero doubledFockEmbedding).symm
    have hpair := doubledFockEmbedding_injective hzero
    have hx1 : exteriorToSpinor8 x.1 = 0 := by
      exact congrArg Prod.fst hpair
    have hx2 : exteriorToSpinor8 x.2 = 0 := by
      exact congrArg Prod.snd hpair
    apply Prod.ext
    · exact exteriorToSpinor8.injective (by simpa using hx1)
    · exact exteriorToSpinor8.injective (by simpa using hx2)
  · intro hx
    rw [hx]
    exact map_zero nativeConcreteHestenesEmbedding

noncomputable def nativeConcreteDiracAction
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3) :
    NativeSpinorCarrier →L[ℝ] NativeSpinorCarrier :=
  nativeCoordinateAction
    (dirac32 (transportedConcreteDiracMatrix v φ))

theorem nativeConcreteDiracAction_intertwines
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3)
    (x : DoubledExterior3) :
    nativeConcreteDiracAction v φ
        (nativeConcreteHestenesEmbedding x) =
      nativeConcreteHestenesEmbedding (concreteDirac3 v φ x) := by
  rw [nativeConcreteHestenesEmbedding_apply,
    nativeConcreteDiracAction, nativeCoordinateAction_on_coordinate]
  exact congrArg coordinateToNative
    (concreteDoubledDirac_to_master_intertwine v φ x)

theorem nativeConcreteDiracAction_eq_nativeHodgeDirac_of_matrix_compatibility
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3)
    (hA : dirac32 (transportedConcreteDiracMatrix v φ) =
      nativeMatrix
        Cl55MasterWittSpinorEnvelopeBridge.embeddedSplitOctonionHodgeDirac) :
    nativeConcreteDiracAction v φ = nativeHodgeDirac := by
  unfold nativeConcreteDiracAction nativeHodgeDirac nativeContinuous
    nativeCoordinateAction
  rw [hA]

theorem nativeConcreteDiracAction_eq_nativeMasterHodgeDirac_of_matrix_compatibility
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3)
    (hA : dirac32 (transportedConcreteDiracMatrix v φ) =
      nativeMatrix embeddedSplitOctonionHodgeDirac) :
    nativeConcreteDiracAction v φ = nativeMasterHodgeDirac := by
  rw [nativeConcreteDiracAction_eq_nativeHodgeDirac_of_matrix_compatibility
    v φ hA, nativeMasterHodgeDirac_eq_nativeHodgeDirac]

theorem nativeHodgeDirac_intertwines_concreteDirac_of_matrix_compatibility
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3)
    (hA : dirac32 (transportedConcreteDiracMatrix v φ) =
      nativeMatrix
        Cl55MasterWittSpinorEnvelopeBridge.embeddedSplitOctonionHodgeDirac)
    (x : DoubledExterior3) :
    nativeHodgeDirac (nativeConcreteHestenesEmbedding x) =
      nativeConcreteHestenesEmbedding (concreteDirac3 v φ x) := by
  rw [← nativeConcreteDiracAction_eq_nativeHodgeDirac_of_matrix_compatibility
    v φ hA]
  exact nativeConcreteDiracAction_intertwines v φ x

noncomputable def nativeConcreteLaplacianAction
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3) :
    NativeSpinorCarrier →L[ℝ] NativeSpinorCarrier :=
  (nativeConcreteDiracAction v φ).comp (nativeConcreteDiracAction v φ)

theorem nativeConcreteLaplacianAction_eq_nativeHodgeLaplacian_of_matrix_compatibility
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3)
    (hA : dirac32 (transportedConcreteDiracMatrix v φ) =
      nativeMatrix
        Cl55MasterWittSpinorEnvelopeBridge.embeddedSplitOctonionHodgeDirac) :
    nativeConcreteLaplacianAction v φ = nativeHodgeLaplacian := by
  unfold nativeConcreteLaplacianAction nativeHodgeLaplacian
  rw [nativeConcreteDiracAction_eq_nativeHodgeDirac_of_matrix_compatibility
    v φ hA]

theorem nativeConcreteLaplacianAction_intertwines
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3)
    (x : DoubledExterior3) :
    nativeConcreteLaplacianAction v φ
        (nativeConcreteHestenesEmbedding x) =
      nativeConcreteHestenesEmbedding (concreteLaplacian3 v φ x) := by
  unfold nativeConcreteLaplacianAction
  rw [ContinuousLinearMap.comp_apply,
    nativeConcreteDiracAction_intertwines,
    nativeConcreteDiracAction_intertwines]
  have h := congrArg
    (fun T : DoubledExterior3End => T x) (concreteDirac3_sq v φ)
  have h' : concreteDirac3 v φ (concreteDirac3 v φ x) =
      concreteLaplacian3 v φ x := by
    simpa using h
  rw [h']

theorem nativeHodgeLaplacian_intertwines_concreteLaplacian_of_matrix_compatibility
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3)
    (hA : dirac32 (transportedConcreteDiracMatrix v φ) =
      nativeMatrix
        Cl55MasterWittSpinorEnvelopeBridge.embeddedSplitOctonionHodgeDirac)
    (x : DoubledExterior3) :
    nativeHodgeLaplacian (nativeConcreteHestenesEmbedding x) =
      nativeConcreteHestenesEmbedding (concreteLaplacian3 v φ x) := by
  rw [← nativeConcreteLaplacianAction_eq_nativeHodgeLaplacian_of_matrix_compatibility
    v φ hA]
  exact nativeConcreteLaplacianAction_intertwines v φ x

noncomputable def coordinateHestenesPhaseMatrix : CoordinateMat32 :=
  LinearMap.toMatrix' embeddedHestenesPhase32

theorem coordinateHestenesPhaseMatrix_mulVec
    (z : Cl55ConcreteHestenesCarrierEmbeddingBridge.Spinor32) :
    Matrix.mulVec coordinateHestenesPhaseMatrix z =
      embeddedHestenesPhase32 z := by
  change Matrix.mulVec (LinearMap.toMatrix' embeddedHestenesPhase32) z =
    embeddedHestenesPhase32 z
  exact LinearMap.toMatrix'_mulVec embeddedHestenesPhase32 z

noncomputable def nativeConcretePhaseAction :
    NativeSpinorCarrier →L[ℝ] NativeSpinorCarrier :=
  nativeCoordinateAction coordinateHestenesPhaseMatrix

theorem nativeConcretePhaseAction_intertwines
    (x : DoubledExterior3) :
    nativeConcretePhaseAction (nativeConcreteHestenesEmbedding x) =
      nativeConcreteHestenesEmbedding (hestenesPhase3 x) := by
  rw [nativeConcreteHestenesEmbedding_apply,
    nativeConcretePhaseAction, nativeCoordinateAction_on_coordinate,
    coordinateHestenesPhaseMatrix_mulVec]
  simpa [nativeConcreteHestenesEmbedding, doubledCoordinateEquiv,
    hestenesPhase3, hestenesPhase8]
    using embeddedHestenesPhase32_on_doubledEmbedding
      (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)

theorem nativeConcretePhaseAction_intertwines_dirac
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3)
    (x : DoubledExterior3) :
    nativeConcretePhaseAction
        (nativeConcreteDiracAction v φ
          (nativeConcreteHestenesEmbedding x)) =
      nativeConcreteDiracAction v φ
        (nativeConcretePhaseAction (nativeConcreteHestenesEmbedding x)) := by
  rw [nativeConcreteDiracAction_intertwines,
    nativeConcretePhaseAction_intertwines,
    nativeConcretePhaseAction_intertwines,
    nativeConcreteDiracAction_intertwines]
  have h := congrArg
    (fun T : DoubledExterior3End => T x) (concreteDirac3_phase v φ)
  simpa only [Module.End.mul_apply] using
    congrArg nativeConcreteHestenesEmbedding h

theorem nativeConcretePhaseAction_intertwines_laplacian
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3)
    (x : DoubledExterior3) :
    nativeConcretePhaseAction
        (nativeConcreteLaplacianAction v φ
          (nativeConcreteHestenesEmbedding x)) =
      nativeConcreteLaplacianAction v φ
        (nativeConcretePhaseAction (nativeConcreteHestenesEmbedding x)) := by
  unfold nativeConcreteLaplacianAction
  rw [ContinuousLinearMap.comp_apply,
    nativeConcreteDiracAction_intertwines,
    nativeConcretePhaseAction_intertwines_dirac,
    nativeConcretePhaseAction_intertwines]
  have h := congrArg
    (fun T : DoubledExterior3End => T x) (concreteDirac3_phase v φ)
  have h' : hestenesPhase3 (concreteDirac3 v φ x) =
      concreteDirac3 v φ (hestenesPhase3 x) := by
    simpa only [Module.End.mul_apply] using h
  rw [h']
  rw [ContinuousLinearMap.comp_apply,
    nativeConcretePhaseAction_intertwines,
    nativeConcreteDiracAction_intertwines (v := v) (φ := φ)
      (x := hestenesPhase3 x)]

theorem nativeConcretePhaseAction_sq_on_embedding
    (x : DoubledExterior3) :
    nativeConcretePhaseAction
        (nativeConcretePhaseAction (nativeConcreteHestenesEmbedding x)) =
      -nativeConcreteHestenesEmbedding x := by
  rw [nativeConcretePhaseAction_intertwines,
    nativeConcretePhaseAction_intertwines]
  have h := congrArg (fun T : DoubledExterior3End => T x) hestenesPhase3_sq
  have h' : hestenesPhase3 (hestenesPhase3 x) = -x := by
    simpa using h
  rw [h']
  exact map_neg nativeConcreteHestenesEmbedding x

noncomputable def nativeConcreteHestenesImage :
    Submodule ℝ NativeSpinorCarrier :=
  LinearMap.range nativeConcreteHestenesEmbedding

noncomputable def nativeConcreteHestenesEmbeddingToImage :
    DoubledExterior3 →ₗ[ℝ] nativeConcreteHestenesImage :=
  nativeConcreteHestenesEmbedding.codRestrict
    nativeConcreteHestenesImage (fun x => ⟨x, rfl⟩)

theorem nativeConcreteHestenesEmbeddingToImage_bijective :
    Function.Bijective nativeConcreteHestenesEmbeddingToImage := by
  constructor
  · intro x y hxy
    apply nativeConcreteHestenesEmbedding_injective
    exact congrArg Subtype.val hxy
  · intro y
    rcases y.2 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

noncomputable def nativeConcreteHestenesEmbeddingEquiv :
    DoubledExterior3 ≃ₗ[ℝ] nativeConcreteHestenesImage :=
  LinearEquiv.ofBijective nativeConcreteHestenesEmbeddingToImage
    nativeConcreteHestenesEmbeddingToImage_bijective

@[simp] theorem nativeConcreteHestenesEmbeddingEquiv_apply
    (x : DoubledExterior3) :
    nativeConcreteHestenesEmbeddingEquiv x =
      ⟨nativeConcreteHestenesEmbedding x, ⟨x, rfl⟩⟩ := rfl

noncomputable def nativeConcreteDiracOnImage
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3) :
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

theorem nativeConcreteDiracOnImage_intertwines_embeddingEquiv
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3)
    (x : DoubledExterior3) :
    nativeConcreteDiracOnImage v φ
        (nativeConcreteHestenesEmbeddingEquiv x) =
      nativeConcreteHestenesEmbeddingEquiv (concreteDirac3 v φ x) := by
  apply Subtype.ext
  change nativeConcreteDiracAction v φ
      (nativeConcreteHestenesEmbedding x) =
    nativeConcreteHestenesEmbedding (concreteDirac3 v φ x)
  exact nativeConcreteDiracAction_intertwines v φ x

theorem nativeConcreteDiracOnImage_eq_conjugate
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3) :
    nativeConcreteDiracOnImage v φ =
      nativeConcreteHestenesEmbeddingEquiv.toLinearMap.comp
        ((concreteDirac3 v φ).comp
          nativeConcreteHestenesEmbeddingEquiv.symm.toLinearMap) := by
  apply LinearMap.ext
  intro z
  simpa [LinearMap.comp_apply] using
    nativeConcreteDiracOnImage_intertwines_embeddingEquiv v φ
      (nativeConcreteHestenesEmbeddingEquiv.symm z)

noncomputable def nativeConcreteLaplacianOnImage
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3) :
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

theorem nativeConcreteLaplacianOnImage_intertwines_embeddingEquiv
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3)
    (x : DoubledExterior3) :
    nativeConcreteLaplacianOnImage v φ
        (nativeConcreteHestenesEmbeddingEquiv x) =
      nativeConcreteHestenesEmbeddingEquiv (concreteLaplacian3 v φ x) := by
  apply Subtype.ext
  change nativeConcreteLaplacianAction v φ
      (nativeConcreteHestenesEmbedding x) =
    nativeConcreteHestenesEmbedding (concreteLaplacian3 v φ x)
  exact nativeConcreteLaplacianAction_intertwines v φ x

theorem nativeConcreteLaplacianOnImage_eq_conjugate
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3) :
    nativeConcreteLaplacianOnImage v φ =
      nativeConcreteHestenesEmbeddingEquiv.toLinearMap.comp
        ((concreteLaplacian3 v φ).comp
          nativeConcreteHestenesEmbeddingEquiv.symm.toLinearMap) := by
  apply LinearMap.ext
  intro z
  simpa [LinearMap.comp_apply] using
    nativeConcreteLaplacianOnImage_intertwines_embeddingEquiv v φ
      (nativeConcreteHestenesEmbeddingEquiv.symm z)

noncomputable def nativeConcretePhaseOnImage :
    nativeConcreteHestenesImage →ₗ[ℝ] nativeConcreteHestenesImage where
  toFun z :=
    ⟨nativeConcretePhaseAction z.1, by
      rcases z.2 with ⟨x, hx⟩
      refine ⟨hestenesPhase3 x, ?_⟩
      rw [← hx]
      exact (nativeConcretePhaseAction_intertwines x).symm⟩
  map_add' x y := by
    apply Subtype.ext
    simp [map_add]
  map_smul' c x := by
    apply Subtype.ext
    simp [map_smul]

theorem nativeConcretePhaseOnImage_intertwines_embeddingEquiv
    (x : DoubledExterior3) :
    nativeConcretePhaseOnImage
        (nativeConcreteHestenesEmbeddingEquiv x) =
      nativeConcreteHestenesEmbeddingEquiv (hestenesPhase3 x) := by
  apply Subtype.ext
  change nativeConcretePhaseAction (nativeConcreteHestenesEmbedding x) =
    nativeConcreteHestenesEmbedding (hestenesPhase3 x)
  exact nativeConcretePhaseAction_intertwines x

theorem nativeConcretePhaseOnImage_sq :
    nativeConcretePhaseOnImage.comp nativeConcretePhaseOnImage =
      -(1 : nativeConcreteHestenesImage →ₗ[ℝ] nativeConcreteHestenesImage) := by
  apply LinearMap.ext
  rintro ⟨z, hz⟩
  rcases hz with ⟨x, hx⟩
  apply Subtype.ext
  change nativeConcretePhaseAction
      (nativeConcretePhaseAction z) = -z
  rw [← hx, nativeConcretePhaseAction_intertwines,
    nativeConcretePhaseAction_intertwines]
  exact map_neg nativeConcreteHestenesEmbedding x

theorem nativeConcretePhaseOnImage_sq_apply
    (x : nativeConcreteHestenesImage) :
    nativeConcretePhaseOnImage (nativeConcretePhaseOnImage x) = -x := by
  have h := congrArg
    (fun T : nativeConcreteHestenesImage →ₗ[ℝ] nativeConcreteHestenesImage => T x)
    nativeConcretePhaseOnImage_sq
  simpa [LinearMap.comp_apply] using h

theorem nativeConcretePhaseOnImage_bijective :
    Function.Bijective nativeConcretePhaseOnImage := by
  constructor
  · intro x y hxy
    calc
      x = -nativeConcretePhaseOnImage
          (nativeConcretePhaseOnImage x) := by
            rw [nativeConcretePhaseOnImage_sq_apply]
            simp
      _ = -nativeConcretePhaseOnImage
          (nativeConcretePhaseOnImage y) := by rw [hxy]
      _ = y := by
        rw [nativeConcretePhaseOnImage_sq_apply]
        simp
  · intro y
    refine ⟨-nativeConcretePhaseOnImage y, ?_⟩
    calc
      nativeConcretePhaseOnImage (-nativeConcretePhaseOnImage y) =
          -nativeConcretePhaseOnImage (nativeConcretePhaseOnImage y) := by
            rw [map_neg]
      _ = y := by
        rw [nativeConcretePhaseOnImage_sq_apply]
        simp

noncomputable def nativeConcretePhaseOnImageEquiv :
  nativeConcreteHestenesImage ≃ₗ[ℝ] nativeConcreteHestenesImage :=
  LinearEquiv.ofBijective nativeConcretePhaseOnImage
    nativeConcretePhaseOnImage_bijective

/-! The concrete chirality and its Hestenes composite can also be transported
to the native image.  This is deliberately an image-level construction: it
does not identify the doubled concrete packet with the whole 32-dimensional
master carrier. -/

noncomputable def nativeConcreteChiralityOnImage :
    nativeConcreteHestenesImage →ₗ[ℝ] nativeConcreteHestenesImage :=
  nativeConcreteHestenesEmbeddingEquiv.toLinearMap.comp
    (concreteChirality3.comp
      nativeConcreteHestenesEmbeddingEquiv.symm.toLinearMap)

theorem nativeConcreteChiralityOnImage_intertwines_embeddingEquiv
    (x : DoubledExterior3) :
    nativeConcreteChiralityOnImage
        (nativeConcreteHestenesEmbeddingEquiv x) =
      nativeConcreteHestenesEmbeddingEquiv (concreteChirality3 x) := by
  change nativeConcreteHestenesEmbeddingEquiv
      (concreteChirality3
        (nativeConcreteHestenesEmbeddingEquiv.symm
          (nativeConcreteHestenesEmbeddingEquiv x))) = _
  rw [nativeConcreteHestenesEmbeddingEquiv.symm_apply_apply]

theorem nativeConcreteChiralityOnImage_sq :
    nativeConcreteChiralityOnImage.comp nativeConcreteChiralityOnImage =
      (1 : nativeConcreteHestenesImage →ₗ[ℝ] nativeConcreteHestenesImage) := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply]
  rw [← nativeConcreteHestenesEmbeddingEquiv.apply_symm_apply z]
  rw [nativeConcreteChiralityOnImage_intertwines_embeddingEquiv,
    nativeConcreteChiralityOnImage_intertwines_embeddingEquiv]
  simpa using congrArg nativeConcreteHestenesEmbeddingEquiv
    (congrArg (fun T : DoubledExterior3End => T
      (nativeConcreteHestenesEmbeddingEquiv.symm z)) concreteChirality3_sq)

noncomputable def nativeConcreteChiralComplexOnImage :
    nativeConcreteHestenesImage →ₗ[ℝ] nativeConcreteHestenesImage :=
  nativeConcretePhaseOnImage.comp nativeConcreteChiralityOnImage

theorem nativeConcreteChiralComplexOnImage_intertwines_embeddingEquiv
    (x : DoubledExterior3) :
    nativeConcreteChiralComplexOnImage
        (nativeConcreteHestenesEmbeddingEquiv x) =
      nativeConcreteHestenesEmbeddingEquiv
        (hestenesChiralComplex3 x) := by
  rw [nativeConcreteChiralComplexOnImage,
    LinearMap.comp_apply,
    nativeConcreteChiralityOnImage_intertwines_embeddingEquiv,
    nativeConcretePhaseOnImage_intertwines_embeddingEquiv]
  rfl

theorem nativeConcreteChiralComplexOnImage_sq :
    nativeConcreteChiralComplexOnImage.comp
        nativeConcreteChiralComplexOnImage =
      -(1 : nativeConcreteHestenesImage →ₗ[ℝ] nativeConcreteHestenesImage) := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply]
  rw [← nativeConcreteHestenesEmbeddingEquiv.apply_symm_apply z]
  rw [nativeConcreteChiralComplexOnImage_intertwines_embeddingEquiv,
    nativeConcreteChiralComplexOnImage_intertwines_embeddingEquiv]
  apply Subtype.ext
  change nativeConcreteHestenesEmbedding
      (hestenesChiralComplex3
        (hestenesChiralComplex3
          (nativeConcreteHestenesEmbeddingEquiv.symm z))) =
    -nativeConcreteHestenesEmbedding
      (nativeConcreteHestenesEmbeddingEquiv.symm z)
  have hpoint :
      hestenesChiralComplex3
          (hestenesChiralComplex3
            (nativeConcreteHestenesEmbeddingEquiv.symm z)) =
        -nativeConcreteHestenesEmbeddingEquiv.symm z := by
    have h := congrArg (fun T : DoubledExterior3End => T
      (nativeConcreteHestenesEmbeddingEquiv.symm z))
      hestenesChiralComplex3_sq
    simpa only [Module.End.mul_apply] using h
  simpa only [nativeConcreteHestenesEmbedding, map_neg] using
    congrArg nativeConcreteHestenesEmbedding hpoint

theorem nativeConcreteChiralComplexOnImage_anticommutes_dirac
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3) :
    nativeConcreteChiralComplexOnImage.comp
        (nativeConcreteDiracOnImage v φ) =
      -(nativeConcreteDiracOnImage v φ).comp
        nativeConcreteChiralComplexOnImage := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply]
  rw [← nativeConcreteHestenesEmbeddingEquiv.apply_symm_apply z]
  change nativeConcreteChiralComplexOnImage
      (nativeConcreteDiracOnImage v φ
        (nativeConcreteHestenesEmbeddingEquiv
          (nativeConcreteHestenesEmbeddingEquiv.symm z))) =
    -nativeConcreteDiracOnImage v φ
      (nativeConcreteChiralComplexOnImage
        (nativeConcreteHestenesEmbeddingEquiv
          (nativeConcreteHestenesEmbeddingEquiv.symm z)))
  rw [nativeConcreteDiracOnImage_intertwines_embeddingEquiv v φ,
    nativeConcreteChiralComplexOnImage_intertwines_embeddingEquiv
      (concreteDirac3 v φ (nativeConcreteHestenesEmbeddingEquiv.symm z)),
    nativeConcreteChiralComplexOnImage_intertwines_embeddingEquiv]
  rw [nativeConcreteDiracOnImage_intertwines_embeddingEquiv v φ
    (hestenesChiralComplex3 (nativeConcreteHestenesEmbeddingEquiv.symm z))]
  apply Subtype.ext
  change nativeConcreteHestenesEmbedding
      (hestenesChiralComplex3
        (concreteDirac3 v φ (nativeConcreteHestenesEmbeddingEquiv.symm z))) =
    -nativeConcreteHestenesEmbedding
      (concreteDirac3 v φ
        (hestenesChiralComplex3
          (nativeConcreteHestenesEmbeddingEquiv.symm z)))
  have hpoint := congrArg (fun T : DoubledExterior3End => T
      (nativeConcreteHestenesEmbeddingEquiv.symm z))
    (hestenesChiralComplex3_anticommutes_dirac v φ)
  simpa [nativeConcreteHestenesEmbedding, Module.End.mul_apply, map_neg] using
    congrArg nativeConcreteHestenesEmbedding hpoint

theorem nativeConcreteChiralComplexOnImage_commutes_chirality :
    nativeConcreteChiralComplexOnImage.comp
        nativeConcreteChiralityOnImage =
      nativeConcreteChiralityOnImage.comp
        nativeConcreteChiralComplexOnImage := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply]
  rw [← nativeConcreteHestenesEmbeddingEquiv.apply_symm_apply z]
  rw [nativeConcreteChiralityOnImage_intertwines_embeddingEquiv,
    nativeConcreteChiralComplexOnImage_intertwines_embeddingEquiv,
    nativeConcreteChiralComplexOnImage_intertwines_embeddingEquiv,
    nativeConcreteChiralityOnImage_intertwines_embeddingEquiv]
  apply Subtype.ext
  change nativeConcreteHestenesEmbedding
      (hestenesChiralComplex3
        (concreteChirality3 (nativeConcreteHestenesEmbeddingEquiv.symm z))) =
    nativeConcreteHestenesEmbedding
      (concreteChirality3
        (hestenesChiralComplex3 (nativeConcreteHestenesEmbeddingEquiv.symm z)))
  exact congrArg nativeConcreteHestenesEmbedding
    (congrArg (fun T : DoubledExterior3End => T
      (nativeConcreteHestenesEmbeddingEquiv.symm z))
      hestenesChiralComplex3_commutes_chirality)

end InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge
