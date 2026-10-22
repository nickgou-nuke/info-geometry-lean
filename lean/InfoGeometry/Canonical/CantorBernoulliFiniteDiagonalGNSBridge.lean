/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalTraceEnergy
import InfoGeometry.Canonical.CantorBernoulliCylinderColimitL2
import InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge
import InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge

/-!
# Finite Bernoulli diagonal map on the native trace GNS stages

The finite BitWord trace-energy contraction transports to the native finite
C⋆ trace-state PreGNS norm and extends to each completed finite-stage GNS
space. The completed stage maps are compatible across the filtered system;
they descend to the algebraic GNS colimit and extend continuously to its
completion, with the finite-stage readout preserved. Their image is dense in
the Bernoulli boundary `L²` space, but this readout is not an identification of
the full noncommutative GNS colimit with `L²`.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace NNReal

namespace InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalGNSBridge

open InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalTraceEnergy
open InfoGeometry.Canonical.CantorKMSState
open InfoGeometry.Canonical.CantorBernoulliDiagTraceBridge
open InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalHilbertSchmidt
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagL2Embedding
open InfoGeometry.Canonical.CantorBernoulliCylinderColimitL2
open InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge
open InfoGeometry.Canonical.GenuineMatrixStageMorphism
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationRefinementBridge
open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit
open InfoGeometry.Canonical.FilteredIsometricInnerProductDirectLimit
open InfoGeometry.Canonical.FilteredIsometricHilbertCompletion
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSTomitaModularForm

local instance cstarMatrixStageRealCFC (n : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrixStage n) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance cstarMatrixStageNonnegSpectrum (n : ℕ) :
    NonnegSpectrumClass ℝ (CStarMatrixStage n) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- The native finite C⋆ matrix stage reindexed as a BitWord matrix stage. -/
def cstarStageToBitWordStage (n : ℕ) :
    CStarMatrixStage n ≃⋆ₐ[ℂ] BitWordMatrixStage n :=
  (CStarMatrix.ofMatrixStarAlgEquiv).symm.trans
    (stageStarAlgEquiv n).symm

/-- The normalized trace on BitWord matrices is the canonical normalized
trace after the natural stage reindexing. -/
theorem bitWordMatrixTraceFunctional_eq_canonicalStageTrace
    (n : ℕ) (A : BitWordMatrixStage n) :
    bitWordMatrixTraceFunctional n A =
      matrixTraceState n (stageStarAlgEquiv n A) := by
  rw [← stageStarAlgEquiv_normalizedTrace]
  simp [normalizedTrace, bitWordMatrixTraceFunctional_apply,
    Fintype.card_bool, Fintype.card_fin]

/-- The native finite gauge state reads the BitWord matrix through the
canonical, successor-compatible reindexing. -/
theorem gaugeStateFamily_canonical_bitWord_matrix_readout
    (n : ℕ) (A : BitWordMatrixStage n) :
    (gaugeStateFamily.state n).functional
        (CStarMatrix.ofMatrixStarAlgEquiv (stageStarAlgEquiv n A)) =
      bitWordMatrixTraceFunctional n A := by
  rw [gaugeStateFamily_readout]
  change matrixTraceState n (stageStarAlgEquiv n A) = _
  exact (bitWordMatrixTraceFunctional_eq_canonicalStageTrace n A).symm

/-- The native finite gauge state on a diagonal matrix is integration of its
prefix observable against the projective-limit Bernoulli measure. -/
theorem gaugeStateFamily_diagonal_projective_integral
    (n : ℕ) (f : DiagAlg n) :
    (gaugeStateFamily.state n).functional
        ((cstarStageToBitWordStage n).symm (Matrix.diagonal f)) =
      ∫ q, f (π n q) ∂projectiveLimitMeasure := by
  calc
    (gaugeStateFamily.state n).functional
        ((cstarStageToBitWordStage n).symm (Matrix.diagonal f)) =
      bitWordMatrixTraceFunctional n (Matrix.diagonal f) := by
        change (gaugeStateFamily.state n).functional
            (CStarMatrix.ofMatrixStarAlgEquiv
              (stageStarAlgEquiv n (Matrix.diagonal f))) = _
        exact gaugeStateFamily_canonical_bitWord_matrix_readout n
          (Matrix.diagonal f)
    _ = InfoGeometry.Canonical.UHFInductiveLimitBoundary.stageTrace n f := by
      rw [stageTrace_eq_DiagTrace]
      exact bitWordMatrixTraceFunctional_diagonal n f
    _ = ∫ q, f (π n q) ∂projectiveLimitMeasure :=
      (projectiveLimitMeasure_integral_prefix_eq_stageTrace n f).symm

/-- The common vacuum in the native filtered GNS Hilbert colimit evaluates
every finite UHF diagonal observable as its projective-limit Bernoulli
integral. This is a diagonal-sector readout; it does not identify the full
noncommutative GNS colimit with the boundary `L²` space. -/
theorem gaugeGNSColimitVacuum_diagonal_projective_integral
    (n : ℕ) (f : DiagAlg n) :
    ⟪gaugeGNSColimitVacuum,
      CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation.globalStageRepresentationStarAlgHom
        gaugeStage gaugeSystem gaugeStateFamily n
        ((cstarStageToBitWordStage n).symm (Matrix.diagonal f))
        gaugeGNSColimitVacuum⟫_ℂ =
      ∫ q, f (π n q) ∂projectiveLimitMeasure := by
  rw [gaugeGNSColimitVacuum_stage_expectation]
  exact gaugeStateFamily_diagonal_projective_integral n f

/-- The spatial Bernoulli vector state after the finite Cuntz-boundary
representation agrees with the projective-limit integral on every finite
diagonal observable. -/
theorem spatialState_boundaryRep_diagonal_projective_integral
    (n : ℕ) (f : DiagAlg n) :
    spatialState.functional (boundaryRep n (Matrix.diagonal f)) =
      ∫ q, f (π n q) ∂projectiveLimitMeasure := by
  calc
    spatialState.functional (boundaryRep n (Matrix.diagonal f)) =
        bitWordMatrixTraceFunctional n (Matrix.diagonal f) :=
      spatialState_boundaryRep_diagonal_eq_matrixTrace n f
    _ = InfoGeometry.Canonical.UHFInductiveLimitBoundary.stageTrace n f := by
      rw [stageTrace_eq_DiagTrace]
      exact bitWordMatrixTraceFunctional_diagonal n f
    _ = ∫ q, f (π n q) ∂projectiveLimitMeasure :=
      (projectiveLimitMeasure_integral_prefix_eq_stageTrace n f).symm

/-- The native C⋆ successor is carried to the canonical BitWord successor. -/
theorem cstarStageToBitWordStage_succ
    (n : ℕ) (A : CStarMatrixStage n) :
    cstarStageToBitWordStage (n + 1)
        (gaugeSystem.map (Nat.le.step (le_refl n)) A) =
      ComplexMatrixStage.bondFun n (cstarStageToBitWordStage n A) := by
  apply (stageStarAlgEquiv (n + 1)).injective
  change stageStarAlgEquiv (n + 1)
      (cstarStageToBitWordStage (n + 1)
        (gaugeSystem.map (Nat.le.step (le_refl n)) A)) =
    stageStarAlgEquiv (n + 1)
      (ComplexMatrixStage.bondFun n (cstarStageToBitWordStage n A))
  rw [stageStarAlgEquiv_bond]
  simp only [cstarStageToBitWordStage, StarAlgEquiv.trans_apply,
    StarAlgEquiv.apply_symm_apply]
  change (CStarMatrix.ofMatrixStarAlgEquiv).symm
      (gaugeSystem.map (Nat.le.step (le_refl n)) A) =
    CuntzMatrixTraceTower.concreteStep n
      ((CStarMatrix.ofMatrixStarAlgEquiv).symm A)
  rw [show gaugeSystem.map (Nat.le.step (le_refl n)) =
      cstarConcreteMap (Nat.le.step (le_refl n)) by rfl]
  rw [cstarConcreteMap_toMatrixStage]
  simp [CuntzMatrixTraceTower.concreteMap,
    CuntzMatrixTraceTower.map_succ, CuntzMatrixTraceTower.map_id,
    CuntzMatrixTraceTower.concreteData]

/-- The native C⋆ successor, transported to the BitWord matrix carrier, is
exactly the explicit dyadic matrix embedding used by the boundary
representation. -/
theorem cstarStageToBitWordStage_succ_dyadic
    (n : ℕ) (A : CStarMatrixStage n) :
    cstarStageToBitWordStage (n + 1)
        (gaugeSystem.map (Nat.le.step (le_refl n)) A) =
      dyadicMatrixEmbedding n (cstarStageToBitWordStage n A) := by
  rw [cstarStageToBitWordStage_succ]
  exact GenuineMatrixStageMorphism.bondFun_eq_dyadicMatrixEmbedding n
    (cstarStageToBitWordStage n A)

/-- The finite boundary representation is compatible with the native C⋆
transition after transporting its source to the BitWord carrier. -/
theorem boundaryRep_cstarTransition_succ
    (n : ℕ) (A : CStarMatrixStage n) :
    boundaryRep n (cstarStageToBitWordStage n A) =
      boundaryRep (n + 1)
        (cstarStageToBitWordStage (n + 1)
          (gaugeSystem.map (Nat.le.step (le_refl n)) A)) := by
  rw [cstarStageToBitWordStage_succ_dyadic]
  exact boundaryRep_bond_compatible n (cstarStageToBitWordStage n A)

/-- The matrix diagonal as a complex-linear map into the existing diagonal
stage. -/
def bitWordDiagonalLinearMap (n : ℕ) :
    BitWordMatrixStage n →ₗ[ℂ] DiagAlg n where
  toFun := diagonalPart n
  map_add' A B := by
    ext u
    simp [diagonalPart, Matrix.diag]
  map_smul' c A := by
    ext u
    simp [diagonalPart, Matrix.diag]

/-- The finite C⋆-stage diagonal followed by the existing Bernoulli cylinder
map. -/
def cstarDiagonalCylinderLinearMap (n : ℕ) :
    CStarMatrixStage n →ₗ[ℂ] L2Boundary :=
  (diagonalCylinderL2 n).comp
    ((bitWordDiagonalLinearMap n).comp
      ((cstarStageToBitWordStage n).toAlgEquiv.toLinearMap))

/-- The finite native C⋆-stage diagonal readout agrees across the successor
transition, by the existing matrix-diagonal and Bernoulli-cylinder squares. -/
theorem cstarDiagonalCylinderLinearMap_succ
    (n : ℕ) (A : CStarMatrixStage n) :
    cstarDiagonalCylinderLinearMap (n + 1)
        (gaugeSystem.map (Nat.le.step (le_refl n)) A) =
      cstarDiagonalCylinderLinearMap n A := by
  simp only [cstarDiagonalCylinderLinearMap, LinearMap.comp_apply]
  change diagonalCylinderL2 (n + 1)
      (diagonalPart (n + 1)
        (cstarStageToBitWordStage (n + 1)
          (gaugeSystem.map (Nat.le.step (le_refl n)) A))) =
    diagonalCylinderL2 n (diagonalPart n (cstarStageToBitWordStage n A))
  rw [cstarStageToBitWordStage_succ]
  rw [diagonalPart_bond_compatible]
  exact diagonalCylinderL2_compatible_succ n (diagonalPart n
    (cstarStageToBitWordStage n A))

/-- The algebraic diagonal map on the pre-GNS carrier of the finite gauge
trace state. -/
def gaugeDiagonalPreGNSLinearMap (n : ℕ) :
    (gaugeStateFamily.state n).functional.PreGNS →ₗ[ℂ] L2Boundary :=
  (cstarDiagonalCylinderLinearMap n).comp
    ((gaugeStateFamily.state n).functional.ofPreGNS.toLinearMap)

/-- Transport of the normalized BitWord trace energy to the native finite
C⋆ trace-state evaluation. -/
theorem gaugeTraceEnergy_eq_stateEvaluation
    (n : ℕ) (A : CStarMatrixStage n) :
    bitWordMatrixTraceFunctional n
        (star (cstarStageToBitWordStage n A) *
          cstarStageToBitWordStage n A) =
      (gaugeStateFamily.state n).functional (star A * A) := by
  let B := cstarStageToBitWordStage n A
  have htransport :
      CStarMatrix.ofMatrixStarAlgEquiv (stageStarAlgEquiv n B) = A := by
    change (cstarStageToBitWordStage n).symm
      (cstarStageToBitWordStage n A) = A
    exact (cstarStageToBitWordStage n).symm_apply_apply A
  calc
    bitWordMatrixTraceFunctional n
        (star B * B) = bitWordMatrixGaugeReadout n (star B * B) :=
      (bitWordMatrixGaugeReadout_eq_trace n _).symm
    _ = (gaugeStateFamily.state n).functional
          (CStarMatrix.ofMatrixStarAlgEquiv
            (stageStarAlgEquiv n (star B * B))) := by
      rw [gaugeStateFamily_canonical_bitWord_matrix_readout]
      exact bitWordMatrixGaugeReadout_eq_trace n _
    _ = (gaugeStateFamily.state n).functional (star A * A) := by
      congr 1
      calc
        CStarMatrix.ofMatrixStarAlgEquiv
            (stageStarAlgEquiv n (star B * B)) =
          star (CStarMatrix.ofMatrixStarAlgEquiv
              (stageStarAlgEquiv n B)) *
            CStarMatrix.ofMatrixStarAlgEquiv
              (stageStarAlgEquiv n B) := by
                simp only [map_mul, map_star]
        _ = star A * A := by rw [htransport]

/-- The finite diagonal map is contractive for the native trace-state PreGNS
norm. -/
theorem gaugeDiagonalPreGNS_norm_le
    (n : ℕ) (x : (gaugeStateFamily.state n).functional.PreGNS) :
    ‖gaugeDiagonalPreGNSLinearMap n x‖ ≤ ‖x‖ := by
  let A := (gaugeStateFamily.state n).functional.ofPreGNS x
  have henergy := diagonalCylinderL2_norm_sq_le_traceEnergy n
    (cstarStageToBitWordStage n A)
  have hstate := gaugeTraceEnergy_eq_stateEvaluation n A
  have hpreGNS :
      ‖x‖ ^ 2 =
        (gaugeStateFamily.state n).functional (star A * A) := by
    simpa [A] using
      (PositiveLinearMap.preGNS_norm_sq
        (gaugeStateFamily.state n).functional x)
  have hpreGNS_re :
      ((gaugeStateFamily.state n).functional (star A * A)).re =
        ‖x‖ ^ 2 := by
    calc
      ((gaugeStateFamily.state n).functional (star A * A)).re =
          (((‖x‖ : ℝ) : ℂ) ^ 2).re :=
        congrArg Complex.re hpreGNS.symm
      _ = ‖x‖ ^ 2 := by
        calc
          (((‖x‖ : ℝ) : ℂ) ^ 2).re =
              (((‖x‖ ^ 2 : ℝ) : ℂ)).re :=
            congrArg Complex.re (Complex.ofReal_pow ‖x‖ 2).symm
          _ = ‖x‖ ^ 2 := Complex.ofReal_re _
  have hsq : ‖gaugeDiagonalPreGNSLinearMap n x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    calc
      ‖gaugeDiagonalPreGNSLinearMap n x‖ ^ 2 =
          ‖diagonalCylinderL2 n
            (diagonalPart n (cstarStageToBitWordStage n A))‖ ^ 2 := by
              rfl
      _ ≤ (bitWordMatrixTraceFunctional n
            (star (cstarStageToBitWordStage n A) *
              cstarStageToBitWordStage n A)).re := henergy
      _ = ‖x‖ ^ 2 := by rw [hstate]; exact hpreGNS_re
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Continuous form of the finite-stage pre-GNS diagonal map. -/
def gaugeDiagonalPreGNSCLM (n : ℕ) :
    (gaugeStateFamily.state n).functional.PreGNS →L[ℂ] L2Boundary :=
  let f : (gaugeStateFamily.state n).functional.PreGNS →ₛₗ[RingHom.id ℂ] L2Boundary :=
    { toFun := gaugeDiagonalPreGNSLinearMap n
      map_add' := by
        intro x y
        exact (gaugeDiagonalPreGNSLinearMap n).map_add x y
      map_smul' := by
        intro c x
        exact (gaugeDiagonalPreGNSLinearMap n).map_smul c x }
  have hbound : ∀ x, ‖f x‖ ≤ (1 : ℝ) * ‖x‖ := by
    intro x
    simpa [f, gaugeDiagonalPreGNSLinearMap, cstarDiagonalCylinderLinearMap,
      bitWordDiagonalLinearMap] using gaugeDiagonalPreGNS_norm_le n x
  { toFun := f
    map_add' := f.map_add
    map_smul' := f.map_smul
    cont := AddMonoidHomClass.continuous_of_bound f 1 hbound }

/-- Extension of the finite-stage diagonal contraction to the completed
native GNS Hilbert space. -/
def gaugeDiagonalGNSMap (n : ℕ) :
    (gaugeStateFamily.state n).functional.GNS →L[ℂ] L2Boundary :=
  (gaugeDiagonalPreGNSCLM n).fromCompletion

/-- The completed finite-stage GNS diagonal remains contractive. -/
theorem gaugeDiagonalGNSMap_norm_le
    (n : ℕ) (x : gaugeGNSStage n) :
    ‖gaugeDiagonalGNSMap n x‖ ≤ ‖x‖ := by
  have hLip : LipschitzWith 1
      (gaugeDiagonalPreGNSCLM n :
        (gaugeStateFamily.state n).functional.PreGNS → L2Boundary) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    calc
      ‖gaugeDiagonalPreGNSCLM n x -
          gaugeDiagonalPreGNSCLM n y‖ =
        ‖gaugeDiagonalPreGNSCLM n (x - y)‖ := by
          rw [map_sub]
      _ ≤ ‖x - y‖ := gaugeDiagonalPreGNS_norm_le n (x - y)
      _ = (1 : ℝ) * ‖x - y‖ := by simp
  have hExt := hLip.completion_extension
  have hzero :
      UniformSpace.Completion.extension (gaugeDiagonalPreGNSCLM n) 0 = 0 := by
    rw [← UniformSpace.Completion.coe_zero]
    rw [UniformSpace.Completion.extension_coe
      hLip.uniformContinuous]
    exact map_zero _
  have hdist := hExt.dist_le_mul x 0
  rw [hzero, dist_eq_norm, dist_eq_norm] at hdist
  simpa [gaugeDiagonalGNSMap, ContinuousLinearMap.coe_fromCompletion] using hdist

/-- The completed GNS map agrees with the finite diagonal cylinder map on
canonical algebra vectors. -/
@[simp] theorem gaugeDiagonalGNSMap_toPreGNS
    (n : ℕ) (A : CStarMatrixStage n) :
    gaugeDiagonalGNSMap n
        ((gaugeStateFamily.state n).functional.toPreGNS A :
          (gaugeStateFamily.state n).functional.GNS) =
      diagonalCylinderL2 n
        (diagonalPart n (cstarStageToBitWordStage n A)) := by
  change (gaugeDiagonalPreGNSCLM n).fromCompletion
      ((gaugeStateFamily.state n).functional.toPreGNS A) = _
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  simp [gaugeDiagonalPreGNSCLM, gaugeDiagonalPreGNSLinearMap,
    cstarDiagonalCylinderLinearMap, bitWordDiagonalLinearMap,
    cstarStageToBitWordStage]

/-- The completed finite-stage diagonal maps are compatible with the native
GNS successor transition. -/
theorem gaugeDiagonalGNSMap_transition_succ
    (n : ℕ) (x : gaugeGNSStage n) :
    gaugeDiagonalGNSMap (n + 1)
        (filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily
          (Nat.le.step (le_refl n)) x) =
      gaugeDiagonalGNSMap n x := by
  let T : gaugeGNSStage n →L[ℂ] L2Boundary :=
    (gaugeDiagonalGNSMap (n + 1)).comp
      (filteredGNSMapCLM gaugeStage gaugeSystem gaugeStateFamily
        (Nat.le.step (le_refl n)))
  have hfun : (T : gaugeGNSStage n → L2Boundary) =
      gaugeDiagonalGNSMap n := by
    apply UniformSpace.Completion.denseRange_coe.equalizer
    · exact T.continuous
    · exact (gaugeDiagonalGNSMap n).continuous
    · funext y
      obtain ⟨A, rfl⟩ :=
        (gaugeStateFamily.state n).functional.toPreGNS.surjective y
      change T
          ((gaugeStateFamily.state n).functional.toPreGNS A :
            gaugeGNSStage n) =
        gaugeDiagonalGNSMap n
          ((gaugeStateFamily.state n).functional.toPreGNS A :
            gaugeGNSStage n)
      simp only [T, ContinuousLinearMap.comp_apply,
        filteredGNSMapCLM_apply, filteredGNSMap_toPreGNS,
        gaugeDiagonalGNSMap_toPreGNS]
      exact cstarDiagonalCylinderLinearMap_succ n A
  simpa [T, filteredGNSMapCLM_apply] using congrFun hfun x

/-- Compatibility of the completed finite-stage diagonal maps for every
finite-stage inclusion. -/
theorem gaugeDiagonalGNSMap_transition
    {m n : ℕ} (hmn : m ≤ n) (x : gaugeGNSStage m) :
    gaugeDiagonalGNSMap n
        (filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily hmn x) =
      gaugeDiagonalGNSMap m x := by
  induction n, hmn using Nat.le_induction with
  | base =>
      rw [filteredGNSMap_id]
      rfl
  | succ n hmn ih =>
      calc
        gaugeDiagonalGNSMap (n + 1)
            (filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily
              (Nat.le.step hmn) x) =
          gaugeDiagonalGNSMap n
            (filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily hmn x) := by
              have hcomp := congrFun
                (filteredGNSMap_comp gaugeStage gaugeSystem gaugeStateFamily
                  hmn (Nat.le.step (le_refl n))) x
              have hproof :
                  le_trans hmn (Nat.le.step (le_refl n)) =
                    Nat.le.step hmn := Subsingleton.elim _ _
              have htransition :
                  filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily
                      (Nat.le.step hmn) x =
                    filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily
                      (Nat.le.step (le_refl n))
                        (filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily
                          hmn x) := by
                simpa [hproof] using hcomp.symm
              rw [htransition]
              exact gaugeDiagonalGNSMap_transition_succ n
                (filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily hmn x)
        _ = gaugeDiagonalGNSMap m x := ih

/-- The finite completed-GNS readouts, viewed as real-linear maps, form a
cocone over the native filtered GNS transition system. -/
def gaugeDiagonalGNSColimitStageMap (n : ℕ) :
    gaugeGNSStage n →ₗ[ℝ] L2Boundary :=
  (gaugeDiagonalGNSMap n).toLinearMap.restrictScalars ℝ

theorem gaugeDiagonalGNSColimitStageMap_compatible
    {m n : ℕ} (hmn : m ≤ n) (x : gaugeGNSStage m) :
    gaugeDiagonalGNSColimitStageMap n
        (realTransition (GNSStage gaugeStage gaugeSystem gaugeStateFamily)
          (filteredGNSIsometricDirectSystem
            gaugeStage gaugeSystem gaugeStateFamily) hmn x) =
      gaugeDiagonalGNSColimitStageMap m x := by
  change gaugeDiagonalGNSMap n
      (filteredGNSLinearIsometry gaugeStage gaugeSystem gaugeStateFamily hmn x) =
    gaugeDiagonalGNSMap m x
  rw [filteredGNSLinearIsometry_apply]
  exact gaugeDiagonalGNSMap_transition hmn x

/-- Real-linear descent of the coherent diagonal readouts to the genuine
algebraic module direct limit of the finite GNS spaces. -/
def gaugeDiagonalGNSAlgebraicColimitMapReal :
    AlgebraicGNSHilbertColimit gaugeStage gaugeSystem gaugeStateFamily →ₗ[ℝ]
      L2Boundary :=
  Module.DirectLimit.lift ℝ ℕ (GNSStage gaugeStage gaugeSystem gaugeStateFamily)
    (fun _ _ hij => realTransition
      (GNSStage gaugeStage gaugeSystem gaugeStateFamily)
      (filteredGNSIsometricDirectSystem gaugeStage gaugeSystem gaugeStateFamily) hij)
    gaugeDiagonalGNSColimitStageMap
    (by
      intro m n hmn x
      exact gaugeDiagonalGNSColimitStageMap_compatible hmn x)

@[simp] theorem gaugeDiagonalGNSAlgebraicColimitMapReal_stage
    (n : ℕ) (x : gaugeGNSStage n) :
    gaugeDiagonalGNSAlgebraicColimitMapReal
        (stageToDirectLimitLinearMap
          (GNSStage gaugeStage gaugeSystem gaugeStateFamily)
          (filteredGNSIsometricDirectSystem
            gaugeStage gaugeSystem gaugeStateFamily) n x) =
      gaugeDiagonalGNSMap n x := by
  change gaugeDiagonalGNSAlgebraicColimitMapReal
      (Module.DirectLimit.of ℝ ℕ
        (GNSStage gaugeStage gaugeSystem gaugeStateFamily)
        (fun i j hij => realTransition
          (GNSStage gaugeStage gaugeSystem gaugeStateFamily)
          (filteredGNSIsometricDirectSystem
            gaugeStage gaugeSystem gaugeStateFamily) hij) n x) = _
  rw [gaugeDiagonalGNSAlgebraicColimitMapReal,
    Module.DirectLimit.lift_of
      (g := gaugeDiagonalGNSColimitStageMap)
      (fun m n hmn x => gaugeDiagonalGNSColimitStageMap_compatible hmn x)
      (i := n) x]
  rfl

/-- Complex-linear descent of the compatible finite-stage diagonal maps to
the algebraic filtered GNS colimit. -/
def gaugeDiagonalGNSAlgebraicColimitMap :
    AlgebraicGNSHilbertColimit gaugeStage gaugeSystem gaugeStateFamily →ₗ[ℂ]
      L2Boundary where
  toFun := gaugeDiagonalGNSAlgebraicColimitMapReal
  map_add' := (gaugeDiagonalGNSAlgebraicColimitMapReal).map_add
  map_smul' := by
    intro c z
    induction z using Module.DirectLimit.induction_on with
    | ih n x =>
        rw [complex_smul_of]
        change gaugeDiagonalGNSAlgebraicColimitMapReal
            (stageToDirectLimitLinearMap
              (GNSStage gaugeStage gaugeSystem gaugeStateFamily)
              (filteredGNSIsometricDirectSystem
                gaugeStage gaugeSystem gaugeStateFamily) n (c • x)) =
          c • gaugeDiagonalGNSAlgebraicColimitMapReal
            (stageToDirectLimitLinearMap
              (GNSStage gaugeStage gaugeSystem gaugeStateFamily)
              (filteredGNSIsometricDirectSystem
                gaugeStage gaugeSystem gaugeStateFamily) n x)
        rw [gaugeDiagonalGNSAlgebraicColimitMapReal_stage,
          gaugeDiagonalGNSAlgebraicColimitMapReal_stage]
        exact (gaugeDiagonalGNSMap n).map_smul c x

@[simp] theorem gaugeDiagonalGNSAlgebraicColimitMap_stage
    (n : ℕ) (x : gaugeGNSStage n) :
    gaugeDiagonalGNSAlgebraicColimitMap
        (stageToDirectLimitLinearMap
          (GNSStage gaugeStage gaugeSystem gaugeStateFamily)
          (filteredGNSIsometricDirectSystem
            gaugeStage gaugeSystem gaugeStateFamily) n x) =
      gaugeDiagonalGNSMap n x := by
  exact gaugeDiagonalGNSAlgebraicColimitMapReal_stage n x

theorem gaugeDiagonalGNSAlgebraicColimitMap_norm_le
    (z : AlgebraicGNSHilbertColimit gaugeStage gaugeSystem gaugeStateFamily) :
    ‖gaugeDiagonalGNSAlgebraicColimitMap z‖ ≤ ‖z‖ := by
  induction z using Module.DirectLimit.induction_on with
  | ih n x =>
      change ‖gaugeDiagonalGNSAlgebraicColimitMap
          (stageToDirectLimitLinearMap
            (GNSStage gaugeStage gaugeSystem gaugeStateFamily)
            (filteredGNSIsometricDirectSystem
              gaugeStage gaugeSystem gaugeStateFamily) n x)‖ ≤
        ‖stageToDirectLimitLinearMap
          (GNSStage gaugeStage gaugeSystem gaugeStateFamily)
          (filteredGNSIsometricDirectSystem
            gaugeStage gaugeSystem gaugeStateFamily) n x‖
      rw [gaugeDiagonalGNSAlgebraicColimitMap_stage]
      rw [← stageToDirectLimitLinearIsometry_apply
        (GNSStage gaugeStage gaugeSystem gaugeStateFamily)
        (filteredGNSIsometricDirectSystem
          gaugeStage gaugeSystem gaugeStateFamily) n x]
      rw [(stageToDirectLimitLinearIsometry
        (GNSStage gaugeStage gaugeSystem gaugeStateFamily)
        (filteredGNSIsometricDirectSystem
          gaugeStage gaugeSystem gaugeStateFamily) n).norm_map]
      exact gaugeDiagonalGNSMap_norm_le n x

/-- Bounded complex-linear diagonal readout on the algebraic filtered GNS
colimit. -/
def gaugeDiagonalGNSAlgebraicColimitMapCLM :
    AlgebraicGNSHilbertColimit gaugeStage gaugeSystem gaugeStateFamily →L[ℂ]
      L2Boundary :=
  gaugeDiagonalGNSAlgebraicColimitMap.mkContinuous 1
    (by
      intro z
      simpa using gaugeDiagonalGNSAlgebraicColimitMap_norm_le z)

/-- Continuous extension of the algebraic diagonal readout to the completed
native filtered GNS Hilbert colimit. -/
def gaugeDiagonalGNSHilbertColimitMap :
    gaugeGNSHilbertColimit →L[ℂ] L2Boundary :=
  gaugeDiagonalGNSAlgebraicColimitMapCLM.fromCompletion

@[simp] theorem gaugeDiagonalGNSHilbertColimitMap_stage
    (n : ℕ) (x : gaugeGNSStage n) :
    gaugeDiagonalGNSHilbertColimitMap
        (gaugeGNSStageToColimit n x) = gaugeDiagonalGNSMap n x := by
  change gaugeDiagonalGNSAlgebraicColimitMapCLM.fromCompletion
      (stageToHilbertDirectLimit
        (GNSStage gaugeStage gaugeSystem gaugeStateFamily)
        (filteredGNSIsometricDirectSystem
          gaugeStage gaugeSystem gaugeStateFamily) n x) = _
  rw [stageToHilbertDirectLimit_apply,
    directLimitToCompletion,
    ContinuousLinearMap.fromCompletion_apply_coe]
  exact gaugeDiagonalGNSAlgebraicColimitMap_stage n x

/-- The GNS class of the finite diagonal matrix maps back to its Bernoulli
cylinder function. -/
noncomputable def gaugeDiagonalGNSStageDiagonalVector
    (n : ℕ) (f : DiagAlg n) : gaugeGNSStage n :=
  (gaugeStateFamily.state n).functional.toPreGNS
    ((cstarStageToBitWordStage n).symm (Matrix.diagonal f))

@[simp] theorem gaugeDiagonalGNSMap_diagonal_stage
    (n : ℕ) (f : DiagAlg n) :
    gaugeDiagonalGNSMap n (gaugeDiagonalGNSStageDiagonalVector n f) =
      diagonalCylinderL2 n f := by
  change gaugeDiagonalGNSMap n
      ((gaugeStateFamily.state n).functional.toPreGNS
        ((cstarStageToBitWordStage n).symm (Matrix.diagonal f)) :
          gaugeGNSStage n) = _
  rw [gaugeDiagonalGNSMap_toPreGNS]
  rw [(cstarStageToBitWordStage n).apply_symm_apply]
  simp [diagonalPart]

/-- The finite diagonal GNS representatives preserve the full complex inner
product of their Bernoulli boundary cylinder images. -/
theorem gaugeDiagonalGNSStageDiagonalVector_inner
    (n : ℕ) (f g : DiagAlg n) :
    inner ℂ (gaugeDiagonalGNSStageDiagonalVector n f)
        (gaugeDiagonalGNSStageDiagonalVector n g) =
      inner ℂ (diagonalCylinderL2 n f) (diagonalCylinderL2 n g) := by
  change inner ℂ
      ((gaugeStateFamily.state n).functional.toPreGNS
        ((cstarStageToBitWordStage n).symm (Matrix.diagonal f)) :
          (gaugeStateFamily.state n).functional.GNS)
      ((gaugeStateFamily.state n).functional.toPreGNS
        ((cstarStageToBitWordStage n).symm (Matrix.diagonal g)) :
          (gaugeStateFamily.state n).functional.GNS) = _
  rw [UniformSpace.Completion.inner_coe,
    PositiveLinearMap.preGNS_inner_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS]
  let D := star (Matrix.diagonal f) * Matrix.diagonal g
  have hprod :
      star ((cstarStageToBitWordStage n).symm (Matrix.diagonal f)) *
          (cstarStageToBitWordStage n).symm (Matrix.diagonal g) =
        (cstarStageToBitWordStage n).symm D := by
    apply (cstarStageToBitWordStage n).injective
    simp [D, map_mul, map_star]
  have hreadout :
      (gaugeStateFamily.state n).functional
          ((cstarStageToBitWordStage n).symm D) =
        bitWordMatrixTraceFunctional n D := by
    change (gaugeStateFamily.state n).functional
        (CStarMatrix.ofMatrixStarAlgEquiv (stageStarAlgEquiv n D)) = _
    exact gaugeStateFamily_canonical_bitWord_matrix_readout n D
  rw [hprod, hreadout]
  change bitWordMatrixTraceFunctional n
      (star (Matrix.diagonal f) * Matrix.diagonal g) = _
  rw [show star (Matrix.diagonal f) * Matrix.diagonal g =
      Matrix.diagonal (fun w => star (f w) * g w) by
        change Matrix.conjTranspose (Matrix.diagonal f) * Matrix.diagonal g = _
        rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
        simp]
  rw [bitWordMatrixTraceFunctional_diagonal,
    diagonalCylinderL2_inner]

/-- The completed GNS-colimit diagonal readout preserves inner products on
the canonical vectors coming from any one finite diagonal stage. -/
theorem gaugeDiagonalGNSHilbertColimitMap_inner_diagonal_stage
    (n : ℕ) (f g : DiagAlg n) :
    inner ℂ
        (gaugeGNSStageToColimit n
          (gaugeDiagonalGNSStageDiagonalVector n f))
        (gaugeGNSStageToColimit n
          (gaugeDiagonalGNSStageDiagonalVector n g)) =
      inner ℂ
        (gaugeDiagonalGNSHilbertColimitMap
          (gaugeGNSStageToColimit n
            (gaugeDiagonalGNSStageDiagonalVector n f)))
        (gaugeDiagonalGNSHilbertColimitMap
          (gaugeGNSStageToColimit n
            (gaugeDiagonalGNSStageDiagonalVector n g)) ) := by
  calc
    inner ℂ
        (gaugeGNSStageToColimit n
          (gaugeDiagonalGNSStageDiagonalVector n f))
        (gaugeGNSStageToColimit n
          (gaugeDiagonalGNSStageDiagonalVector n g)) =
      inner ℂ (gaugeDiagonalGNSStageDiagonalVector n f)
        (gaugeDiagonalGNSStageDiagonalVector n g) :=
      (gaugeGNSStageToColimit n).inner_map_map _ _
    _ = inner ℂ (diagonalCylinderL2 n f) (diagonalCylinderL2 n g) :=
      gaugeDiagonalGNSStageDiagonalVector_inner n f g
    _ = inner ℂ
        (gaugeDiagonalGNSHilbertColimitMap
          (gaugeGNSStageToColimit n
            (gaugeDiagonalGNSStageDiagonalVector n f)))
        (gaugeDiagonalGNSHilbertColimitMap
          (gaugeGNSStageToColimit n
            (gaugeDiagonalGNSStageDiagonalVector n g))) := by
      rw [gaugeDiagonalGNSHilbertColimitMap_stage,
        gaugeDiagonalGNSHilbertColimitMap_stage,
        gaugeDiagonalGNSMap_diagonal_stage,
        gaugeDiagonalGNSMap_diagonal_stage]

/-- The completed native finite-matrix GNS colimit has dense diagonal
readout in Bernoulli boundary `L²`: each finite cylinder is the readout of
the corresponding diagonal GNS vector, and the existing cylinder carrier is
dense. This does not identify the full noncommutative GNS colimit with `L²`. -/
theorem gaugeDiagonalGNSHilbertColimitMap_denseRange :
    DenseRange gaugeDiagonalGNSHilbertColimitMap := by
  apply (cylinderColimitToL2_denseRange).mono
  rintro y ⟨g, rfl⟩
  obtain ⟨⟨n, f⟩, hg⟩ := g.property
  have hstage :
      g = ⟨cylinder n f, cylinder_mem_colimit n f⟩ := by
    apply Subtype.ext
    exact hg.symm
  refine ⟨gaugeGNSStageToColimit n
    (gaugeDiagonalGNSStageDiagonalVector n f), ?_⟩
  rw [gaugeDiagonalGNSHilbertColimitMap_stage,
    gaugeDiagonalGNSMap_diagonal_stage, hstage,
    cylinderColimitToL2_stage]

end InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalGNSBridge

end
