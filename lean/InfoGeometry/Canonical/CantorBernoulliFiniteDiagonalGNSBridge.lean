/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalTraceEnergy
import InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge

/-!
# Finite Bernoulli diagonal map on the native trace GNS stages

The finite BitWord trace-energy contraction transports to the native finite
C⋆ trace-state PreGNS norm and extends to each completed finite-stage GNS
space. This file does not yet descend the maps to the filtered GNS Hilbert
colimit.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace NNReal

namespace InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalGNSBridge

open InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalTraceEnergy
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalHilbertSchmidt
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagL2Embedding
open InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

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
    (bitWordStageStarAlgEquiv n).symm

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
      CStarMatrix.ofMatrixStarAlgEquiv (bitWordStageStarAlgEquiv n B) = A := by
    have hB : bitWordStageStarAlgEquiv n B =
        (CStarMatrix.ofMatrixStarAlgEquiv).symm A := by
      simp [B, cstarStageToBitWordStage]
    calc
      CStarMatrix.ofMatrixStarAlgEquiv (bitWordStageStarAlgEquiv n B) =
          CStarMatrix.ofMatrixStarAlgEquiv
            ((CStarMatrix.ofMatrixStarAlgEquiv).symm A) :=
        congrArg CStarMatrix.ofMatrixStarAlgEquiv hB
      _ = A := (CStarMatrix.ofMatrixStarAlgEquiv).apply_symm_apply A
  calc
    bitWordMatrixTraceFunctional n
        (star B * B) = bitWordMatrixGaugeReadout n (star B * B) :=
      (bitWordMatrixGaugeReadout_eq_trace n _).symm
    _ = (gaugeStateFamily.state n).functional
          (CStarMatrix.ofMatrixStarAlgEquiv
            (bitWordStageStarAlgEquiv n (star B * B))) :=
      (gaugeStateFamily_bitWord_matrix_readout n _).symm
    _ = (gaugeStateFamily.state n).functional (star A * A) := by
      congr 1
      calc
        CStarMatrix.ofMatrixStarAlgEquiv
            (bitWordStageStarAlgEquiv n (star B * B)) =
          star (CStarMatrix.ofMatrixStarAlgEquiv
              (bitWordStageStarAlgEquiv n B)) *
            CStarMatrix.ofMatrixStarAlgEquiv
              (bitWordStageStarAlgEquiv n B) := by
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

end InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalGNSBridge

end
