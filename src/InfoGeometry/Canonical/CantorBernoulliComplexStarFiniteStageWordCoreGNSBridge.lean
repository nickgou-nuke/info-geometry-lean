/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CantorBernoulliComplexStarFiniteStageGNSBridge
import InfoGeometry.Canonical.CantorBernoulliComplexStarBinaryGaugeFiniteCore
import InfoGeometry.Canonical.CantorBernoulliComplexStarBinaryGaugeFiniteCoreGNSKMSBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageWordCoreBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge

/-!
# Algebraic word-core readout in the native filtered GNS colimit

The finite gauge word-core functional, the corrected quotient finite-stage
trace, and the native filtered-GNS colimit vacuum are identified on every
finite matrix stage.  The matrix is arbitrary, so this is not a diagonal or
commutative reduction.  The result remains finite-stage and does not assert a
functional on the full infinite quotient or an analytic KMS/Tomita theorem.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace InfoGeometry.Canonical.CantorBernoulliComplexStarFiniteStageWordCoreGNSBridge

open scoped ComplexOrder InnerProductSpace

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open InfoGeometry.Canonical.CantorBernoulliComplexStarFiniteStageGNSBridge
open InfoGeometry.Canonical.CantorBernoulliComplexStarBinaryGaugeFiniteCore
open InfoGeometry.Canonical.CantorBernoulliComplexStarBinaryGaugeFiniteCoreGNSKMSBridge
open InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageWordCoreBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliBitWordStarInductiveSystemBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliLinearGaugeUHFFactorizationBridge

theorem gaugeGNSColimitVacuum_wordCoreFiniteStage_expectation_eq_phi0
    (n : ℕ) (A : BitWordMatrixStage n) :
    ⟪gaugeGNSColimitVacuum,
      globalStageRepresentationStarAlgHom
        gaugeStage gaugeSystem gaugeStateFamily n
        (CStarMatrix.ofMatrixStarAlgEquiv
          (bitWordStageStarAlgEquiv n A))
        gaugeGNSColimitVacuum⟫_ℂ =
      phi0 (wordCoreFiniteStageElement n A) := by
  calc
    ⟪gaugeGNSColimitVacuum,
        globalStageRepresentationStarAlgHom
          gaugeStage gaugeSystem gaugeStateFamily n
          (CStarMatrix.ofMatrixStarAlgEquiv
            (bitWordStageStarAlgEquiv n A))
          gaugeGNSColimitVacuum⟫_ℂ =
        complexStarFiniteStageTrace n A :=
      gaugeGNSColimitVacuum_complexStarFiniteStage_expectation n A
    _ = phi0 (wordCoreFiniteStageElement n A) :=
      (phi0_wordCoreFiniteStageElement_eq_complexStarFiniteStageTrace n A).symm

/-! The word-core readout is compatible with the already constructed dyadic
`StarAlgHom` stage embedding.  This is a statement about arbitrary finite
matrix stages; it does not extend `phi0` to the infinite quotient. -/

theorem phi0_wordCoreFiniteStageElement_dyadic_compatible
    (n : ℕ) (A : BitWordMatrixStage n) :
    phi0 (wordCoreFiniteStageElement (n + 1)
      (bitWordDyadicStarEmbedding n A)) =
      phi0 (wordCoreFiniteStageElement n A) := by
  rw [phi0_wordCoreFiniteStageElement_eq_complexStarFiniteStageTrace,
    phi0_wordCoreFiniteStageElement_eq_complexStarFiniteStageTrace]
  exact complexStarFiniteStageTrace_transition n A

theorem phi0_wordCoreFiniteStageElement_map_compatible
    {i j : ℕ} (hij : i ≤ j) (A : BitWordMatrixStage i) :
    phi0 (wordCoreFiniteStageElement j
      (bitWordStarMap bitWordDyadicStarData hij A)) =
      phi0 (wordCoreFiniteStageElement i A) := by
  rw [phi0_wordCoreFiniteStageElement_eq_complexStarFiniteStageTrace,
    phi0_wordCoreFiniteStageElement_eq_complexStarFiniteStageTrace,
    complexStarFiniteStageTrace_eq_matrixTrace,
    complexStarFiniteStageTrace_eq_matrixTrace]
  exact bitWordDyadicStarMap_trace_compatible hij A

theorem phi0_wordCoreFiniteStageElement_finiteCore_kms_boundary
    (z : ℂ) (n : ℕ) (A B : BitWordMatrixStage n) :
    phi0 (wordCoreFiniteStageElement n
      (A * finiteCoreFlow n z B)) =
      phi0 (wordCoreFiniteStageElement n (B * A)) := by
  rw [phi0_wordCoreFiniteStageElement_eq_complexStarFiniteStageTrace,
    phi0_wordCoreFiniteStageElement_eq_complexStarFiniteStageTrace,
    complexStarFiniteStageTrace_eq_matrixTrace,
    complexStarFiniteStageTrace_eq_matrixTrace]
  exact finiteCore_kms_boundary z n A B

theorem gaugeGNSColimitVacuum_finiteCore_kms_boundary_wordCore
    (z : ℂ) (n : ℕ) (A B : BitWordMatrixStage n) :
    ⟪gaugeGNSColimitVacuum,
      globalStageRepresentationStarAlgHom
        gaugeStage gaugeSystem gaugeStateFamily n
        (CStarMatrix.ofMatrixStarAlgEquiv
          (bitWordStageStarAlgEquiv n
            (A * finiteCoreFlow n z B)))
        gaugeGNSColimitVacuum⟫_ℂ =
      phi0 (wordCoreFiniteStageElement n (B * A)) := by
  calc
    ⟪gaugeGNSColimitVacuum,
        globalStageRepresentationStarAlgHom
          gaugeStage gaugeSystem gaugeStateFamily n
          (CStarMatrix.ofMatrixStarAlgEquiv
            (bitWordStageStarAlgEquiv n
              (A * finiteCoreFlow n z B)))
          gaugeGNSColimitVacuum⟫_ℂ =
        ⟪gaugeGNSColimitVacuum,
          globalStageRepresentationStarAlgHom
            gaugeStage gaugeSystem gaugeStateFamily n
            (CStarMatrix.ofMatrixStarAlgEquiv
              (bitWordStageStarAlgEquiv n (B * A)))
            gaugeGNSColimitVacuum⟫_ℂ :=
      gaugeGNSColimitVacuum_finiteCore_kms_boundary z n A B
    _ = phi0 (wordCoreFiniteStageElement n (B * A)) :=
      gaugeGNSColimitVacuum_wordCoreFiniteStage_expectation_eq_phi0 n (B * A)

end InfoGeometry.Canonical.CantorBernoulliComplexStarFiniteStageWordCoreGNSBridge
