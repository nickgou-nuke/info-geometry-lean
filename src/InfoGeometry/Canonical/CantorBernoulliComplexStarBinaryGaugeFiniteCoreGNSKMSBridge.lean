/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CantorBernoulliComplexStarBinaryGaugeFiniteCore
import InfoGeometry.Canonical.CantorBernoulliComplexStarFiniteStageGNSBridge

/-!
# Finite binary gauge boundary in the native filtered GNS colimit

This owner connects the arbitrary-matrix finite binary carrier flow to the
already constructed filtered-GNS vacuum readout.  It introduces no new state,
completion, or dynamics: the finite-core boundary theorem and the existing
GNS expectation theorem are composed on the same matrix-stage carrier.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace InfoGeometry.Canonical.CantorBernoulliComplexStarBinaryGaugeFiniteCoreGNSKMSBridge

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open InfoGeometry.Canonical.CantorBernoulliComplexStarBinaryGaugeFiniteCore
open InfoGeometry.Canonical.CantorBernoulliComplexStarFiniteStageGNSBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge
open InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open scoped ComplexOrder InnerProductSpace

/-- The arbitrary-matrix finite binary boundary identity is read by the native
filtered-GNS colimit vacuum. -/
theorem gaugeGNSColimitVacuum_finiteCore_kms_boundary
    (z : ℂ) (n : ℕ) (A B : BitWordMatrixStage n) :
    ⟪gaugeGNSColimitVacuum,
      globalStageRepresentationStarAlgHom
        gaugeStage gaugeSystem gaugeStateFamily n
        (CStarMatrix.ofMatrixStarAlgEquiv
          (bitWordStageStarAlgEquiv n (A * finiteCoreFlow n z B)))
        (gaugeGNSColimitVacuum)⟫_ℂ =
      ⟪gaugeGNSColimitVacuum,
        globalStageRepresentationStarAlgHom
          gaugeStage gaugeSystem gaugeStateFamily n
          (CStarMatrix.ofMatrixStarAlgEquiv
            (bitWordStageStarAlgEquiv n (B * A)))
          (gaugeGNSColimitVacuum)⟫_ℂ := by
  rw [gaugeGNSColimitVacuum_complexStarFiniteStage_expectation,
    gaugeGNSColimitVacuum_complexStarFiniteStage_expectation,
    complexStarFiniteStageTrace_eq_matrixTrace,
    complexStarFiniteStageTrace_eq_matrixTrace]
  exact finiteCore_kms_boundary z n A B

end InfoGeometry.Canonical.CantorBernoulliComplexStarBinaryGaugeFiniteCoreGNSKMSBridge
