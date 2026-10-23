/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge
import InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge

/-!
# Corrected finite quotient stages and the native Bernoulli GNS colimit

This is a downstream composition owner.  The finite quotient owner supplies
the corrected complex-* word-pair matrix stages and the filtered-GNS owner
supplies the native finite C⋆-stage expectation inside its Hilbert colimit.
The theorems below identify those existing readouts; they do not construct a
functional on the full infinite quotient, an infinite C⋆ completion, or
analytic KMS/Tomita data.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace InfoGeometry.Canonical.CantorBernoulliComplexStarFiniteStageGNSBridge

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open CStarStateColimit.Native.FilteredGNSTailRepresentation
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Canonical.CantorBernoulliDiagTraceBridge
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalTraceEnergy
open InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge
open InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeTraceBridge
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliLinearGaugeUHFFactorizationBridge
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open scoped ComplexOrder InnerProductSpace NNReal

/-! The native colimit vacuum and the corrected quotient finite-stage trace
have the same readout on every binary-word matrix stage. -/

theorem gaugeGNSColimitVacuum_complexStarFiniteStage_expectation
    (n : ℕ) (A : BitWordMatrixStage n) :
    ⟪gaugeGNSColimitVacuum,
      globalStageRepresentationStarAlgHom
        gaugeStage gaugeSystem gaugeStateFamily n
        (CStarMatrix.ofMatrixStarAlgEquiv
          (bitWordStageStarAlgEquiv n A))
        (gaugeGNSColimitVacuum)⟫_ℂ =
      complexStarFiniteStageTrace n A := by
  rw [gaugeGNSColimitVacuum_stage_expectation,
    gaugeStateFamily_bitWord_matrix_readout,
    bitWordMatrixGaugeReadout_eq_trace]
  exact (complexStarFiniteStageTrace_eq_matrixTrace n A).symm

/-! For independent word indices `u` and `v`, the same colimit expectation
recovers the existing Bernoulli word-core functional. -/

theorem gaugeGNSColimitVacuum_bitWordMatrixUnit_eq_phi0
    (n : ℕ)
    (u v : InfoGeometry.Canonical.UHFInductiveColimitBoundary.BitWord n) :
    ⟪gaugeGNSColimitVacuum,
      globalStageRepresentationStarAlgHom
        gaugeStage gaugeSystem gaugeStateFamily n
        (CStarMatrix.ofMatrixStarAlgEquiv
          (bitWordStageStarAlgEquiv n (Matrix.single u v (1 : ℂ))))
        (gaugeGNSColimitVacuum)⟫_ℂ =
      phi0 (wordMonomial (List.ofFn u) (List.ofFn v)) := by
  rw [gaugeGNSColimitVacuum_complexStarFiniteStage_expectation,
    complexStarFiniteStageTrace_matrixUnit_eq_phi0]

/-! The same corrected quotient stage reaches the projective-limit Bernoulli
integral on its diagonal subalgebra.  The carrier is the full noncommutative
finite matrix stage; only the observable is restricted to a diagonal matrix
for this measure readout.  This does not extend the integral to the full
infinite quotient or assert an analytic KMS state. -/

theorem gaugeGNSColimitVacuum_complexStarFiniteStage_diagonal_projective_integral
    (n : ℕ) (f : DiagAlg n) :
    ⟪gaugeGNSColimitVacuum,
      globalStageRepresentationStarAlgHom
        gaugeStage gaugeSystem gaugeStateFamily n
        (CStarMatrix.ofMatrixStarAlgEquiv
          (bitWordStageStarAlgEquiv n (Matrix.diagonal f)))
        (gaugeGNSColimitVacuum)⟫_ℂ =
      ∫ q, f (π n q) ∂projectiveLimitMeasure := by
  calc
    ⟪gaugeGNSColimitVacuum,
        globalStageRepresentationStarAlgHom
          gaugeStage gaugeSystem gaugeStateFamily n
          (CStarMatrix.ofMatrixStarAlgEquiv
            (bitWordStageStarAlgEquiv n (Matrix.diagonal f)))
          (gaugeGNSColimitVacuum)⟫_ℂ =
        complexStarFiniteStageTrace n (Matrix.diagonal f) :=
      gaugeGNSColimitVacuum_complexStarFiniteStage_expectation n
        (Matrix.diagonal f)
    _ = bitWordMatrixTraceFunctional n (Matrix.diagonal f) :=
      complexStarFiniteStageTrace_eq_matrixTrace n (Matrix.diagonal f)
    _ = InfoGeometry.Canonical.UHFInductiveLimitBoundary.stageTrace n f := by
      rw [stageTrace_eq_DiagTrace]
      exact bitWordMatrixTraceFunctional_diagonal n f
    _ = ∫ q, f (π n q) ∂projectiveLimitMeasure :=
      (projectiveLimitMeasure_integral_prefix_eq_stageTrace n f).symm

/-! The finite quotient-stage readout is cyclic.  This is the genuine
equal-depth/UHF-core normalized matrix-trace identity; it is not an
unrestricted modular-flow or KMS theorem on the Cuntz quotient. -/

theorem complexStarFiniteStageTrace_mul_comm
    (n : ℕ) (A B : BitWordMatrixStage n) :
    complexStarFiniteStageTrace n (A * B) =
      complexStarFiniteStageTrace n (B * A) := by
  rw [complexStarFiniteStageTrace_eq_matrixTrace,
    complexStarFiniteStageTrace_eq_matrixTrace,
    ← bitWordMatrixGaugeReadout_eq_trace,
    ← bitWordMatrixGaugeReadout_eq_trace]
  exact bitWordMatrixGaugeReadout_mul_comm n A B

/-! The same finite-core cyclicity is visible in the native filtered GNS
vacuum through the global stage representation. -/

theorem gaugeGNSColimitVacuum_complexStarFiniteStage_cyclic
    (n : ℕ) (A B : BitWordMatrixStage n) :
    ⟪gaugeGNSColimitVacuum,
      globalStageRepresentationStarAlgHom
        gaugeStage gaugeSystem gaugeStateFamily n
        (CStarMatrix.ofMatrixStarAlgEquiv
          (bitWordStageStarAlgEquiv n (A * B)))
        (gaugeGNSColimitVacuum)⟫_ℂ =
      ⟪gaugeGNSColimitVacuum,
        globalStageRepresentationStarAlgHom
          gaugeStage gaugeSystem gaugeStateFamily n
          (CStarMatrix.ofMatrixStarAlgEquiv
            (bitWordStageStarAlgEquiv n (B * A)))
          (gaugeGNSColimitVacuum)⟫_ℂ := by
  rw [gaugeGNSColimitVacuum_complexStarFiniteStage_expectation,
    gaugeGNSColimitVacuum_complexStarFiniteStage_expectation]
  exact complexStarFiniteStageTrace_mul_comm n A B

end InfoGeometry.Canonical.CantorBernoulliComplexStarFiniteStageGNSBridge
