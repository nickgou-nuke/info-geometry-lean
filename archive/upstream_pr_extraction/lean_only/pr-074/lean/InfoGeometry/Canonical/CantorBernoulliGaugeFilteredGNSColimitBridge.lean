import InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
import InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeTraceBridge
import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
import InfoGeometry.Canonical.FilteredGNSHilbertColimit
import InfoGeometry.Canonical.FilteredGNSColimitRepresentation
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
import InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum

/-!
# Cantor–Bernoulli gauge states through the native filtered GNS colimit

The finite C⋆ matrix trace states and their compatible transition maps are
already constructed in `CantorBernoulliCStarMatrixTraceState`.  The generic
filtered GNS owners are already constructed in `FilteredGNSHilbertColimit`.
This file is only the concrete wire between them.

In particular, this owner does not introduce a completion of the infinite
Cuntz algebra, and it does not identify the finite matrix tower with a
finite-stage Cuntz family.  Its infinite object is the native filtered
inductive colimit of the finite-stage GNS Hilbert spaces.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 1000000

namespace InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeTraceBridge
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
open InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum
open scoped ComplexOrder InnerProductSpace NNReal

/-- The concrete finite-stage carrier for the Bernoulli/UHF gauge state. -/
abbrev gaugeStage := CStarMatrixStage

/-- The already constructed native star-inductive system of matrix stages. -/
abbrev gaugeSystem :
    ContinuousStarInductiveSystem gaugeStage :=
  cstarMatrixInductiveSystem

/-- The compatible normalized finite-stage gauge state family. -/
abbrev gaugeStateFamily :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      gaugeStage gaugeSystem :=
  cstarMatrixTraceStateFamily

/-- The finite-stage GNS Hilbert space attached to the concrete gauge state. -/
abbrev gaugeGNSStage (n : ℕ) : Type :=
  (gaugeStateFamily.state n).functional.GNS

/-- The native filtered inductive colimit of the finite-stage gauge GNS spaces. -/
abbrev gaugeGNSHilbertColimit : Type :=
  GNSHilbertColimit gaugeStage gaugeSystem gaugeStateFamily

/-- Canonical inclusion of a finite gauge GNS stage into the filtered colimit. -/
def gaugeGNSStageToColimit (n : ℕ) :
    gaugeGNSStage n →ₗᵢ[ℂ] gaugeGNSHilbertColimit :=
  gnsStageToHilbertColimit gaugeStage gaugeSystem gaugeStateFamily n

@[simp] theorem gaugeGNSStageToColimit_transition
    {m n : ℕ} (hmn : m ≤ n) (x : gaugeGNSStage m) :
    gaugeGNSStageToColimit n
        (filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily hmn x) =
      gaugeGNSStageToColimit m x := by
  exact gnsStageToHilbertColimit_transition
    gaugeStage gaugeSystem gaugeStateFamily hmn x

theorem gaugeGNSStageToColimit_norm
    (n : ℕ) (x : gaugeGNSStage n) :
    ‖gaugeGNSStageToColimit n x‖ = ‖x‖ := by
  exact (gaugeGNSStageToColimit n).norm_map x

/-- The finite-stage gauge GNS images generate the native colimit densely. -/
theorem dense_iUnion_range_gaugeGNSStageToColimit :
    Dense (⋃ n : ℕ, Set.range (gaugeGNSStageToColimit n)) :=
  dense_iUnion_range_gnsStageToHilbertColimit
    gaugeStage gaugeSystem gaugeStateFamily

theorem gaugeGNSHilbertColimit_complete :
    CompleteSpace gaugeGNSHilbertColimit :=
  inferInstance

/-- The concrete state readout on every finite stage is the normalized matrix
trace transported through Mathlib's finite C⋆ matrix carrier. -/
@[simp] theorem gaugeStateFamily_readout
    (n : ℕ) (A : CStarMatrixStage n) :
    (gaugeStateFamily.state n).functional A =
      cstarMatrixTraceFunctional n A := by
  rfl

theorem gaugeStateFamily_faithful
    (n : ℕ) (A : CStarMatrixStage n) :
    (gaugeStateFamily.state n).functional (star A * A) = 0 ↔ A = 0 :=
  cstarMatrixTraceState_faithful n A

/-! The finite matrix/GNS state family has the canonical word-kernel readout.
This is the concrete wire from the filtered C⋆-GNS stages to the binary-word
gauge data; it makes no claim about a completed infinite Cuntz state. -/

theorem gaugeStateFamily_bitWord_matrix_unit
    (n : ℕ) (u v : BitWord n) :
    (gaugeStateFamily.state n).functional
        (CStarMatrix.ofMatrixStarAlgEquiv
          (Matrix.single
            (InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeTraceBridge.bitWordIndexEquiv n u)
            (InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeTraceBridge.bitWordIndexEquiv n v)
            1)) =
      canonicalGaugeState (List.ofFn u) (List.ofFn v) := by
  rw [gaugeStateFamily_readout]
  change matrixTraceState n
      (Matrix.single
        (InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeTraceBridge.bitWordIndexEquiv n u)
        (InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeTraceBridge.bitWordIndexEquiv n v)
        1) = _
  exact matrixTraceState_bitWordUnit_eq_canonicalGaugeState n u v

/-! The arbitrary fixed-depth matrix readout is the transported Bernoulli
gauge trace.  This is a finite-stage statement; it does not identify the
filtered GNS colimit with an infinite C*-completion. -/

theorem gaugeStateFamily_bitWord_matrix_readout
    (n : ℕ) (A : BitWordMatrixStage n) :
    (gaugeStateFamily.state n).functional
        (CStarMatrix.ofMatrixStarAlgEquiv
          (bitWordStageStarAlgEquiv n A)) =
      bitWordMatrixGaugeReadout n A := by
  rw [gaugeStateFamily_readout]
  change cstarMatrixTraceFunctional n
      (CStarMatrix.ofMatrixStarAlgEquiv
        (bitWordStageStarAlgEquiv n A)) = _
  rw [cstarMatrixTraceFunctional_apply]
  change matrixTraceState n (bitWordStageStarAlgEquiv n A) = _
  symm
  exact bitWordMatrixGaugeReadout_transport n A

/-- The canonical finite-stage vacuum in the native Mathlib GNS construction. -/
noncomputable def gaugeGNSVacuum (n : ℕ) : gaugeGNSStage n :=
  InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsVacuum
    (gaugeStateFamily.state n).functional

/-- The finite-stage GNS vacuum recovers the native normalized matrix trace for
every observable, not only for the binary matrix-unit generators. -/
theorem gaugeGNSStage_matrix_expectation
    (n : ℕ) (A : CStarMatrixStage n) :
    ⟪gaugeGNSVacuum n,
      ((gaugeStateFamily.state n).functional.gnsStarAlgHom A)
        (gaugeGNSVacuum n)⟫_ℂ =
      (gaugeStateFamily.state n).functional A := by
  change
    ⟪InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsVacuum
        (gaugeStateFamily.state n).functional,
      ((gaugeStateFamily.state n).functional.gnsStarAlgHom A)
        (InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsVacuum
          (gaugeStateFamily.state n).functional)⟫_ℂ =
      (gaugeStateFamily.state n).functional A
  exact gns_state_expectation_recovery
    (gaugeStateFamily.state n).functional A

/-- The finite-stage GNS vacuum recovers the concrete word-kernel readout. -/
theorem gaugeGNSStage_bitWord_matrix_unit_expectation
    (n : ℕ) (u v : BitWord n) :
    ⟪gaugeGNSVacuum n,
      ((gaugeStateFamily.state n).functional.gnsStarAlgHom
        (CStarMatrix.ofMatrixStarAlgEquiv
          (Matrix.single
            (InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeTraceBridge.bitWordIndexEquiv n u)
            (InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeTraceBridge.bitWordIndexEquiv n v)
            1)))
        (gaugeGNSVacuum n)⟫_ℂ =
      canonicalGaugeState (List.ofFn u) (List.ofFn v) := by
  change
    ⟪InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsVacuum
        (gaugeStateFamily.state n).functional,
      ((gaugeStateFamily.state n).functional.gnsStarAlgHom
        (CStarMatrix.ofMatrixStarAlgEquiv
          (Matrix.single
            (InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeTraceBridge.bitWordIndexEquiv n u)
            (InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeTraceBridge.bitWordIndexEquiv n v)
            1)))
        (InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsVacuum
          (gaugeStateFamily.state n).functional)⟫_ℂ =
      canonicalGaugeState (List.ofFn u) (List.ofFn v)
  rw [InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gns_state_expectation_recovery]
  exact gaugeStateFamily_bitWord_matrix_unit n u v

end InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge
