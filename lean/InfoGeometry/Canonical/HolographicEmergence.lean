import InfoGeometry.Canonical.AnomalyInflow
import InfoGeometry.Canonical.ChiralTorsionBridge
import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.Canonical.WeylPathHysteresis
import InfoGeometry.Canonical.WeylAnomalySource

/-!
# Research.HolographicEmergence

Constructive theorem package for the holographic chain:

- emergent time-flow from Sinkhorn/Weyl gauge dynamics
- anomaly-to-scale (chiral phase) emergence
- torsion/path-dependence and explicit update-order hysteresis witness

This module provides the stable, non-vacuous components of the holographic 
emergence bridge. Degenerate zero-quadratic-form scaffolds have been removed.
-/

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.HolographicEmergence

open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.WeylInformationGauge
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.InformationTorsion
open InfoGeometry.Canonical.ChiralTorsionBridge
open InfoGeometry.Canonical.AnomalyInflow
open InfoGeometry.Canonical.TopologicalInvariants
open InfoGeometry.Canonical.SpectralInference

section TimeFlow

variable (n : Nat)

/-- Emergent time-flow law: one monotone Lyapunov tick per Sinkhorn step. -/
def EmergentTimeFlow (T : SinkhornTrajectory n) : Prop :=
  ∀ k : Nat, trajectoryLyapunovNext n T k ≤ trajectoryLyapunov n T k

/-- Theorem `emergentTimeFlow_of_sinkhornTrajectory`. -/
theorem emergentTimeFlow_of_sinkhornTrajectory
    (T : SinkhornTrajectory n) :
    EmergentTimeFlow n T := by
  intro k
  exact trajectoryLyapunov_monotone (n := n) T k

end TimeFlow

section AnomalyScale

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Anomaly-generated scale phase state (chiral branch). -/
abbrev AnomalyScalePhase (CI : ConformalInference E) : Prop :=
  CI.ChiralInferenceState

/-- Theorem `anomalyScalePhase_of_nonzeroAnomaly`. -/
theorem anomalyScalePhase_of_nonzeroAnomaly
    (CI : ConformalInference E)
    (hAnom : CI.chiralAnomalyOperator ≠ 0) :
    AnomalyScalePhase CI :=
  chiralInferenceState_of_nonzero_anomaly (CI := CI) hAnom

end AnomalyScale

section TorsionHysteresis

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Theorem `pathDependence_of_twistedInference`. -/
theorem pathDependence_of_twistedInference
    (T : TwistedInference E) :
    UpdateOrderPathDependent T.dual.nabla :=
  twistedInference_updateOrderPathDependent (T := T)

/-- Theorem `exists_gaugeOrderHysteresis_witness`. -/
theorem exists_gaugeOrderHysteresis_witness :
    ∃ (M : Coupling 2)
      (hrow : HasPositiveRowSums 2 M)
      (hcolRow : HasPositiveColSums 2 (rowNormalize 2 M hrow))
      (hcol : HasPositiveColSums 2 M)
      (hrowCol : HasPositiveRowSums 2 (colNormalize 2 M hcol)),
      UpdateOrderHysteresis 2 M hrow hcolRow hcol hrowCol := by
  refine ⟨weylOrderWitnessMatrix2,
    weylOrderWitnessMatrix2_positiveRows,
    weylOrderWitnessMatrix2_positiveCols_afterRow,
    weylOrderWitnessMatrix2_positiveCols,
    weylOrderWitnessMatrix2_positiveRows_afterCol,
    ?_⟩
  unfold UpdateOrderHysteresis rowThenColUpdate colThenRowUpdate
  intro hEq
  have h00 := congrArg (fun A => A (0 : Fin 2) (0 : Fin 2)) hEq
  norm_num [colNormalize, rowNormalize, rowSum, colSum, weylOrderWitnessMatrix2] at h00

end TorsionHysteresis

end InfoGeometry.Canonical.HolographicEmergence
