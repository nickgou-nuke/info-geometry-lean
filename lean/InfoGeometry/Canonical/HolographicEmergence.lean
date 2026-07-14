import InfoGeometry.Canonical.AnomalyInflow
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

/-- Theorem `anomalyScalePhase_of_nonzeroAnomaly`. -/
theorem anomalyScalePhase_of_nonzeroAnomaly
    (CI : ConformalInference E)
    (hAnom : CI.chiralAnomalyOperator ≠ 0) :
    CI.IsChiralInference :=
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

/-- Lemma 1: the explicit 2×2 Weyl witness has the required row positivity. -/
theorem weylWitness_has_positive_rows :
    HasPositiveRowSums 2 weylOrderWitnessMatrix2 := by
  exact weylOrderWitnessMatrix2_positiveRows

/-- Lemma 2: row-normalizing the explicit witness leaves positive column sums. -/
theorem weylWitness_rowNormalize_has_positive_cols :
    HasPositiveColSums 2
      (rowNormalize 2 weylOrderWitnessMatrix2 weylWitness_has_positive_rows) := by
  exact weylOrderWitnessMatrix2_positiveCols_afterRow

/-- Lemma 3: the explicit 2×2 Weyl witness has the required column positivity. -/
theorem weylWitness_has_positive_cols :
    HasPositiveColSums 2 weylOrderWitnessMatrix2 := by
  exact weylOrderWitnessMatrix2_positiveCols

/-- Lemma 4: column-normalizing the explicit witness leaves positive row sums. -/
theorem weylWitness_colNormalize_has_positive_rows :
    HasPositiveRowSums 2
      (colNormalize 2 weylOrderWitnessMatrix2 weylWitness_has_positive_cols) := by
  exact weylOrderWitnessMatrix2_positiveRows_afterCol

/-- Lemma 5: the two normalization orders differ on the `(0,0)` entry. -/
theorem weylWitness_rowThenCol_ne_colThenRow :
    rowThenColUpdate 2 weylOrderWitnessMatrix2
        weylWitness_has_positive_rows
        weylWitness_rowNormalize_has_positive_cols
      ≠
      colThenRowUpdate 2 weylOrderWitnessMatrix2
        weylWitness_has_positive_cols
        weylWitness_colNormalize_has_positive_rows := by
  intro hEq
  have h00 := congrArg (fun A => A (0 : Fin 2) (0 : Fin 2)) hEq
  norm_num [rowThenColUpdate, colThenRowUpdate, colNormalize, rowNormalize, rowSum, colSum,
    weylOrderWitnessMatrix2, weylWitness_has_positive_rows, weylWitness_rowNormalize_has_positive_cols,
    weylWitness_has_positive_cols, weylWitness_colNormalize_has_positive_rows] at h00

/-- Lemma 6: the explicit witness has update-order hysteresis. -/
theorem weylWitness_updateOrderHysteresis :
    UpdateOrderHysteresis 2 weylOrderWitnessMatrix2
      weylWitness_has_positive_rows
      weylWitness_rowNormalize_has_positive_cols
      weylWitness_has_positive_cols
      weylWitness_colNormalize_has_positive_rows := by
  unfold UpdateOrderHysteresis
  exact weylWitness_rowThenCol_ne_colThenRow

/-- The explicit row-then-column Weyl witness has zero column residual after its column step. -/
theorem weylWitness_rowThenCol_colLyapunov_eq_zero :
    colLyapunov 2
      (rowThenColUpdate 2 weylOrderWitnessMatrix2
        weylWitness_has_positive_rows
        weylWitness_rowNormalize_has_positive_cols) = 0 := by
  exact colLyapunov_colNormalize_eq_zero (n := 2)
    (M := rowNormalize 2 weylOrderWitnessMatrix2 weylWitness_has_positive_rows)
    weylWitness_rowNormalize_has_positive_cols

/-- The explicit column-then-row Weyl witness has zero row residual after its row step. -/
theorem weylWitness_colThenRow_rowLyapunov_eq_zero :
    rowLyapunov 2
      (colThenRowUpdate 2 weylOrderWitnessMatrix2
        weylWitness_has_positive_cols
        weylWitness_colNormalize_has_positive_rows) = 0 := by
  exact rowLyapunov_rowNormalize_eq_zero (n := 2)
    (M := colNormalize 2 weylOrderWitnessMatrix2 weylWitness_has_positive_cols)
    weylWitness_colNormalize_has_positive_rows

/-- Theorem: an explicit 2×2 gauge-order hysteresis witness exists. -/
theorem exists_gaugeOrderHysteresis :
    ∃ (M : Coupling 2)
      (hrow : HasPositiveRowSums 2 M)
      (hcolRow : HasPositiveColSums 2 (rowNormalize 2 M hrow))
      (hcol : HasPositiveColSums 2 M)
      (hrowCol : HasPositiveRowSums 2 (colNormalize 2 M hcol)),
      UpdateOrderHysteresis 2 M hrow hcolRow hcol hrowCol := by
  exact ⟨weylOrderWitnessMatrix2,
    weylWitness_has_positive_rows,
    weylWitness_rowNormalize_has_positive_cols,
    weylWitness_has_positive_cols,
    weylWitness_colNormalize_has_positive_rows,
    weylWitness_updateOrderHysteresis⟩

end TorsionHysteresis

end InfoGeometry.Canonical.HolographicEmergence
