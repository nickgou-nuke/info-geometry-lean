import InfoGeometry.Canonical.AnomalyInflow
import InfoGeometry.Canonical.ChiralTorsionBridge
import InfoGeometry.Canonical.WeylInformationGauge

/-!
# Research.HolographicEmergence

Constructive theorem package for the full chain:

- emergent time-flow from Sinkhorn/Weyl gauge dynamics
- anomaly-to-scale (chiral phase) emergence
- torsion/path-dependence and explicit update-order hysteresis witness
- boundary anomaly cancellation plus vacuum-apex twistor lift
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
open InfoGeometry.Twistor

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
      UpdateOrderHysteresis 2 M hrow hcolRow hcol hrowCol :=
  exists_updateOrderHysteresis_n2

end TorsionHysteresis

section BoundaryTwistor

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- Boundary closure: bulk variation cancels boundary anomaly. -/
theorem boundaryAnomalyCancellation
    (L : BayesianLoop E) (IST : InfoSpectralTriple E) :
    AnomalyInflowClosure (E := E) L IST :=
  anomalyInflowClosure (E := E) L IST

/-- Canonical degenerate null quadratic form on doubled space. -/
noncomputable def zeroVacuumApexQuadraticForm :
    QuadraticForm ℝ (InfoGeometry.Krein.DoubledSpace E) := 0

@[simp] lemma zeroVacuumApexQuadraticForm_apply
    (v : InfoGeometry.Krein.DoubledSpace E) :
    zeroVacuumApexQuadraticForm (E := E) v = 0 := rfl

/--
Canonical nullness witness for any nonzero doubled representative under the
degenerate vacuum-apex quadratic form.
-/
lemma isVacuumApexNull_zeroVacuumApexQuadraticForm
    (v : UnnormalizedProjectiveState (E := E)) :
    IsVacuumApexNull (E := E) (zeroVacuumApexQuadraticForm (E := E)) v := by
  simp [IsVacuumApexNull, zeroVacuumApexQuadraticForm]

/-- Null vacuum-apex representative lifts to a twistor point from an explicit null witness. -/
theorem vacuumApexNull_lifts_to_twistor_of_isVacuumApexNull
    (Q : QuadraticForm ℝ (InfoGeometry.Krein.DoubledSpace E))
    (v : UnnormalizedProjectiveState (E := E))
    (hNull : IsVacuumApexNull (E := E) Q v) :
    ∃ t : DoubledTwistorSpace (E := E) Q, t = vacuumApexTwistor (E := E) Q v hNull := by
  exact ⟨vacuumApexTwistor (E := E) Q v hNull, rfl⟩

/-- Canonical closure proposition for vacuum-apex twistor lift. -/
def VacuumApexTwistorClosure
    (Q : QuadraticForm ℝ (InfoGeometry.Krein.DoubledSpace E))
    (v : UnnormalizedProjectiveState (E := E)) : Prop :=
  ∃ t : DoubledTwistorSpace (E := E) Q,
    ∃ hNull : IsVacuumApexNull (E := E) Q v,
      t = vacuumApexTwistor (E := E) Q v hNull

/--
Constructive closure witness: explicit nullness gives the twistor-lift closure.
-/
theorem vacuumApexTwistorClosure_of_isVacuumApexNull
    (Q : QuadraticForm ℝ (InfoGeometry.Krein.DoubledSpace E))
    (v : UnnormalizedProjectiveState (E := E))
    (hNull : IsVacuumApexNull (E := E) Q v) :
    VacuumApexTwistorClosure (E := E) Q v := by
  refine ⟨vacuumApexTwistor (E := E) Q v hNull, hNull, rfl⟩

/--
Canonical twistor lift with no external nullness hypothesis:
the null witness is discharged by `zeroVacuumApexQuadraticForm`.
-/
theorem vacuumApexNull_lifts_to_twistor
    (v : UnnormalizedProjectiveState (E := E)) :
    ∃ t : DoubledTwistorSpace (E := E) (zeroVacuumApexQuadraticForm (E := E)),
      t = vacuumApexTwistor (E := E)
        (zeroVacuumApexQuadraticForm (E := E))
        v
        (isVacuumApexNull_zeroVacuumApexQuadraticForm (E := E) v) := by
  exact vacuumApexNull_lifts_to_twistor_of_isVacuumApexNull (E := E)
    (Q := zeroVacuumApexQuadraticForm (E := E))
    (v := v)
    (hNull := isVacuumApexNull_zeroVacuumApexQuadraticForm (E := E) v)

/--
Backward-compatible alias for the canonical zero-null twistor lift.
-/
theorem vacuumApexNull_lifts_to_twistor_zeroVacuumApexQuadraticForm
    (v : UnnormalizedProjectiveState (E := E)) :
    ∃ t : DoubledTwistorSpace (E := E) (zeroVacuumApexQuadraticForm (E := E)),
      t = vacuumApexTwistor (E := E)
        (zeroVacuumApexQuadraticForm (E := E))
        v
        (isVacuumApexNull_zeroVacuumApexQuadraticForm (E := E) v) := by
  exact vacuumApexNull_lifts_to_twistor (E := E) v

/--
Closure-first twistor lift: no external nullness hypothesis is required.
-/
theorem vacuumApexTwistorClosure_zeroVacuumApexQuadraticForm
    (v : UnnormalizedProjectiveState (E := E)) :
    VacuumApexTwistorClosure
      (E := E)
      (zeroVacuumApexQuadraticForm (E := E))
      v := by
  exact vacuumApexTwistorClosure_of_isVacuumApexNull
    (E := E)
    (Q := zeroVacuumApexQuadraticForm (E := E))
    (v := v)
    (hNull := isVacuumApexNull_zeroVacuumApexQuadraticForm (E := E) v)

end BoundaryTwistor

section Package

variable (n : Nat)
variable {X : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [FiniteDimensional ℝ X]

/--
Full constructive holographic-emergence package in one theorem:
time-flow + anomaly-scale + torsion/hysteresis + boundary/twistor closure.
-/
theorem holographicEmergence_package_of_isVacuumApexNull
    (Tflow : SinkhornTrajectory n)
    (CI : ConformalInference X)
    (hAnom : CI.chiralAnomalyOperator ≠ 0)
    (Tw : TwistedInference X)
    (L : BayesianLoop X)
    (IST : InfoSpectralTriple X)
    (Q : QuadraticForm ℝ (InfoGeometry.Krein.DoubledSpace X))
    (v : UnnormalizedProjectiveState (E := X))
    (hNull : IsVacuumApexNull (E := X) Q v) :
    EmergentTimeFlow n Tflow
      ∧ AnomalyScalePhase CI
      ∧ UpdateOrderPathDependent Tw.dual.nabla
      ∧ (∃ (M : Coupling 2)
          (hrow : HasPositiveRowSums 2 M)
          (hcolRow : HasPositiveColSums 2 (rowNormalize 2 M hrow))
          (hcol : HasPositiveColSums 2 M)
      (hrowCol : HasPositiveRowSums 2 (colNormalize 2 M hcol)),
          UpdateOrderHysteresis 2 M hrow hcolRow hcol hrowCol)
      ∧ AnomalyInflowClosure (E := X) L IST
      ∧ (∃ t : DoubledTwistorSpace (E := X) Q, t = vacuumApexTwistor (E := X) Q v hNull) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact emergentTimeFlow_of_sinkhornTrajectory (n := n) Tflow
  · exact anomalyScalePhase_of_nonzeroAnomaly (CI := CI) hAnom
  · exact pathDependence_of_twistedInference (T := Tw)
  · exact exists_gaugeOrderHysteresis_witness
  · exact boundaryAnomalyCancellation (E := X) L IST
  · exact vacuumApexNull_lifts_to_twistor_of_isVacuumApexNull (E := X) Q v hNull

/--
Full constructive holographic-emergence package in canonical zero-null form.
This removes the external `hNull` argument from the user-facing API.
-/
theorem holographicEmergence_package
    (Tflow : SinkhornTrajectory n)
    (CI : ConformalInference X)
    (hAnom : CI.chiralAnomalyOperator ≠ 0)
    (Tw : TwistedInference X)
    (L : BayesianLoop X)
    (IST : InfoSpectralTriple X)
    (v : UnnormalizedProjectiveState (E := X)) :
    EmergentTimeFlow n Tflow
      ∧ AnomalyScalePhase CI
      ∧ UpdateOrderPathDependent Tw.dual.nabla
      ∧ (∃ (M : Coupling 2)
          (hrow : HasPositiveRowSums 2 M)
          (hcolRow : HasPositiveColSums 2 (rowNormalize 2 M hrow))
          (hcol : HasPositiveColSums 2 M)
          (hrowCol : HasPositiveRowSums 2 (colNormalize 2 M hcol)),
          UpdateOrderHysteresis 2 M hrow hcolRow hcol hrowCol)
      ∧ AnomalyInflowClosure (E := X) L IST
      ∧ (∃ t : DoubledTwistorSpace (E := X) (zeroVacuumApexQuadraticForm (E := X)),
          t = vacuumApexTwistor (E := X)
            (zeroVacuumApexQuadraticForm (E := X))
            v
            (isVacuumApexNull_zeroVacuumApexQuadraticForm (E := X) v)) := by
  exact holographicEmergence_package_of_isVacuumApexNull (n := n)
    (Tflow := Tflow) (CI := CI) (hAnom := hAnom) (Tw := Tw)
    (L := L) (IST := IST)
    (Q := zeroVacuumApexQuadraticForm (E := X))
    (v := v)
    (hNull := isVacuumApexNull_zeroVacuumApexQuadraticForm (E := X) v)

/--
Backward-compatible alias for the canonical zero-null package.
-/
theorem holographicEmergence_package_zeroVacuumApexQuadraticForm
    (Tflow : SinkhornTrajectory n)
    (CI : ConformalInference X)
    (hAnom : CI.chiralAnomalyOperator ≠ 0)
    (Tw : TwistedInference X)
    (L : BayesianLoop X)
    (IST : InfoSpectralTriple X)
    (v : UnnormalizedProjectiveState (E := X)) :
    EmergentTimeFlow n Tflow
      ∧ AnomalyScalePhase CI
      ∧ UpdateOrderPathDependent Tw.dual.nabla
      ∧ (∃ (M : Coupling 2)
          (hrow : HasPositiveRowSums 2 M)
          (hcolRow : HasPositiveColSums 2 (rowNormalize 2 M hrow))
          (hcol : HasPositiveColSums 2 M)
          (hrowCol : HasPositiveRowSums 2 (colNormalize 2 M hcol)),
          UpdateOrderHysteresis 2 M hrow hcolRow hcol hrowCol)
      ∧ AnomalyInflowClosure (E := X) L IST
      ∧ (∃ t : DoubledTwistorSpace (E := X) (zeroVacuumApexQuadraticForm (E := X)),
          t = vacuumApexTwistor (E := X)
            (zeroVacuumApexQuadraticForm (E := X))
            v
            (isVacuumApexNull_zeroVacuumApexQuadraticForm (E := X) v)) := by
  exact holographicEmergence_package (n := n)
    (Tflow := Tflow) (CI := CI) (hAnom := hAnom) (Tw := Tw)
    (L := L) (IST := IST) (v := v)

end Package

end InfoGeometry.Canonical.HolographicEmergence
