import Mathlib.Tactic
import InfoGeometry.Probability.DetectorPenroseEikonalRay
import InfoGeometry.Physics.BayesianTuringCantor
import InfoGeometry.QuantumGeometry.Projective.QGT

noncomputable section

open InfoGeometry.Probability.DetectorPenroseEikonalRay
open InfoGeometry.QuantumGeometry.Projective
open InfoGeometry.Physics.BayesianTuringCantor

namespace InfoGeometry.Integration.AnomalyIncidenceBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A non-zero Berry curvature/anomaly strictly breaks the `IsIncident` relation.
If two spacetime points X and Y have a determinant (norm) separation exactly
equal to a non-zero Berry curvature (anomalous mass generation), they cannot
be mutually incident to the same non-degenerate Penrose twistor. -/
theorem berry_anomaly_breaks_incidence
    (Z : PenroseTwistor) (X Y : Vec22)
    (ψ : NormalizedState H) (A B : H →L[ℂ] H)
    (h_anomaly : berryCurvature ψ A B ≠ 0)
    (h_mass : detVec22 (subVec22 X Y) = berryCurvature ψ A B) :
    ¬ (IsIncident Z X ∧ IsIncident Z Y ∧ (Z.pi.p0 ≠ 0 ∨ Z.pi.p1 ≠ 0)) := by
  intro h
  rcases h with ⟨hX, hY, h_pi⟩
  have h_null := penrose_incidence_null_separation Z X Y hX hY h_pi
  rw [h_mass] at h_null
  exact h_anomaly h_null.symm

end InfoGeometry.Integration.AnomalyIncidenceBridge
