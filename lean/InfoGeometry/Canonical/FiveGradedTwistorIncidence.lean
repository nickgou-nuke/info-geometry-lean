import InfoGeometry.Canonical.ConformalFiveGradeInversion
import InfoGeometry.Twistor.Incidence
import InfoGeometry.Krein.DoubledSpace

noncomputable section

/-!
# InfoGeometry.Canonical.FiveGradedTwistorIncidence

Theorem-safe bridge for the incidence equations of the five-graded twistor
model.

This file keeps the layers separated:
- the five-grade inversion is owned by `ConformalFiveGradeInversion`;
- the classical twistor incidence equation is owned by `Twistor.Incidence`;
- the real doubled phase axis is owned by `Krein.DoubledSpace`;
- the boundary / Majorana / zero-mode readouts remain explicit witness data.

No current-algebra anomaly is introduced here.
-/

namespace InfoGeometry.Canonical.FiveGradedTwistorIncidence

open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Clifford.Soldering
open InfoGeometry.Twistor.Incidence
open InfoGeometry.Krein

local notation "Spin" => (ℝ × ℝ)

/--
Five-graded twistor incidence packet.

`phaseAxis` is the internal real phase generator, abstractly satisfying
`phaseAxis^2 = -1` on the spinor carrier.

The equations are kept as explicit witnesses:
- `incidenceEquation`: `ω = I x π`;
- `majoranaEquation`: `JZ = Z`;
- `boundaryProjection`: `P_∂ Z = Z`;
- `boundaryZeroMode`: `D_∂ Z = 0`.
-/
structure FiveGradedTwistorIncidencePacket where
  inversion : FiveGradedConformalInversion Vec22
  twistor : Twistor
  point : Vec22

  /-- Internal phase axis replacing the external scalar `i`. -/
  phaseAxis : Spin →L[ℝ] Spin

  /-- The phase axis squares to minus the identity. -/
  phaseAxis_sq : phaseAxis.comp phaseAxis = - (ContinuousLinearMap.id ℝ Spin)

  /-- Majorana boundary reality condition. -/
  boundaryProjector : Spin →L[ℝ] Spin
  boundaryProjector_idem : boundaryProjector.comp boundaryProjector = boundaryProjector
  boundaryOperator : Spin →L[ℝ] Spin

namespace FiveGradedTwistorIncidencePacket

def incidenceEquation (P : FiveGradedTwistorIncidencePacket) : Prop :=
  P.twistor.1 = InfoGeometry.Twistor.Incidence.pointAction P.point P.twistor.2

def majoranaEquation (P : FiveGradedTwistorIncidencePacket) : Prop :=
  (P.phaseAxis P.twistor.1, P.phaseAxis P.twistor.2) = P.twistor

def boundaryProjection (P : FiveGradedTwistorIncidencePacket) : Prop :=
  P.boundaryProjector P.twistor.1 = P.twistor.1 ∧
    P.boundaryProjector P.twistor.2 = P.twistor.2

def boundaryZeroMode (P : FiveGradedTwistorIncidencePacket) : Prop :=
  P.boundaryOperator P.twistor.1 = 0 ∧ P.boundaryOperator P.twistor.2 = 0

end FiveGradedTwistorIncidencePacket

namespace FiveGradedTwistorIncidencePacket

variable {P : FiveGradedTwistorIncidencePacket}

@[simp]
theorem incidenceEquation_iff :
    P.incidenceEquation ↔
      P.twistor.1 = InfoGeometry.Twistor.Incidence.pointAction P.point P.twistor.2 :=
  Iff.rfl

@[simp]
theorem majoranaEquation_iff :
    P.majoranaEquation ↔ (P.phaseAxis P.twistor.1, P.phaseAxis P.twistor.2) = P.twistor :=
  Iff.rfl

@[simp]
theorem boundaryProjection_iff :
    P.boundaryProjection ↔
      P.boundaryProjector P.twistor.1 = P.twistor.1 ∧
        P.boundaryProjector P.twistor.2 = P.twistor.2 :=
  Iff.rfl

@[simp]
theorem boundaryZeroMode_iff :
    P.boundaryZeroMode ↔
      P.boundaryOperator P.twistor.1 = 0 ∧ P.boundaryOperator P.twistor.2 = 0 :=
  Iff.rfl

/-- The twistor incidence predicate is the classical point-action equation. -/
theorem incident_iff_twistorEquation :
    InfoGeometry.Twistor.Incidence.Incident P.twistor P.point ↔
      P.twistor.1 = InfoGeometry.Twistor.Incidence.pointAction P.point P.twistor.2 :=
  Iff.rfl

/-- The packet’s incidence witness recovers the classical incident predicate. -/
theorem incident_of_incidenceEquation (h : P.incidenceEquation) :
    InfoGeometry.Twistor.Incidence.Incident P.twistor P.point := by
  simpa [InfoGeometry.Twistor.Incidence.Incident] using h

/-- The five-grade inversion swaps source and sink sectors. -/
theorem source_iff_sink (x : Vec22) :
    x ∈ P.inversion.sourceSet ↔ P.inversion.theta x ∈ P.inversion.sinkSet :=
  P.inversion.mem_source_iff_mem_sink x

/-- The five-grade inversion swaps incoming and outgoing sectors. -/
theorem incoming_iff_outgoing (x : Vec22) :
    x ∈ P.inversion.incomingSet ↔ P.inversion.theta x ∈ P.inversion.outgoingSet :=
  P.inversion.mem_incoming_iff_mem_outgoing x

/-- The five-grade inversion fixes the modular center. -/
theorem center_iff_center (x : Vec22) :
    x ∈ P.inversion.centerSet ↔ P.inversion.theta x ∈ P.inversion.centerSet :=
  P.inversion.mem_center_iff_mem_center x

/--
Null separation for two points incident with the same twistor.

This is the classical twistor-incidence theorem re-exposed at the five-graded
surface.
-/
theorem incident_points_null_separated
    (X Y : Vec22)
    (hX : InfoGeometry.Twistor.Incidence.Incident P.twistor X)
    (hY : InfoGeometry.Twistor.Incidence.Incident P.twistor Y)
    (h_pi : P.twistor.2 ≠ 0) :
    q22 (X - Y) = 0 :=
  InfoGeometry.Twistor.Incidence.incident_points_null_separated P.twistor X Y hX hY h_pi

end FiveGradedTwistorIncidencePacket

end InfoGeometry.Canonical.FiveGradedTwistorIncidence
