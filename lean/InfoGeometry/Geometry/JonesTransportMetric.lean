/-
InfoGeometry/Geometry/JonesTransportMetric.lean

Metric reconstruction from admissible operatorial Jones transports.

The distance between projective polarization states is interpreted as the
minimal cost of admissible coherent transport. Nonunitary projectors/polarizers
are boundary or dissipative events, not ordinary isometries.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus

noncomputable section

namespace InfoGeometry.Geometry.JonesTransportMetric

open InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus

/--
A projective polarization state represented by an algebraic projector.
-/
structure ProjectivePolarizationState
    (Op : Type*) [Mul Op] where
  /-- Projector representative. -/
  P : Op

  /-- Idempotence of the representative. -/
  idem : IsProjector P

/--
A Jones transport takes one projective state to another.
-/
def JonesTransportRealizes
    {Op : Type*} [Mul Op]
    (J : OperatorialJonesDatum Op)
    (A B : ProjectivePolarizationState Op) : Prop :=
  J.transform A.P = B.P

/--
Admissibility for metric transport.

A concrete model should restrict this to coherent/lossless/unitary or
Krein-calibrated transports. Brewster projections generally fail this and
belong to the boundary/dissipative layer.
-/
def IsMetricAdmissibleJonesTransport
    {Op : Type*} [Mul Op]
    (_J : OperatorialJonesDatum Op) : Prop :=
  True

/--
Metric reconstructed from operatorial Jones transport costs.
-/
structure JonesTransportMetricDatum
    (Op : Type*) [Mul Op] where
  /-- Cost assigned to a Jones transport. -/
  cost : OperatorialJonesDatum Op → ℝ

  /-- Distance between projective polarization states. -/
  distance :
    ProjectivePolarizationState Op →
      ProjectivePolarizationState Op →
        ℝ

  /-- Nonnegativity of the reconstructed distance. -/
  nonnegative :
    ∀ A B, 0 ≤ distance A B

  /-- Self-distance is zero. -/
  zero_self :
    ∀ A, distance A A = 0

  /-- Symmetry of distance. -/
  symmetric :
    ∀ A B, distance A B = distance B A

  /--
  Transport lower bound: any admissible Jones transport realizing `A -> B`
  has cost at least the distance.
  -/
  distance_le_transport_cost :
    ∀ (J : OperatorialJonesDatum Op)
      (A B : ProjectivePolarizationState Op),
      IsMetricAdmissibleJonesTransport J →
      JonesTransportRealizes J A B →
        distance A B ≤ cost J


namespace JonesTransportMetricDatum

variable {Op : Type*} [Mul Op]
variable (M : JonesTransportMetricDatum Op)

/-- Re-export nonnegativity. -/
theorem distance_nonnegative
    (A B : ProjectivePolarizationState Op) :
    0 ≤ M.distance A B :=
  M.nonnegative A B

/-- Re-export self-distance. -/
theorem distance_self
    (A : ProjectivePolarizationState Op) :
    M.distance A A = 0 :=
  M.zero_self A

end JonesTransportMetricDatum

end InfoGeometry.Geometry.JonesTransportMetric
