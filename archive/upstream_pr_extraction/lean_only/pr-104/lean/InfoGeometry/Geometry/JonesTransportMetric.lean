/-
InfoGeometry/Geometry/JonesTransportMetric.lean

Metric reconstruction from admissible operatorial Jones transports.

The distance between projective polarization states is interpreted as the
minimal cost of admissible coherent transport. Nonunitary projectors/polarizers
are boundary or dissipative events, not ordinary isometries.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus

noncomputable section

namespace InfoGeometry.Geometry.JonesTransportMetric

open InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus

/-!
A projective polarization state is the native subtype of algebraic
projectors.  This replaces the former one-field property structure while
retaining the `P` and `idem` accessors used by the owner API.
-/
abbrev ProjectivePolarizationState
    (Op : Type*) [Mul Op] :=
  {P : Op // IsProjector P}

namespace ProjectivePolarizationState

abbrev P {Op : Type*} [Mul Op]
    (A : ProjectivePolarizationState Op) : Op :=
  A.1

abbrev idem {Op : Type*} [Mul Op]
    (A : ProjectivePolarizationState Op) : IsProjector A.P :=
  A.2

end ProjectivePolarizationState

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

Metric reconstructed from operatorial Jones transport costs.
-/
structure JonesTransportMetricDatum
    (Op : Type*) [Mul Op] where
  /--
  Model-specific admissible transport predicate.

  A concrete model can restrict this to lossless, Krein-calibrated, coherent, or
  other theorem-owned transport classes. This file does not manufacture such a
  class from an arbitrary property on `OperatorialJonesDatum`.
  -/
  admissible : OperatorialJonesDatum Op → Prop

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
      admissible J →
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

/-- Re-export symmetry of the reconstructed transport distance. -/
theorem distance_symm
    (A B : ProjectivePolarizationState Op) :
    M.distance A B = M.distance B A :=
  M.symmetric A B

end JonesTransportMetricDatum

end InfoGeometry.Geometry.JonesTransportMetric
