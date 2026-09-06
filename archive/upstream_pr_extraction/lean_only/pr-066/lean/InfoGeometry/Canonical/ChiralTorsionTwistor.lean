import InfoGeometry.Convex.ProjectiveRays
import InfoGeometry.Twistor.NullProjective

namespace InfoGeometry.Canonical.ChiralTorsionBridge

open InfoGeometry.Convex
open InfoGeometry.Twistor
open InfoGeometry.Krein

section ProjectiveTwistor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Unnormalized representative of a projective knowledge ray. -/
abbrev UnnormalizedProjectiveState := NonzeroDoubledState (E := E)

/-- Vacuum-apex null condition on a nonzero doubled representative. -/
def IsVacuumApexNull
    (Q : QuadraticForm ℝ (DoubledSpace E))
    (v : UnnormalizedProjectiveState (E := E)) : Prop :=
  Q v.1 = 0

/-- A null unnormalized representative defines a canonical twistor point. -/
noncomputable def vacuumApexTwistor
    (Q : QuadraticForm ℝ (DoubledSpace E))
    (v : UnnormalizedProjectiveState (E := E))
    (hNull : IsVacuumApexNull Q v) :
    DoubledTwistorSpace Q :=
  doubledTwistorMk Q v.1 v.2 hNull

end ProjectiveTwistor

end InfoGeometry.Canonical.ChiralTorsionBridge
