import InfoGeometry.Canonical.IBCore

/-!
# InfoGeometry.Unstable.IBSurrogates

Legacy unstable compatibility layer around the canonical finite
Information Bottleneck Blahut-Arimoto step.
These names are kept for local experimentation and now route directly
through the proved canonical IB dynamics.
-/

namespace InfoGeometry.Unstable.IBSurrogates

open scoped BigOperators ENNReal NNReal
open InfoGeometry.Canonical.IB

variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace T] [MeasurableSingletonClass T]

/-- Legacy unstable name for the canonical one-step BA update. -/
noncomputable def ibIteration
    (prob : IBProblem (X := X) (Y := Y)) :
    (X → InfoGeometry.FinProb T) → (X → InfoGeometry.FinProb T) :=
  ibBlahutArimotoStep prob

/-- Fixed-point marker for the canonical BA step under the legacy unstable name. -/
def ib_fixedPoint
    (prob : IBProblem (X := X) (Y := Y))
    (p : X → InfoGeometry.FinProb T) : Prop :=
  ibIteration prob p = p

/-- Legacy unstable one-step descent wrapper for the canonical frozen-target gap theorem. -/
theorem ib_iteration_descent
    (prob : IBProblem (X := X) (Y := Y))
    (pOld : X → InfoGeometry.FinProb T) :
    baFrozenTargetGap prob pOld (ibIteration prob pOld) ≤
      baFrozenTargetGap prob pOld pOld := by
  simpa [ibIteration] using
    (ibBlahutArimotoStep_descent_frozenTarget
      (X := X) (Y := Y) (T := T) (prob := prob) (pOld := pOld))

end InfoGeometry.Unstable.IBSurrogates
