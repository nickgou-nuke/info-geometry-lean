import InfoGeometry.Canonical.IBTrajectory
import InfoGeometry.Canonical.IBFrozenDescent

/-!
# InfoGeometry.Canonical.IBFiniteIteration

Canonical one-step descent and iteration-level monotonicity consequences for
the finite Information Bottleneck dynamics.
-/

open scoped BigOperators ENNReal NNReal

set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace InfoGeometry.Canonical.IB

variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace T] [MeasurableSingletonClass T]

/--
Along the canonical BA trajectory, the frozen-target gap at step `n + 1`
relative to the step-`n` anchor vanishes exactly.
-/
theorem ibTrajectory_step_gap_eq_zero
    (prob : IBProblem (X := X) (Y := Y))
    (p0 : X → FinProb T) (n : Nat) :
    baFrozenTargetGap prob
      (ibTrajectory prob p0 n)
      (ibTrajectory prob p0 (n + 1)) = 0 := by
  simpa [ibTrajectory_succ] using
    (baFrozenTargetGap_step_eq_zero
      (X := X) (Y := Y) (T := T)
      (prob := prob)
      (pOld := ibTrajectory prob p0 n))

/--
Along the canonical BA trajectory, the one-step update minimizes the
frozen-target gap relative to the current anchor.
-/
theorem ibTrajectory_step_descent_frozenTarget
    (prob : IBProblem (X := X) (Y := Y))
    (p0 : X → FinProb T) (n : Nat) :
    baFrozenTargetGap prob
      (ibTrajectory prob p0 n)
      (ibTrajectory prob p0 (n + 1))
      ≤
    baFrozenTargetGap prob
      (ibTrajectory prob p0 n)
      (ibTrajectory prob p0 n) := by
  simpa [ibTrajectory_succ] using
    (ibBlahutArimotoStep_descent_frozenTarget
      (X := X) (Y := Y) (T := T)
      (prob := prob)
      (pOld := ibTrajectory prob p0 n))

/--
For a current encoder policy `p`, the canonical BA step decreases the frozen
variational functional built from the induced target marginal and projection of
`p`.
-/
theorem ibBlahutArimotoStep_variational_descent_currentTarget
    [DecidableEq T]
    (prob : IBProblem (X := X) (Y := Y))
    (p : X → FinProb T)
    (hq : ∀ t : T, 0 < ((inducedMarginalT prob p) t).toReal) :
    ibVariationalFunctionalFrozen prob
      (inducedMarginalT prob p)
      (inducedMProjection prob p)
      (ibBlahutArimotoStep prob p)
      ≤
    ibVariationalFunctionalFrozen prob
      (inducedMarginalT prob p)
      (inducedMProjection prob p)
      p := by
  simpa [ibBlahutArimotoStep_eq_frozen_induced] using
    (ibVariationalFunctional_frozen_descent
      (X := X) (Y := Y) (T := T)
      (prob := prob)
      (qT := inducedMarginalT prob p)
      (mY_givenT := inducedMProjection prob p)
      (hq := hq)
      (p := p))

/--
Iteration-level current-target variational descent along the canonical BA
trajectory.
-/
theorem ibTrajectory_variational_descent_currentTarget
    [DecidableEq T]
    (prob : IBProblem (X := X) (Y := Y))
    (p0 : X → FinProb T) (n : Nat)
    (hq : ∀ t : T, 0 < ((inducedMarginalT prob (ibTrajectory prob p0 n)) t).toReal) :
    ibVariationalFunctionalFrozen prob
      (inducedMarginalT prob (ibTrajectory prob p0 n))
      (inducedMProjection prob (ibTrajectory prob p0 n))
      (ibTrajectory prob p0 (n + 1))
      ≤
    ibVariationalFunctionalFrozen prob
      (inducedMarginalT prob (ibTrajectory prob p0 n))
      (inducedMProjection prob (ibTrajectory prob p0 n))
      (ibTrajectory prob p0 n) := by
  simpa [ibTrajectory_succ] using
    (ibBlahutArimotoStep_variational_descent_currentTarget
      (X := X) (Y := Y) (T := T)
      (prob := prob)
      (p := ibTrajectory prob p0 n)
      (hq := hq))

end InfoGeometry.Canonical.IB
