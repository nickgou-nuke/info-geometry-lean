import InfoGeometry.Canonical.IBCore

namespace InfoGeometry.Canonical.IB.Sandbox

variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq T]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace T] [MeasurableSingletonClass T]

open scoped BigOperators ENNReal NNReal

theorem ibVariationalFunctional_frozen_descent_internal_bridge
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (p : X → FinProb T)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (C : ℝ)
    (hStepDecomp :
      ibVariationalFunctional prob (ibBlahutArimotoStepFrozen (X := X) (Y := Y) (T := T) prob qT mY_givenT) mY_givenT
        = C + ibVariationalFunctionalFrozen prob qT mY_givenT
            (ibBlahutArimotoStepFrozen (X := X) (Y := Y) (T := T) prob qT mY_givenT))
    (hPDecomp :
      ibVariationalFunctional prob p mY_givenT
        = C + ibVariationalFunctionalFrozen prob qT mY_givenT p) :
    ibVariationalFunctional prob (ibBlahutArimotoStepFrozen (X := X) (Y := Y) (T := T) prob qT mY_givenT) mY_givenT
    ≤ ibVariationalFunctional prob p mY_givenT := by
  rw [hStepDecomp, hPDecomp]
  have h_descent := ibVariationalFunctional_frozen_descent prob qT mY_givenT hq p
  linarith

end InfoGeometry.Canonical.IB.Sandbox
