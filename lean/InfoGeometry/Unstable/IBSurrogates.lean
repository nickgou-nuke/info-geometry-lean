import InfoGeometry.Canonical.IBCore

/-!
# InfoGeometry.Unstable.IBSurrogates

Isolated placeholder layer for Information Bottleneck iteration.
These definitions are explicitly unstable and must not be used by canonical proofs.
-/

namespace InfoGeometry.Unstable.IBSurrogates

open scoped BigOperators ENNReal NNReal
open InfoGeometry.Canonical.IB

variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T]

/-- BA iteration placeholder (identity map). -/
noncomputable def ibIteration
    (_prob : IBProblem (X := X) (Y := Y)) :
    (X → InfoGeometry.FinProb T) → (X → InfoGeometry.FinProb T) :=
  fun p => p

/-- Fixed-point marker for the unstable BA placeholder. -/
def ib_fixedPoint
    (prob : IBProblem (X := X) (Y := Y))
    (p : X → InfoGeometry.FinProb T) : Prop :=
  ibIteration prob p = p

/-- One-step descent for the unstable BA placeholder. -/
theorem ib_iteration_descent
    (prob : IBProblem (X := X) (Y := Y))
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace T] [MeasurableSingletonClass T]
    (pOld : X → InfoGeometry.FinProb T) :
    ibLagrangian prob (ibIteration prob pOld) ≤ ibLagrangian prob pOld := by
  simp [ibIteration]

end InfoGeometry.Unstable.IBSurrogates
