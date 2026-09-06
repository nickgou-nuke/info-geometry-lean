import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SusceptibilityHessian

/-! ## 1. Hessian response data -/

/--
Bregman/Fisher Hessian response datum.

`hessian U` is the local linear response metric at state `U`.
-/
structure HessianResponseDatum
    (State : Type*) [NormedAddCommGroup State] [NormedSpace ℝ State] where
  /-- Local Hessian/linear-response operator. -/
  hessian : State → State →L[ℝ] State

namespace HessianResponseDatum

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
variable (H : HessianResponseDatum State)

/-- A state is regular exactly when its Hessian response operator is bijective. -/
def regularAt
    (U : State) : Prop :=
  Function.Bijective (H.hessian U)

/-- Degeneracy is canonically the complement of the installed regular locus. -/
def singularAt
    (U : State) : Prop :=
  ¬ H.regularAt U

/-- The historical exclusion law is now definitional, not stored evidence. -/
theorem singular_not_regular
    (U : State) :
    H.singularAt U → ¬ H.regularAt U :=
  id

/-- Re-export of the abstract singular/regular exclusion law. -/
theorem not_regular_of_singular
    {U : State}
    (hU : H.singularAt U) :
    ¬ H.regularAt U :=
  hU

end HessianResponseDatum

/--
The Hessian degeneracy boundary.

This is the optical/material response boundary used by snap and singular
response modules.  It is just the named singular locus of the Hessian datum.
-/
def IsHessianDegenerate
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (H : HessianResponseDatum State)
    (U : State) : Prop :=
  H.singularAt U
