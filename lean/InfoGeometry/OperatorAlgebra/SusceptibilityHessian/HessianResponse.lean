import Mathlib

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

  /-- Regularity/invertibility region. -/
  regularAt : State → Prop

  /-- Degeneracy/snap boundary. -/
  singularAt : State → Prop

  /-- Singular means not regular at this abstract layer. -/
  singular_not_regular :
    ∀ U : State, singularAt U → ¬ regularAt U

namespace HessianResponseDatum

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
variable (H : HessianResponseDatum State)

/-- Re-export of the abstract singular/regular exclusion law. -/
theorem not_regular_of_singular
    {U : State}
    (hU : H.singularAt U) :
    ¬ H.regularAt U :=
  H.singular_not_regular U hU

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
