import Mathlib

/-!
QMS isolated proof targets for replacing two impossible Duhamel theorem sockets
in `InfoGeometry.Canonical.SouriauOperatorialLogPotential` with positive
first-order readback theorems.

Mathematical context:
- `Param` is the parameter carrier.
- `Op` is the operator/exponential carrier.
- `Direction` is the tangent/direction carrier.
- `D.derivativeOfExp β δ` is the directional derivative of the untraced
  operatorial exponential at `β` in direction `δ`.
- `D.higherSimplexOrderedForms 1 β [δ]` is the first ordered Duhamel/Kubo
  insertion form.
- `D.traceStateKMSReadout : Op → ℝ` is a scalar trace/state/KMS readout.
- The owner currently carries only the first Duhamel proof obligation
  `derivativeOfExp_eq_first_ordered_form`.

Valid propositions derivable from these premises:
1. the first ordered form equals the derivative, by symmetry of the supplied
   first-Duhamel law;
2. the scalar readout of the derivative equals the scalar readout of the first
   ordered form, by congruence through `traceStateKMSReadout`.

These are first-order readback theorems. They are not full higher-simplex,
trace-class, cumulant, or analytic Kubo/Duhamel closure.
-/

namespace InfoGeometry.QMS.SouriauOperatorialLogPotentialDuhamelReadouts

structure DuhamelOperatorDerivative (Param Op Direction : Type*) where
  K : Param → Op
  directionToInsertion : Direction → Op
  derivativeOfExp : Param → Direction → Op
  higherSimplexOrderedForms : Nat → Param → List Direction → Op
  traceStateKMSReadout : Op → ℝ
  derivativeOfExp_eq_first_ordered_form :
    ∀ β δ, derivativeOfExp β δ = higherSimplexOrderedForms 1 β [δ]

/--
The first ordered Duhamel form is the directional derivative, read back from the
explicit first-Duhamel proof obligation.
-/
theorem firstOrderedForm_eq_derivativeOfExp
    {Param Op Direction : Type*}
    (D : DuhamelOperatorDerivative Param Op Direction)
    (β : Param) (δ : Direction) :
    D.higherSimplexOrderedForms 1 β [δ] = D.derivativeOfExp β δ := by
  exact (D.derivativeOfExp_eq_first_ordered_form β δ).symm

/--
Applying the scalar trace/state/KMS readout to the first Duhamel law preserves
the equality of the derivative and the first ordered form.
-/
theorem traceStateKMSReadout_derivative_eq_firstOrderedForm
    {Param Op Direction : Type*}
    (D : DuhamelOperatorDerivative Param Op Direction)
    (β : Param) (δ : Direction) :
    D.traceStateKMSReadout (D.derivativeOfExp β δ) =
      D.traceStateKMSReadout (D.higherSimplexOrderedForms 1 β [δ]) := by
  exact congrArg D.traceStateKMSReadout (D.derivativeOfExp_eq_first_ordered_form β δ)

end InfoGeometry.QMS.SouriauOperatorialLogPotentialDuhamelReadouts
