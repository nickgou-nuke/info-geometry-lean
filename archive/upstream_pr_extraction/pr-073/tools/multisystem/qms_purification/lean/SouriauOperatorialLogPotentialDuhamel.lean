import Mathlib

/-!
QMS isolated proof target for purifying
`InfoGeometry.Canonical.SouriauOperatorialLogPotential.duhamelFormulaClaim`.

Mathematical context:
- `Param` is the parameter carrier.
- `Op` is the operator/exponential carrier.
- `Direction` is the tangent/direction carrier.
- `D.derivativeOfExp β δ` denotes the directional derivative of the untraced
  operatorial exponential family at parameter `β` in direction `δ`.
- `D.higherSimplexOrderedForms n β directions` denotes the ordered Duhamel/Kubo
  `n`-simplex operator form.
- The classical Duhamel formula states that the first directional derivative of
  an operator exponential is represented by the first ordered insertion/simplex
  form. In this abstract owner file there is no analytic semigroup, integral,
  differentiability, Banach/operator topology, or functional calculus from which
  to derive that formula.

QMS purification move:
- Do not prove the Duhamel formula from arbitrary fields.
- Store the Duhamel first-variation law as an explicit proof obligation field.
- Prove the public theorem as a field readback.

Existing mathlib/literature context:
- The algebraic proof below uses only projection from a structure field; no
  mathlib analytic Duhamel theorem is invoked.
- The analytic Duhamel formula belongs to operator semigroup/functional-calculus
  literature; formalizing that route would require additional hypotheses not
  present in this owner surface.
-/

namespace InfoGeometry.QMS.SouriauOperatorialLogPotentialDuhamel

structure DuhamelOperatorDerivative (Param Op Direction : Type*) where
  K : Param → Op
  directionToInsertion : Direction → Op
  derivativeOfExp : Param → Direction → Op
  higherSimplexOrderedForms : Nat → Param → List Direction → Op
  traceStateKMSReadout : Op → ℝ
  derivativeOfExp_eq_first_ordered_form :
    ∀ β δ, derivativeOfExp β δ = higherSimplexOrderedForms 1 β [δ]

/--
The first Duhamel derivative formula is a theorem-honest readback from the
explicit first-variation proof obligation carried by `DuhamelOperatorDerivative`.
-/
theorem duhamelFormula_from_field
    {Param Op Direction : Type*}
    (D : DuhamelOperatorDerivative Param Op Direction)
    (β : Param) (δ : Direction) :
    D.derivativeOfExp β δ = D.higherSimplexOrderedForms 1 β [δ] := by
  exact D.derivativeOfExp_eq_first_ordered_form β δ

end InfoGeometry.QMS.SouriauOperatorialLogPotentialDuhamel
