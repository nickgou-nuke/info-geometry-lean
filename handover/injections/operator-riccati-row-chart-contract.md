# Ground-truth contract: ordered operator Riccati row-chart tangent

## Claim

For a unital associative ring `B`, the right action of an operator matrix
`[[a,b],[c,d]]` on the row `[1,T]` has first-order components
`a + T*c` and `b + T*d`. The induced affine-chart tangent is
`b + T*d - a*T - T*c*T`. This polynomial is natural under ring homomorphisms.
Its translation, spin-dilation, and conformal specializations hold with all
operator products in the stated order.

## Carrier and convention

The coefficient carrier is arbitrary `[Ring B]`; the matrix carrier is
`Matrix (Fin 2) (Fin 2) B`. Rows act on the right. The chart is the ordered
ratio `X⁻¹Y` in the usual invertible chart, but the theorem itself is
division-free and states the tangent compatibility equation
`(a + T*c)*T + velocity = b + T*d`.

## Existing owners and exact evidence

* `OperatorAlgebra/OperatorMobiusAction.lean` owns the operator matrix carrier,
  denominator-free column action, and its composition and ring-map laws.
* `OperatorAlgebra/ThermodynamicSL2OperatorLift.lean` owns
  `operatorRiccatiVelocity d b c z := b + d*z + z*d - z*c*z` for its
  trace-patterned column-action generator. It does not state the general
  row-chart formula with four independently ordered operator coefficients.
* The archived AI Studio transcript at
  `cached/aistudio_extracts/aistudio_prompt_1xHyRdU-TU8mjwZzKRRrzTAdvk8nPm7Or/transcript.md`
  states `b + T*d - a*T - T*c*T`; its commutative scalar specialization is
  not used as proof evidence.

## Smallest gap

Add a focused row-action owner proving the two row components, their ordered
Riccati tangent identity, its ring-hom naturality, and the three exact channel
specializations. No quotient/inverse, analytic flow, or scalar model is needed
for these polynomial identities.

## Explicit boundary

The result is an infinitesimal algebraic tangent law, not a theorem about
existence or differentiability of the finite fractional transform for
noninvertible operator denominators. It does not identify row and column
action conventions or claim scalar dilation `-2θT` for noncommuting `θ,T`.
