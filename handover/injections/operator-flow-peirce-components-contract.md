# Ground-Truth Contract: Operator Flow on Peirce Components

## Claim

For a complete real normed algebra `A` and a continuous linear derivation
`D : A →L[ℝ] A`, the exponential flow `φₜ = exp(tD)` maps each of the four
associative Peirce formulas for `(P, X)` to the corresponding formula for
`(φₜ(P), φₜ(X))`.

## Carrier and conventions

The carrier is the existing normed operator algebra `A`; multiplication is
its native possibly noncommutative ring multiplication. The complement is
`1 - P`. The four formulas are the existing
`InfoGeometry.Core.PeirceDecomposition.component11/10/01/00`. No idempotency
assumption is needed for the formula-transport equality. Idempotency is
needed to interpret the four expressions as orthogonal Peirce sectors.

## Owner evidence

- `lean/InfoGeometry/Optics/OperatorDerivationForms.lean` defines
  `FrechetOperatorDerivation` with its continuous Leibniz law and proves
  `FrechetOperatorDerivation.flow_mul` using the generic flow theorem.
- `lean/InfoGeometry/Lie/ContinuousDerivationExponential.lean` proves
  `flow_map_mul` and `flow_apply_eq_self_of_apply_eq_zero`.
- `lean/InfoGeometry/Core/PeirceDecomposition.lean` defines the four
  components from `P`, `1-P`, and `X`.
- The same Optics owner already proves transport of Tetraktys components and
  CE spin curvature; those statements do not themselves give all four
  Peirce-coordinate transport equations.

## Smallest gap and theorem

The missing bridge is `flow_transports_peirce_components` in
`OperatorDerivationForms.lean`. It follows from multiplicativity, preservation
of the unit, and linearity of the flow, applied in the exact noncommutative
factor order of each Peirce formula.

## Claims excluded

This theorem alone does not prove a Riccati equation, identify a physical
curvature or mass, classify Möbius transformations, or pass to an infinite
tensor/direct-limit carrier. Those require their own existing owners and
explicit compatibility theorems.

## Follow-up bridge: infinitesimal spin transport

The same Optics owner proves both that `genSig` is transported by the
exponential flow (`flow_transports_peirce_tetraktys`) and that a flow orbit
has derivative `D (flow D t x)` (`ContinuousDerivationExponential.hasStrictDerivAt_orbit`).
The additional theorem `hasStrictDerivAt_flow_peirce_spin` composes these exact
statements. Its derivative is the native operator `D (φₜ (genSig P a c))`;
it does not claim a scalar Riccati law or an analytic classification result.
