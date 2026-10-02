# Bernoulli Legendre duality and the normalized detector response

## Mathematical scope

This specialization uses the existing real Bernoulli owners, not a new
exponential-family implementation:

- `Canonical.AmariBinarySimplexBridge` owns `massieu`, `logistic`, `logit`,
  `negativeEntropy`, `fisherExp`, and `fisherMix`.
- `Analysis.LogOddsSimplexGeometry` supplies the actual chart derivatives.
- `Probability.SimplexQuadraticResponse.response` supplies the quadratic
  response specialized to linear coefficient one.
- `Prequantum.JaynesKLPotential` supplies positive-weight KL nonnegativity.

`Detector.AmariLegendreCore` proves that the Fenchel gap equals the sum of
two generalized KL terms. Consequently negative entropy is the attained
Legendre supremum over all real natural parameters, for each probability
strictly between zero and one. Both potentials have actual Mathlib second
derivatives, with reciprocal Hessians at corresponding coordinates.
Both potentials are proved strictly convex on their respective open charts
(all real natural parameters and probabilities strictly between zero and one).
The natural-coordinate Hessian also equals the expected squared score of
the two Bernoulli outcomes, using derivatives of their log probabilities.

`Detector.AmariHessianDuality` sets `probability = coefficient * efficiency`.
Its statistical chart identities explicitly require `0 < probability < 1`.
It proves the exponential odds identity, log-partition survival identity,
expectation coordinate, and

```text
deriv (deriv massieu) (logit (coefficient * efficiency))
  = coefficient * normalizedSingles(coefficient, efficiency).
```

The coefficient has a global upper bound of one quarter. On the open chart,
equality holds exactly at probability one half. For nonzero coefficient,
efficiency `1 / (2 * coefficient)` attains this value. A positive coefficient
is additionally needed to interpret that efficiency as physically positive.

## Coordinate and model boundaries

This is a Bernoulli model. Log odds is not the natural parameter of a Poisson
family, and the two families are not identified.

The identity concerns a specified normalized response and the Fisher metric
coefficient in the natural parameter. It does not identify arbitrary measured
count rates with a coordinate-invariant scalar amount of information. The
proved efficiency-coordinate pullback instead equals

```text
coefficient^2 / (probability * (1 - probability)).
```

At the endpoint probability one, the normalized response vanishes, but the
finite natural-coordinate chart no longer applies. No finite natural parameter
has logistic value one. Lean's total real logarithm and division assign values
even outside the statistical domain: the regression test explicitly exhibits
a positive totalized `fisher_metric` at the endpoint where singles vanish.
Dropping the open-domain hypothesis would therefore invalidate the singles
identity. No boundary-information-loss theorem is inferred.

No condensate interpretation, detector likelihood fit, Apollonian realization,
Carnot power law, or physical evolution is asserted by these algebraic and
differential identities.

## Declared dependency poset

`Detector.AmariHessianDependency` is a finite declared dependency model with
a native `PartialOrder`, not an extractor of Lean's implementation graph:

```text
logPartition → expectationDerivative → fisherHessian
oddsCoordinate, logPartition → legendreConjugate
oddsCoordinate, fisherHessian, singlesResponse → singlesMetricIdentity
oddsCoordinate, fisherHessian → efficiencyPullback
varianceBound
```

The two coordinate readouts are incomparable in this model. The variance
bound is elementary algebra, not a consequence of thermodynamic dynamics.

## Verification

The regression and axiom-audit entrypoint is
`InfoGeometry.Detector.AmariHessianDualityTests`. All four detector modules,
seven regression examples, and thirty axiom audits pass serial shared-lock
validation with installed Lean 4.28.x and cached Mathlib. The audits contain
only subsets of `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx` or added axioms.

The pinned Lean 4.28.1 toolchain is not installed. This is a targeted
compatibility check, not a full pinned-toolchain repository build. No dependency
metadata or toolchain pin was changed. Required existing Bernoulli and chart
owners were compiled as part of the check; their existing warnings were left
untouched.
