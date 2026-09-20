# Constrained quadratic contact

Owner: `lean/InfoGeometry/Synthesis/ConstrainedQuadraticContact.lean`.
Regression tests: `lean/InfoGeometry/Synthesis/ConstrainedQuadraticContactTests.lean`.

This module reuses `Synthesis.ImpedanceMatchingDuality` and restricts the
efficiency variable to `[0, 1]`. For a nonnegative coupling `k`, it proves:

| Coupling | Maximizing efficiency | Maximum of `k ε (1 - k ε)` | Minimum gap |
| --- | --- | --- | --- |
| `0 ≤ k ≤ 1/2` | `1` | `k (1 - k)` | `(k - 1/2)²` |
| `1/2 < k` | `1/(2k)` | `1/4` | `0` |

The gap compares this constrained maximum with the minimum of the explicitly
defined function `1/4 + τ²`. Native `IsGreatest` and `IsLeast` statements prove
attainment, not merely upper and lower estimates. `constrainedGap_zero_iff`
shows that the constrained gap vanishes exactly when `1/2 ≤ k`.

For example, at `k = 1/4` the unconstrained gap is zero, but the constrained
gap is `1/16`: the unconstrained vertex has efficiency `2`, outside `[0,1]`.
At `k = 0`, every efficiency maximizes the constant zero capacity; the displayed
optimizer is a chosen maximizer, not a claim of uniqueness.

These are quadratic optimization theorems. They do not establish a spectral
parameterization for an unspecified operator, the Selberg conjecture, or a
physical equivalence between variance, entropy, and Fisher information.
For a probability interpretation valid for every efficiency in `[0,1]`, one
must also restrict `k ≤ 1`; the polynomial optimization itself needs no such
upper bound.

The test module is imported by `InfoGeometry.AllExhaustive`. Focused Lean
verification does not certify that the entire repository builds.
