# Thermodynamic M-estimation

Owner: `lean/InfoGeometry/Spectrometry/ThermodynamicMEstimation.lean`.
Regression checks: `lean/InfoGeometry/Spectrometry/ThermodynamicMEstimationTests.lean`.

## Proof dependency order

The dependency order branches rather than asserting a physical causal chain:

```text
Gaussian squared-distance energy -> Frechet derivative --+
                                                        +-> stationary weighted center
Laplace distance energy -> regular-point derivative -----+
                                                        +-> Weiszfeld fixed point
two-state free energy -> logistic derivative ------------+
                          + inverse distance -> compound weights
                          + regular-point chain rule -> annealed stationarity
```

The native owners `GeometricMedianCore` and `AitchisonGeometricMedian` already
provide weighted centers, Laplace derivatives, thermal weights, and derivatives
of the actual annealed objective. They are reused, not duplicated. The new
module supplies Gaussian energy and its derivative, Gaussian and Laplace
stationarity equivalences, the explicit compound-weight formula, and a genuine
`HasFDerivAt ... 0` theorem at regular annealed fixed points.

## Hypotheses and limits

- Gaussian weights are fixed when differentiating. Their sum must be nonzero
  for the barycenter equivalence; signed weights are allowed algebraically.
- Laplace and annealed derivatives require the candidate to differ from every
  observation. A nonempty ensemble then has positive inverse-distance weight sum.
- The annealed derivative requires strictly positive temperature.
- A fixed-point equality is not convergence of an iteration. Stationarity is
  not a proof of global optimality or universal robustness.
- The singleton regression at observation `3` is a geometric median, but the
  unmodified, totalized Weiszfeld formula evaluates to `0` there. This documents
  why collision hypotheses cannot be dropped.
- These norm-based statistical objectives use a positive real inner product.
  They do not replace the repository's indefinite Krein metric or its adjoint.
- No PDF pages or their selected order are changed by this module.

## Validation environment

The pinned Lean 4.28.1 check stops in the imported Mathlib
`Analysis/InnerProductSpace/Calculus.olean` with `incompatible header`.
The available dependency cache is built with Lean 4.28.0. Isolated validation
uses that matching compiler, the shared build lock, and outputs under
`/tmp/isnp-metacompiler-validation`; this is not a pinned-version or full-repo
build claim. No dependency pins or toolchain files are changed.

The regression module audits six theorem axiom sets. Standard Mathlib axioms
(`propext`, `Classical.choice`, `Quot.sound`) are permitted; no `sorryAx` or new
axiom is introduced. These are full Lean proofs, not a claim of choice-free
constructive analysis.
