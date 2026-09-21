# Scalar statistical identities: scope and verification

The owner is `lean/InfoGeometry/ScalarStatisticalIdentities.lean`. It contains
scalar algebra and real-function identities extracted from the supplied text,
not a derivation of spacetime or a limit theorem for probability measures.

## Implemented statements

- Exponential separation is positive for positive initial separation. Strict
  increase additionally requires a positive rate; positivity alone is not chaos.
- Odds and inverse odds are mutually inverse away from their respective poles.
  Positive odds correspond to probabilities in the open unit interval.
- Nonnegative scaling of square-root odds agrees with squared scaling of odds.
- An assumed inverse information/variance relation survives reciprocal sample
  scaling for nonzero sample count. This does not assert equality in a general
  Cramer–Rao inequality.
- Assuming equal scalar moments gives a Fano ratio of one when the mean is
  nonzero and the square-root relative-fluctuation identity. A pair of equal
  numbers is not a construction or characterization of a Poisson distribution.
- The inverse-square-root scale has an exact multiplication law and is
  nonincreasing on positive sample counts for nonnegative coefficient.
- A squared-radius constraint of radius zero forces equality of its center and
  estimate. This is not a convergence theorem about moving centers.
- Scaling value, mean, and variance all linearly scales the standardized
  coordinate by the square root of the scale; it does not preserve it.
  Scaling value and mean linearly and variance quadratically does preserve it.

Mathlib owns exponential monotonicity, square-root identities, cancellation,
and order transport. The unbundled odds formulas here are scalar coordinates;
they introduce no replacement for the existing split-quaternion, binary-simplex,
or categorical owners.

## Dependency poset

`ScalarStatisticalIdentitiesDependencies.lean` uses the native finite-set
inclusion order, pulled back along an injective prerequisite map. The independent
branches are probability → odds, information → reciprocal variance, equal
moments → relative fluctuation, and standardization → scaling identity.
The exponential branch remains separate. This is an explicit mathematical
dependency model, not a causal model of physical experiments or an automatically
extracted declaration graph.

No central limit theorem, law of large numbers, Gaussian distribution,
self-concordant barrier, Cauchy convergence, categorical colimit, or physical
identification is established by these scalar statements. Such claims require
separate objects, hypotheses, and proofs. No `sorry`, new axiom, or `True`
placeholder is used.

## Regression checks

`ScalarStatisticalIdentitiesTests.lean` checks inverse-map poles, zero sample
count, zero variance, negative exponential rate, the two distinct scaling laws,
and incomparable dependency branches. It also prints theorem axiom dependencies.
The existing Lake library glob discovers these modules without a configuration
or pinned-dependency change.

Run only after inspecting compiler processes, using the shared build lock:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.ScalarStatisticalIdentitiesTests
```

Source implementation is not a claim of successful kernel checking: the
targeted build must finish successfully before reporting these files verified.
