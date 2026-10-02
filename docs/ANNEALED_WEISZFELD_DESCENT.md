# Annealed Weiszfeld majorization and descent

## Mathematical target

This development uses the existing `AitchisonGeometricMedian.annealedObjective`
and `annealedStep`, without replacing the objective by its quadratic surrogate.
For fixed positive temperature, the scalar loss is

\[
f_T(r)=-T\log(e^{-r/T}+e^{-c/T}),\qquad
f_T'(r)=w_T(r)=\frac1{1+e^{(r-c)/T}}.
\]

The existing fluctuation owner establishes strict concavity of this scalar loss.
Thus its tangent line is an upper bound, not a lower bound. This is a softminimum;
the argument does not assert that an ordinary convex softplus has this property.

For an anchor `a` distinct from every observation, let

\[
W_i(a)=\frac{w_T(\|a-z_i\|)}{\|a-z_i\|},\qquad
Q(x,a)=F(a)+\frac12\sum_iW_i(a)
  (\|x-z_i\|^2-\|a-z_i\|^2).
\]

The anchor-dependent constants are essential: `Q(a,a) = F(a)`.
The factor `1/2` belongs to the quadratic surrogate; multiplying every weight by
this common factor does not alter the normalized barycenter already implemented
by `annealedStep`.

## Proof owners

- `WeightedQuadraticDescent.lean`: weighted-center score cancellation, Huygens'
  completed-square identity, and global quadratic minimality.
- `ThermalFreeEnergyMajorization.lean`: the concave tangent bound and its
  positive-anchor quadratic upper bound.
- `AnnealedDescentLemma.lean`: touching, majorization, surrogate minimality,
  quantitative descent, strict decrease away from a fixed point, and antitonicity
  of objective values along regular fixed-temperature iterates.
- `AnnealedEnergyConvergence.lean`: a uniform lower bound from `f_T(0)` and
  convergence of the objective values to their infimum.
- `AnnealedDescentDependency.lean`: native finite partial order with separate
  majorization, quadratic-minimization, and lower-bound branches.
- `AnnealedDescentTests.lean`: concrete quadratic and single-observation examples,
  a regular anchor whose next iterate collides with the observation, and eleven
  axiom audits.

All listed Lean paths are under `lean/InfoGeometry/Spectrometry/`.

## Exact scope

The intended quantitative inequality is

\[
F(a_{next})+\frac{\sum_i W_i(a)}2\|a-a_{next}\|^2\le F(a).
\]

The positive-mass results require a nonempty finite observation type. A single
descent step requires only the current anchor to be regular: the candidate may
coincide with an observation. Iterated descent and energy convergence explicitly
require regularity at every anchor. The single-observation regression shows why
this cannot be inferred from initial regularity alone.

Energy convergence does not establish convergence of the parameter sequence,
global optimality, physical phase transitions, or monotonicity when the
temperature changes between steps. Those assertions are not included.

## Verification status

The full regression target **passes Lean 4.28.1**. Its pinned source dependency
closure contains 3,168 modules, checked sequentially under the shared build lock.
All six owners elaborate successfully after repairing the explicit real inner
product notation and two additive-inequality steps. The final regression run
reports eleven axiom audits: only `propext`, `Classical.choice`, and `Quot.sound`
occur; there is no `sorryAx` or added axiom. The dependency-order audit uses only
`propext` and `Quot.sound`. These are classical Mathlib proofs, not a claim of
choice-free constructive analysis.

The successful command was:

```bash
python3 /tmp/isnp-rebuild-pinned.py InfoGeometry.Spectrometry.AnnealedDescentTests
```

The temporary checker validates dependency revisions against `lake-manifest.json`
and compiles exact pinned sources into `/tmp/isnp-rebuilt-4.28.1`, without loading
Lean 4.28.1 artifacts or changing dependency pins. This verifies this regression
target and its dependencies, not the entire repository or the stronger physical
and convergence claims excluded above. Any elaboration failures in the new
scripts must be repaired before this status is promoted to verified.
