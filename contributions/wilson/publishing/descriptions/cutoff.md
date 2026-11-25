## Why

Section 11 of the continuum-limit manuscript combines weighted positive
recursion estimates, comparison of normalized observables, and summability
of cutoff errors. These steps can be exposed as reusable Lean lemmas while
keeping the target-specific RG estimates explicit.

## Changes

The contribution provides four connected analytic components:

- An exact complex ratio identity and a relative-error estimate for `N/Z`,
  retaining the old positive partition function in the denominator. A
  separate exponential multiplication estimate handles bounded changes in
  normalization factors.
- A finite weighted maximum argument for operators monotone and positively
  homogeneous on the nonnegative cone. From `u ≤ T u + s`, `T w ≤ θ w`,
  `s ≤ C w`, positive weights, and `θ < 1`, it derives
  `u i ≤ C / (1 - θ) * w i`. The matrix corollary derives the operator
  properties from nonnegative entries and explicit weighted row sums.
- Power-log summability for every **nonnegative real logarithmic exponent**:
  `K^a * log(b*K+c)^p` is summable when `a < -1`, `b > 0`, `c ≥ 0`, and
  `p ≥ 0`. This covers the manuscript's `p = 4*r + 2*p₀` without assuming
  `p₀` is integral, including the additional factor of `K` in the final
  cutoff estimate when `κ ≥ 13`.
- A consumer that combines that derived summability with explicit relative
  numerator/partition-function comparisons. It proves convergence of the
  full normalized sequence and the quantitative tail bound

\[
\left|N_{K_0+k}/Z_{K_0+k}-L\right|
\le (C_N+B C_Z)\sum_{j=0}^{\infty}e_{K_0+k+j}.
\]

All owners use focused native Mathlib imports. The accompanying README states
the actual carriers, hypotheses, endpoint, and manuscript correspondence.

## Validation

**Current verification:** exact destination Lean 4.36.0 passed in [run 45571203500](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45571203500), job `139058006434`, at preparation source `ff8e1632b45569d88da1c73c0ec160c913fe55f9` against upstream `c25e77e9654a54fc5e4a04bfb637b7144defacc0`. The warnings-as-errors build, 16 fresh axiom reports, source-hash comparison and unchanged dependency-pin checks all passed. The current Lean files match that successful source inventory.

The patch includes a focused workflow and all-public-theorem axiom audit.
From `LEAN/CoreLean`:

```sh
lake exe cache get
lake --wfail build CoreLean.CutoffCheck
lake env lean CoreLean/CutoffCheck.lean
```

The workflow checks the exact fresh axiom inventory, preserves the existing
Lean/Mathlib configuration, and archives its logs. Coverage is the new owners
and their transitive imports. Compiler results and checked source hashes are
recorded separately in the contribution's validation evidence.

## Scope

The physical weighted bounds on `T`, relative cutoff estimates, positivity of
partition functions, uniform observable bounds, and remaining insertion or
geometric error terms still need to be supplied by the Wilson-loop
construction. This contribution proves the generic analytic implications
and the stated remainder summability; it does not claim the manuscript's
full continuum theorem.
