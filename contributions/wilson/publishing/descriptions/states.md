## Why

Analytic renormalization estimates often give summable errors between adjacent
finite-scale functionals. An exact compatible state family requires proving
that the resulting limits retain positivity, complex linearity, normalization,
and the refinement law. Pointwise convergence of arbitrary real functions
does not establish those state properties.

## Changes

Add a reusable native Mathlib construction in two layers:

- For norm-contracting refinement maps and complete metric outputs, summable
  one-step errors give pointwise limits, exact adjacent compatibility, and a
  quantitative tail estimate at every finite refinement horizon.
- For possibly noncommutative complex C-star algebras, normalized native
  positive linear maps and unital star-algebra homomorphisms, construct native
  positive linear limit functionals. Derive transition contractivity from
  Mathlib and prove linearity, positivity, normalization and compatibility.

The assumptions remain explicit:

\[
\|\omega_{n+1}(\iota_n a)-\omega_n(a)\|
\le \varepsilon_n\|a\|,\qquad
\varepsilon_n\ge0,\qquad \sum_n\varepsilon_n<\infty.
\]

The limit family satisfies

\[
\omega^\infty_{n+1}(\iota_n a)=\omega^\infty_n(a),
\qquad
\|\omega^\infty_n(a)-\omega_{n+k}(\iota_{n,n+k}a)\|
\le \Bigl(\sum_{j=0}^\infty\varepsilon_{n+k+j}\Bigr)\|a\|.
\]

The portable modules import only Mathlib and one another. A separate adapter
in the source project supplies its existing `CompatibleStateFamily`; that
InfoGeometry-specific adapter is not included in this upstream patch.

## Validation

The exact destination Lean 4.36.0 / Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842` check passed in
[run 45571203500](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45571203500),
job `139058006920`, at preparation snapshot
`ff8e1632b45569d88da1c73c0ec160c913fe55f9`. The warnings-as-errors build and fresh
audit passed for all ten public theorems and the exported recursive evaluation
definition, for eleven reports. SHA-256 comparison matches the checked Lean
sources to this patch. The three portable modules also passed a separate
Lean 4.34.1 check in the source project.

```sh
lake exe cache get
lake --wfail build CoreLean.ApproximateStateLimitsAudit
lake env lean CoreLean/ApproximateStateLimitsAudit.lean
```

The workflow preserves the checked-in toolchain and dependency configuration,
requires only `propext`, `Classical.choice`, and `Quot.sound` in the fresh audit,
and archives its source and compiler evidence.

## Scope

The uniform error estimate must hold for every observable in each stage
algebra. The project must supply that estimate and the actual observable
algebras/refinement homomorphisms. General Markov averaging maps are not
substituted for multiplicative star-algebra maps. This contribution does not
derive the model-specific RG bounds or a physical continuum theorem.
