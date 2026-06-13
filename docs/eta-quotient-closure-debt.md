# Eta quotient closure debt for `RiemannZetaEquivalences`

This note records the current native-closure status of the eta quotient corridor in
`lean/InfoGeometry/Arithmetic/RiemannZetaEquivalences.lean`.

## Current live Lean surface

In
`lean/InfoGeometry/Arithmetic/RiemannZetaEquivalences.lean`
we currently have:

- native closed theorems:
  - `symmetryAdaptedXi_is_even`
  - `eulerProductZeta_eq_riemannZeta`
  - `dirichletSeriesZeta_eq_riemannZeta`
- certificate-gated analytic target:
  - `DirichletEtaQuotientTarget`
  - `DirichletEtaQuotientCertificate`
  - `dirichletEta_eq_riemannZeta_of_certificate`

The target is:

`0 < s.re → s ≠ 1 → riemannZeta s = (1 - 2 ^ (1 - s))⁻¹ * dirichletEta s`

with

`dirichletEta s = ∑' n : ℕ, ((-1 : ℂ) ^ n) / ((n + 1 : ℕ) : ℂ) ^ s`.

## Search result

I searched:

- the repository under `lean/InfoGeometry/**`
- mathlib under `.lake/packages/mathlib/Mathlib/NumberTheory/**`

for a native theorem directly closing the eta quotient identity, including searches for:

- `dirichlet_eta`
- `dirichletEta`
- `eta quotient`
- `riemannZeta.*eta`
- `eta.*riemannZeta`
- `1 - 2 ^ (1 - s)`

Result:
- no direct theorem was found in the current repo or mathlib surface that states the eta quotient identity in the exact required form.
- the live native closures found are only the right-half-plane Euler product / Dirichlet-series zeta theorems.

## Likely owner corridors for future native closure

The most relevant mathlib corridors appear to be:

- `Mathlib/NumberTheory/LSeries/HurwitzZeta.lean`
- `Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean`
- `Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean`

These provide meromorphic continuation / completed-function infrastructure for related zeta-series objects, but not an already-named direct eta-quotient theorem surfaced in the present search.

## Honest status

As of this audit:

- the eta quotient is numerically witnessed by
  `tools/sympy/riemann_zeta_equivalences_verify.py`
- the Lean side keeps the statement as explicit open analytic closure debt
- there is no fake native theorem and no `sorry` in the current file

## Recommended next closure path

If native closure is required, the next real task is not to invent a wrapper theorem, but to derive the eta quotient identity from mathlib's existing analytic continuation / L-series infrastructure, most likely by:

1. identifying the exact analytic owner object corresponding to the alternating series,
2. proving it matches the positive-index definition used in `dirichletEta`,
3. transporting the continuation identity into the exact target form
   `riemannZeta s = (1 - 2 ^ (1 - s))⁻¹ * dirichletEta s`.

Until that derivation exists, the certificate-gated Lean surface is the correct honest boundary.
