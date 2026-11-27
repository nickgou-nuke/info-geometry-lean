# GRH compatibility integration

## Intent and provenance

Implement the source-backed compatibility analysis requested on 2026-11-27 and
publish it for review against `nickgou-nuke/info-geometry-lean/main`.

Base: `fe24e350b08fdea04f74c0748ef9fd9417c47529`.
External proof: `lsernau/grh-lean`, readable `grh/` edition, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
Recovered arithmetic prerequisites: PR #423, commit
`ae5416753b33f221b438b63b3ea0f072f51b475a`.

The root Lean 4.34.1 / Mathlib pins are retained. The optional
`integrations/grh` project uses the external proof's Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` pins, compiling selected canonical
InfoGeometry sources under that toolchain. It imports the external proof as a
dependency; it does not replace that proof by an assumed field.

## Mathematical contract

| Layer | Carrier and construction | Required result |
|---|---|---|
| Native half-plane interface | Actual Mathlib Dirichlet characters and L-functions | The external `New.grh` supplies the existing `DirichletRightHalfPlaneNonvanishing`; the existing reduction yields native `RiemannHypothesis` |
| Weighted smoothing | Arbitrary real coefficients on positive integer cutoffs | Exact affine interpolation, logarithmic centering error, and `G(x) / x = R(x)` for nonzero cutoffs |
| Growth transfer | Real eventual upper bounds with fixed sign and explicit constants | Integer/real transfer and exponent shift by one under stated positivity conditions |
| Concrete external remainder | `New.lambdaKResidueClass`, `New.logDerivMean`, `New.primeRemainder` | Exact identification of the native weighted statistic with the imported remainder; application of the imported arithmetic estimate |
| Mellin boundary | Actual Bochner integrals and the imported remainder transform | Preserve the factor of `x`, integration domain, convergence hypotheses, and logarithmic centering |
| Real arithmetic readout | `DoubledSpace E` and real operators `a·1 + b·clockAxis` | Faithful zero detection for nontrivial real `E`, modular conjugation, and actual Dirichlet/zeta zero-location consequences |
| Centered completed zeta | Existing actual centered-xi owner | Critical-strip conclusions with endpoint exclusions retained |

The real operator readout is a faithful value representation. It is not a
construction of a Hilbert–Pólya spectral operator. The source of the arithmetic
zero exclusion in the optional integration is the pinned external GRH proof.
The canonical modules retain explicit analytic hypotheses where they do not
import that proof. No estimate is inferred from adaptive normalization alone.

## Acceptance

Validation must record exact source hashes, dependency revisions, fresh Lean
checks, declaration axiom reports, source screening, independent semantic
review, and the scope of any remaining build failure. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted in exported theorem axiom
closures. External upstream verification reports are provenance, not a fresh
validation result for this integration.

All compilation is serialized through the repository's shared build lock.
Canonical root validation and the isolated GRH package are distinct build
surfaces; successful focused validation does not certify every repository
default target.
