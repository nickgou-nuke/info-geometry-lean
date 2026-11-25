# Zorn operator and Souriau intake contract

## Provenance and baseline

This change processes the user-supplied Zorn operator narrative and the separate
`WeinsteinGroupoidSouriauAudit` proposal supplied on 2026-11-24. The source
baseline is `fe24e350b08fdea04f74c0748ef9fd9417c47529`. During this work,
PR #441 introduced overlapping general left-operator results. This change is
therefore stacked on its exact head
`4c45f2bd932592fa86820f2e3360085f9e060c38`, reuses its left-unit criterion,
and adds the right-action and Ell-circular readouts. The earlier para-twistor
draft PR #439 is a separate change and is not modified by this work. A parent
PR's publication is not evidence of native acceptance of its declarations.

The uploaded Souriau proposal is preserved verbatim at
`docs/intake/zorn-souriau-20261124/souriau-proposal.txt`, SHA-256
`849a749a4b8c387fc806d45c6e5a09ff69b928bd5618ff1aa353bd2b39b98799`.
The Zorn narrative is preserved as a transcription in the same intake directory.
These inputs are proposed mathematics, not implementation instructions or
evidence that their claims have been proved.

## Mathematical contracts

| Claim | Actual carrier and assumptions | Existing owner | Smallest new implication |
|---|---|---|---|
| Zorn regular invertibility | The native real `CanonicalZorn`, its nonassociative multiplication, real norm, and `Module.End` regular action | `ZornDerivationBridge`, `FirstQuantizedLeftRegular`, `ZornInverseMoufangBridge`, circular operator readout; PR #441's `CanonicalZornRegularNorm` for the left action | Right-action bijectivity iff the native norm is nonzero; reuse the left criterion and transport both to the native circular coordinates |
| Four-vector incidence | Two real four-vectors, the existing circular Witt embeddings, and the native split norm | `SplitOctonionCircularWittForm`, `SplitOctonionEllCircularQuadraticCoordinates` | Derive the operator invertibility/incidence criterion from the norm formula, without replacing the eight-dimensional carrier by the off-diagonal six-dimensional projection |
| Clifford scope | The universal Clifford algebra of the seven-dimensional imaginary subspace and its represented endomorphisms | `SplitOctonionCliffordAction`, `SplitOctonionCliffordNoninjective` | Documentation correction: the full 128-dimensional algebra does not embed in the 64-dimensional endomorphism algebra |
| Peirce/CAR distinction | Rank-four regular pole projectors; the separate CAR vacuum with one-dimensional range | `SplitOctonionEllCircularOperatorCoordinates`, `RegularCARVacuumSeparation` | Documentation correction; no new minimal-ideal classification is inferred |
| Affine action groupoid | Existing `CartanSouriauAffineCocycle.Datum` on an additive group, including action and cocycle laws | `CartanSouriauAffineCocycle`, mathlib `CategoryTheory.ActionCategory` | Bundle the existing affine action as a native `MulAction`, reuse mathlib's `Groupoid`, and expose typed orbit/invariant-function consumers |
| Cotangent graph signs | A native real bilinear form and `V × Module.Dual ℝ V`; skewness where required | Mathlib bilinear forms; existing KKS scalar owners for comparison | For `Ω((x,ν),(y,μ)) = μ(x) - ν(y) + B(x,y)`, restriction to the positive graph is `-B`, while restriction to the negative graph is `3B`; retain a nonzero counterexample |
| Finite negative log-partition | A nonempty finite index set and real linear charges | Existing positive-log Massieu/calculus owners; mathlib exp/log and finite inequalities | Preserve the `-log Z` convention explicitly and only claim the convexity/transport strength actually established |

The group cocycle `θ`, a possible Lie-algebra cocycle `Θ`, and a scalar
partition shift are different objects. An identification needs an explicit
construction and compatibility theorem.

## Rejected or conditional intake statements

* `Cl(4,3)` is represented on the real eight-dimensional Zorn carrier. The
  representation of the full universal algebra is not injective; the existing
  owner proves dimensions 128 and 64 and a kernel dimension lower bound 64.
  An identification of its image, a simple quotient, or the even algebra is a
  separate theorem.
* `L_a L_b` is generally different from `L_(ab)`. For the convention
  `[a,b,c] = (ab)c - a(bc)`, their discrepancy evaluates to `-[a,b,c]`.
* A null Zorn element need not be square-zero: the nonzero pole idempotents
  are null. Trace/imaginary or explicit square-zero hypotheses must remain.
* A projective point and projective hyperplane require nonzero representatives.
  The affine pairing equation itself also admits zero representatives.
* The basic Peirce pole operators have four-dimensional ranges. The separately
  constructed CAR vacuum has one-dimensional range. Neither statement alone
  establishes a claimed physical minimal-ideal model.
* With the uploaded negative graph laws, its displayed bilinear form gives
  `3B`, not `-B`. This remains false even for a genuine alternating bilinear
  cocycle on the abelian Lie algebra `ℝ²`.
* The native action groupoid is algebraic. No smooth cotangent groupoid,
  closed multiplicative differential form, orbit quotient, or Weinstein
  symplectic-groupoid theorem is supplied by the attachment.
* For `Z = Σ exp(-energy)`, `log Z` has covariance Hessian and `-log Z` has
  negative covariance Hessian, whenever the relevant derivatives are proved.
  Positive definiteness and an inverse Hessian need nondegeneracy. An assumed
  invariant function is not a derivation of entropy invariance.
* Equality of representation dimensions does not construct triality. A neutral
  quadratic form does not by itself construct Born geometry, a causal fermion
  system, or field dynamics.

## Dependency order

The Zorn chain is multiplication and norm, regular inverse identities, operator
invertibility, then the circular four-vector incidence readout. The generic
left criterion is supplied by the parent owner; no duplicate left inverse or
unit API is introduced here. The affine
chain is representation and cocycle, affine action, then its native action
groupoid. The bilinear graph restriction and finite partition calculations
are independent chains until explicit maps relate their inputs.

## Validation and independent review

Root and the repository scout author candidate changes. The mathematical
auditor reviews their statements independently; the QA reviewer checks the
validation route and evidence. Candidate source lives outside promoted owners
until the parent reviews it.

Native compilation and transitive axiom acceptance use the pinned Lean
4.34.1 / mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` environment and
the repository's shared build lock. Existing theorem source, source scans,
native compilation, and native axiom audit are separate evidence. At intake,
no new native validation has run. Final results must replace this provisional
status with exact commands, results, and remaining blockers.
