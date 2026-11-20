# Centered Mangoldt and real operator routes: theorem contract

## Provenance and existing owners

This development follows the user's 2026-11-20 request to search the existing
arithmetic and operator code, implement useful alternative RH routes in native
Mathlib, and publish an upstream PR. The supplied route audit is an intake
document, not proof authority. Source searches and Lean checks determine the
accepted scope below.

The branch combines the unchanged prerequisites from PR #421 (commit
`55c39dfb69b0c139814beb4e0c3766f299a111ee`, finite Mangoldt smoothing) and PR #422
(commit `3c89245fc40b6ddf6d0de385254e3ccef041e47a`, native RH half-plane
equivalence). Both start from main `586c14bc9fb94eb09b56f7dc850d9d5297269f91`.
Neither prerequisite is assumed to have been merged into main.

Reused arithmetic owners are `PrimeDistributionLaw`, `FiniteSmoothedMangoldt`,
`ActualRiemannZetaVonMangoldtBridge`, and
`RiemannHypothesisHalfPlaneReduction`. They provide the actual Mathlib von
Mangoldt coefficients, the finite sum and difference identities, the
convergent-half-plane logarithmic derivative, and the final native RH
equivalence. They do not provide centered square-root cancellation.

## Exact arithmetic target

All cutoffs and inequalities are real. Define

\[
S(x)=\sum_{0\le n\le\lfloor x\rfloor}\Lambda(n)(x/n-1),\qquad
G(x)=S(x)-x\log x+(1+\gamma)x.
\]

The zero term vanishes because native `vonMangoldt 0 = 0`. The real sum must
agree with the existing natural-cutoff sum. For natural `N` and `0 ≤ t ≤ 1`,
prove exact affine interpolation for `S(N+t)` and the identity

\[
G(N+t)=(1-t)G(N)+tG(N+1)+E_N(t).
\]

The independently useful native calculus target is

\[
0\le E_N(t)\le\frac{t(1-t)}{2N}\le\frac1{8N}\quad(N\ge1).
\]

This should transfer eventual signed polynomial bounds from integer to real
cutoffs with explicit constants. The fixed sign must stay outside the
epsilon quantifier. A one-sided bound must not be used as an absolute
integrability estimate.

The centered second difference subtracts the strictly positive second
difference of `x * log x` from `Λ(N+1)/(N+1)`. In particular, at a non-prime-power
index the centered second difference is negative. Positivity/convexity of the
uncentered sum therefore does not itself prove centered cancellation.

## Complete conditional Möbius route

The alternative Möbius route reuses the actual integer `mertensFunction`, the
existing `MertensSquareRootCancellation` statement, its all-indices growth
bound, and the already proved reciprocal-zeta integral for `1 < s.re`.
The native Mellin continuation is implemented in
`Arithmetic/MertensMellinRiemannHypothesis.lean`.

For `0 ≤ r < 1`, assume the actual estimate

\[
|M(N)|\le C(N+1)^r,\qquad C\ge0.
\]

The cutoff `1_(1,∞)(x) M(floor(x))` is locally integrable, vanishes near zero,
and is `O(x^r)` at infinity. Native Mellin differentiation therefore proves
holomorphy of

\[
F(s)=s\int_1^\infty M(\lfloor x\rfloor)x^{-s-1}\,dx
\]

on `r < s.re`, with a separate convergence theorem. The existing reciprocal
identity holds on `1 < s.re`. Analytic continuation on the connected half-plane
extends the denominator-cleared identity

\[
\operatorname{riemannZeta}_1(s)F(s)=s-1.
\]

Mathlib's entire regularization has value one at `s = 1`, so no holomorphy of
the unregularized zeta function at its pole is assumed. The identity excludes
actual zeta zeros when `r < s.re` and `s ≠ 1`. Choosing
`1/2 < r < min(s.re,1)` under `MertensSquareRootCancellation`, and then reusing
the native half-plane equivalence from #422, proves
`MertensSquareRootCancellation → _root_.RiemannHypothesis`.

The cancellation premise is not proved. The reverse implication is not
implemented here. Unordered Möbius `LSeries` summability is used only in the
existing convergent region and is never asserted in the critical strip.

## Mangoldt analytic boundary

The desired centered Mellin identity on `1 < s.re` includes integrability:

\[
\int_1^\infty G(x)x^{-s-1}\,dx=
\frac{-\zeta'(s)/\zeta(s)}{s(s-1)}-
\frac1{(s-1)^2}+\frac{1+\gamma}{s-1}.
\]

It must be proved from native improper integrals and justified integral/series
interchange. Whole-plane statements must use native regularization at the pole.
The external zeta-only Landau source is a bounded navigation reference (18
files, 2,338 lines at snapshot `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`),
not an imported proof dependency. Its mirror states that no source license was
provided; this branch does not relabel those proof bodies as Apache-authored
repository code. Any promoted analytic implementation is written against
native Mathlib and is accepted only at its compiled type.

The one-sided Landau step is a separate substantive positivity/Taylor argument.
An absolute-growth route can use holomorphic Mellin continuation directly, but
its stronger hypothesis must be stated explicitly.

## Exact real operator target

Use a real inner-product space `H`, an actual submodule domain `D`, and a linear
map `K : D →ₗ[ℝ] H`. Domain skew symmetry and a real skew map `J` give

\[
\|Kv-bJv-av\|^2=\|Kv-bJv\|^2+a^2\|v\|^2.
\]

Consequences are a quantitative residual lower bound and exact-mode exclusion.
The concrete `K_max` consumer also proves injectivity of every nonzero real
shift on its existing maximal domain. No boundedness, completeness, or external imaginary
scalar is needed for this endpoint. The existing `K_max` on its maximal real
ℓ² domain is a concrete source of the skewness hypothesis.

The arithmetic zero-to-domain-mode construction remains a separate obligation.
For Krein spaces, nonzero vectors may be neutral: nonneutrality of the relevant
arithmetic modes is required. Positive finite/GNS readouts do not identify the
actual arithmetic Weil form without a proved compatibility or limit theorem.

## Acceptance and scope

Risk labels: R4 (analytic inference and infinite limits), R5 (provenance and
proof-status reporting). Each promoted owner must have full native proofs,
an explicit declaration audit, an independent semantic review, and a distinct
QA rerun. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted
foundational axioms. The pinned Lean/Mathlib versions remain unchanged.

The root package currently stops during resolution of the missing configured
path dependency `external_refs/homotopy-hypothesis-lean4`. Focused checks and
root integration are recorded separately. No result here is to be described
as unconditional RH unless the actual arithmetic cancellation or zero-mode
construction is proved and the final native RH theorem is checked.
