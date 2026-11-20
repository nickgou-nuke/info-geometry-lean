# Centered Mangoldt interpolation and analytic bridge

## Intake and integration

The user requested implementation of the repository-grounded route audit and
publication of a pull request targeting upstream `main`. This branch combines
the finite smoothing in PR #421 (published head
`55c39dfb69b0c139814beb4e0c3766f299a111ee`) and the native RH half-plane
reduction in PR #422 (published head
`3c89245fc40b6ddf6d0de385254e3ccef041e47a`). Both were unmerged at intake;
upstream `main` was `586c14bc9fb94eb09b56f7dc850d9d5297269f91`.

The mathematical source is the real smoothing described in
<https://alpo.ge/remark.pdf>. The separate source audit identified the
`Formalism.zetaLandauEps` interface in the public announcement mirror. No
external proof module is imported, and source inspection is not counted as
kernel verification.

## Exact objects

Reuse `InfoGeometry.Arithmetic.PrimeDistributionLaw.vonMangoldtWeight`,
`harmonicMangoldtSum`, `smoothedMangoldtSum`, and `chebyshevPsiFinite`.
All new smoothing and interpolation objects have real coefficients.

For real x, define S(x) by the native finite sum through the natural floor of
x. The zero-index term vanishes by native von Mangoldt evaluation. Prove that
this range-indexed definition equals the positive-index Icc definition and
agrees with the existing integer sum.

Define G(x) = S(x) - x log x + (1 + gamma) x with Mathlib's actual
`Real.eulerMascheroniConstant`.

## Intended theorem obligations

1. The real-cutoff sum is affine on each closed unit interval [N,N+1], with
   endpoint values supplied by the existing integer owner.
2. For N >= 1 and 0 <= t <= 1,
   G(N+t) = (1-t) G(N) + t G(N+1) + E(N,t),
   where 0 <= E(N,t) <= t(1-t)/(2N) <= 1/(8N).
   The error is derived from native convexity and derivatives of x log x;
   it is not a hypothesis stored in a structure.
3. For either fixed sign, eventual integer power upper bounds transfer to
   eventual real power upper bounds, with nonnegative exponent and an
   explicit constant. Prove the corresponding integer/real equivalence for
   the square-root-plus-epsilon family, preserving all quantifier order.
4. Establish the Mellin identity for S and its centered version on Re(s)>1
   from native L-series, integral, and logarithmic-derivative facts, including
   proofs of the required integrability.

Each promoted owner must have complete Lean proofs, a declaration inventory,
an axiom audit, and independent mathematical review. The allowed foundational
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Canonical owner connections

| Owner | Result supplied to the next step |
| --- | --- |
| `Arithmetic/FiniteSmoothedMangoldt` (PR #421) | Native integer smoothing, harmonic/Chebyshev separation, and first differences |
| `Arithmetic/SmoothedMangoldtReal` | Floor-indexed real sum, positive-index correspondence, exact affine interpolation, and actual centered remainder |
| `Analysis/CenteredLogInterpolation` | Native convexity/second-derivative proof of the logarithmic chord bounds |
| `Arithmetic/SmoothedMangoldtInterpolation` | Exact centered interpolation and both-sign inequalities |
| `Arithmetic/SmoothedMangoldtGrowth` | Explicit integer-to-real constant and equivalence of fixed-sign growth predicates |
| `Arithmetic/ActualRiemannZetaVonMangoldtBridge` (existing) | Native von Mangoldt L-series equals the actual negative zeta logarithmic derivative for Re(s)>1 |
| `Arithmetic/SmoothedMangoldtMellin` | Integrability and evaluated Mellin integrals for S and G on Re(s)>1 |
| `Arithmetic/RiemannHypothesisHalfPlaneReduction` (PR #422) | Native RH iff zeta nonvanishing for Re(s)>1/2 away from s=1 |

The arithmetic-to-Mellin bridge uses the ordinary von Mangoldt function and
the ordinary Riemann zeta function. It does not require the all-character
Dirichlet premise retained separately in PR #422.

For `eta = 1` or `eta = -1`, `alpha >= 0`, `C >= 0`, and `N₀ >= 1`, the
explicit growth contract is

\[
\bigl(\forall N\ge N_0,\ \eta G(N)\le C N^\alpha\bigr)
\Longrightarrow
\bigl(\forall x\ge N_0,\ \eta G(x)\le(2^\alpha C+1/8)x^\alpha\bigr).
\]

The exponent-family equivalence fixes eta first, then quantifies over every
epsilon > 0; each epsilon may have its own constant and threshold. It does
not allow changing the sign with epsilon or the cutoff.

For Re(s)>1, the Mellin contract is

\[
\int_1^\infty S(x)x^{-s-1}\,dx
=\frac{-\zeta'(s)/\zeta(s)}{s(s-1)},
\]

\[
\int_1^\infty G(x)x^{-s-1}\,dx
=\frac{-\zeta'(s)/\zeta(s)}{s(s-1)}
-\frac1{(s-1)^2}+\frac{1+\gamma}{s-1}.
\]

Both statements include `IntegrableOn` as a proved conjunct. Their proof
uses Mathlib's partial-sum integral theorem twice, with genuine growth
bounds obtained from absolute L-series convergence, and evaluates the
elementary centering integrals. Complex scalars occur at this native
analytic boundary; the smoothing and interpolation remain real.

## Scope barriers

The square-root cancellation estimate itself is not supplied by the finite
identities. Neither a positivity hypothesis for an arbitrary functional nor
an assumed Landau implication may be presented as an arithmetic proof.
The one-sided Landau continuation argument and cancellation assertion remain
open until separately implemented and checked. PR #422's actual native RH
endpoint is retained with its explicit nonvanishing premise.

In particular, a one-sided estimate on G does not bound its absolute value.
It cannot be inserted into the convergent-half-plane Mellin theorem to claim
absolute convergence on Re(s)>1/2. The missing Landau step must prove the
appropriate continuation from the corrected nonnegative function, then
identify the actual logarithmic derivative and exclude its poles. Proving
that criterion and proving the arithmetic growth premise are separate
remaining obligations.

This work does not claim an unconditional proof of RH/GRH, a theta-lift
estimate, a global spectral realization, or a full repository build.
The root dependency pins and toolchain are unchanged. Build and publication
evidence will record any root integration blocker separately from the
focused proof verification.
