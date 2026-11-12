# Horizon compression and ordered middle-sector pairing

## Intake and source authority

Intake: `Pasted text(20261112-084537).txt`, supplied on 12 November 2026.
The supplied source is retained with the attachment. Its SHA-256 is
`b65c32caa89c920ed97c746a03a18e30472b52ace04ff3d7ea8b1040e185e657`.
Implementation base: upstream
`a392af178af1fe2bcba2ba39eb405700c6ee103c`.

The intake proposes a chain from a real Clifford algebra and a tripotent
through compression, pairing, thermal dynamics, anomalies, and radiation.
This contract records the algebraic statements, their hypotheses, and the
points at which the proposed chain does not follow. A formal dependency is
an actual construction or theorem use; similarity of physical language does
not supply an implication.

## Existing owners

- `Core/PeirceCompressionDefect.lean`: arbitrary associative-ring multiplication
  defects, polarized star-Gram factorization, finite complement decomposition,
  and exact transfer criteria under properness.
- `Core/PeirceCompressionCStar.lean`: native C-star properness, exact squared
  transfer norm, and mixed-defect bounds without a dimension assumption.
- `Physics/Algebra/TripotentPeirceProjectors.lean`: the three polynomial
  projectors, their six ordered orthogonality laws, and partition of unity.
- `Physics/Algebra/TripotentFiveGradingDecomposition.lean` and
  `Core/TripotentEigenspaces.lean`: native five-grade ranges, a direct-sum
  equivalence, actual adjoint eigenspaces, and grade-addition laws.
- `OperatorAlgebra/PeirceSpine/TripotentParity.lean`: the existing zero-sector
  parity action on those five grade ranges.
- `Core/PeirceCoupledCorners.lean` and
  `Canonical/PeirceCouplingPositivity.lean`: opposite-corner square identities,
  native matrix PSD, exact common kernels, and the distinction between a
  nonzero Gram operator and positive definiteness.
- `Canonical/TripotentMatrixExample.lean`: dense frame units in the full real
  four-by-four matrix algebra, with ordered products, adjoints, nonzero
  sectors, and a noncommutative middle corner.

No new decomposition, grading, parity structure, or unitary witness structure
is introduced. The unitary carrier is Mathlib's `unitary A`; its conjugation
is `Unitary.conjStarAlgAut`.

## Exact conventions and targets

For a star projection `p` and a native unitary `u`, write

\[
\sigma_u(x)=uxu^*,\qquad
\Phi_u(x)=p\sigma_u(x)p,\qquad
B_u(x)=(1-p)\sigma_u(x)p.
\]

The target polarized identity is

\[
\Phi_u(x^*y)-\Phi_u(x)^*\Phi_u(y)=B_u(x)^*B_u(y).
\]

The algebraic theorem is over an arbitrary star ring. Its native C-star
corollaries detect zero and the exact norm. Finite real or complex matrices supply
`Matrix.PosSemidef` and strict trace detection. In particular, for an ambient
star projection `q`, the strict trace deficit is equivalent to
`B_u(q) ≠ 0`; no assumption that `q` lies in the observation corner is needed.

The full-domain map sends `1` to the corner identity `p`. Preservation of
the corner identity by the restricted endomap has the different defect

\[
p-\Phi_u(p)=\bigl((1-p)u^*p\bigr)^*\bigl((1-p)u^*p\bigr).
\]

The reverse unitary in this expression is intentional. In an infinite
operator algebra, one-sided invariance is not silently strengthened to
commutation. The sufficient closed-sector hypothesis is `Commute u p`.

Composition has the exact intermediate-block correction

\[
\Phi_{uv}(x)-\Phi_u(\Phi_v(x))
=p\sigma_u\!\left(p\sigma_v(x)(1-p)
 +(1-p)\sigma_v(x)p+(1-p)\sigma_v(x)(1-p)\right)p.
\]

For a real-algebra tripotent `S`, reuse

\[
P_+=\tfrac12(S^2+S),\quad P_0=1-S^2,\quad
P_-=\tfrac12(S^2-S).
\]

For operator-valued middle coefficients, the ordered construction is

\[
B=(P_+aP_0)(P_0wP_0)(P_0bP_-).
\]

Placing the middle factor first annihilates the incoming corner. The correct
ordering gives `P₊ B P₋ = B`, native grade `+2`, square-zero, and zero-sector
annihilation. For self-adjoint `S`, the adjoint has grade `-2`. Their sum
preserves the existing parity action and satisfies

\[
(B+B^*)^2=BB^*+B^*B,\qquad
[S,B+B^*]=2(B-B^*).
\]

The zero-sector parity owner's involution is `1 - 2 S²`, the negative of
the intake's `2 S² - 1`. Their conjugation actions agree, but their traces
have opposite signs. No trace identification is made here.

The additional kernel target uses native `Module.End ℝ E` and
`LinearMap.ker/range`, with no finite-dimensional assumption. For operators
`B=P₊BP₋` and `C=P₋CP₊`, injectivity of `B` on the negative sector and of `C`
on the positive sector gives exactly the middle-sector kernel for `B+C` and
its square. These injectivity premises are not inferred from nonzero `B`, a
nondegenerate middle coefficient, or sector labels.

The stronger dual-inverse relations posited for the intake's `I₊` and `I₋`,
`BC=P₊` and `CB=P₋`, give the exact algebraic normalization
`(B+C)²=1-P₀` and discharge its middle-kernel equality through Mathlib's
idempotent range/kernel theorem. The dense frame realizes both ordered
inverse equations. These product relations are not established for an
arbitrary `middlePairing` or BdG construction. No analytic gap estimate is
inferred solely from support.

## Countermodels and corrected boundaries

| Intake claim | Exact correction |
| --- | --- |
| `(1-p)up ≠ 0` forces a strict Schwarz defect for a corner projection | False. A unitary exchanging orthogonal sectors has nonzero raw transfer, but maps the observed projection to zero. Strictness concerns `B_u(q)` instead. |
| Compression preserves arbitrary unitary composition | False. The dense-frame exchange has `u²=1`, while two successive compressions kill the cut and compression after `u²` restores it. This witness is an orthogonal reflection, not a constructed continuous exponential path. |
| Corner compression is a tensor partial trace and is CPTP | A direct-sum corner is not a tensor factor. The restricted corner map need not preserve its unit; trace preservation and a partial-trace construction are separate requirements. |
| A middle operator can be moved before the incoming corner | False. The wrong order vanishes; the dense-frame witness has `F₀₂ F₂₃ F₃₁ = F₀₁ ≠ 0` in the correct order. |
| Odd parity implies square-zero | False. The existing dense frame supplies an odd sum whose square is `F₀₁ ≠ 0`. |
| Extreme support or nonzero pairing gives exactly the middle kernel and a gap | Zero-sector inclusion follows. Equality needs the stated outer-sector injectivity; a uniform positive spectral gap requires additional analytic bounds. |
| `[S,H]=[J,H]=0` makes `JH` grade zero | The missing term is `[S,J]H`. Adding `[S,J]=0` repairs grade preservation and also makes the exponential commute with all three polynomial projectors, eliminating their leakage. |

The square of a paired operator can be nonzero PSD while having outer-sector
zero modes. Positive definiteness on the entire ambient space is impossible
when a nonzero middle sector is annihilated. A uniform identity
`(B+B*)²=c(P₊+P₋)` requires the separate ordered product equalities
`BB*=cP₊` and `B*B=cP₋`; a positive gap also requires `c>0`.

The following claims remain outside the implemented theorem surface:

- A GKSL generator, Markov property, Fisher–Rao/parabolic equation, monotone
  entropy, or irreversible dynamics does not follow solely from a compression
  defect. No such analytic construction is supplied.
- The scalar boost formula cannot be substituted with a noncommuting
  operator-valued time parameter. Under the intake's Clifford relations,
  `(J K)²=1`; this is not an elliptic generator. A KMS state and its strip
  analyticity require their own definitions and proof.
- `Tr(2S²-1)=4-N` under the stated finite trace dimensions is trace balance.
  Identifying it with a Weyl anomaly or a renormalization law is additional
  physical input.
- A skew form must have a specified stabilizer. A nonzero complex skew form
  is not invariant under the whole defining `SU(4)` representation: its
  central element `iI` sends that bilinear form to its negative.
- A quotient group action, a complex structure, or a zero-mode subspace
  alone does not construct photons, helicity representations, soft memory,
  a thermal state, or gravitational field equations.

The intake's proposed master equivalence is therefore not promoted as a Lean
theorem. The dependency order used by the implementation is: existing
projectors and unitary conjugation; ordered compression and pairing; exact
transfer/composition/kernel statements; explicit dense countermodels.

## Verification record

Source review and independent static QA were completed on 12 November 2026.
The public inventory contains 77 declarations: 72 theorems and five definitions.
The audit companion names every public declaration exactly once.

- Independent A-A source review: PASS for the stated algebraic and conditional
  claims. This is not kernel acceptance.
- Strict refutation of the five new Lean files and the aggregate import file:
  exit 0, with no reported traps.
- Static Gate 4 on the five new Lean files: exit 0, explicitly
  `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`.
- Warning-strict semantic-vacuity scan: exit 1, with 13 `trivial_surface`
  warnings. Independent QA read the flagged direct compression laws, projector
  adjoint formulas, and dense-frame calculations and found no vacuous premise
  or carrier substitution. Their short proofs were retained.
- Declaration/audit inventory and `git diff --check`: passed.

Kernel verification is still pending. The first local focused build was
cancelled while waiting for another job's active shared build lock, before
Lake or Lean started. A scoped GitHub workflow builds the audit target and
freshly elaborates all five new Lean files on an independent runner. Its
result must be inspected before any axiom-dependency or compilation acceptance
is claimed. Draft publication does not constitute theorem acceptance.

Root Lean and Mathlib pins remain unchanged. The existing focused
`verification/language-symmetry` project is reused with explicit targets;
its missing `DAG` library registration is added because the selected native
owner closure imports `DAG.Basic`. Its cache command now runs from the focused
project directory so dependency archives hydrate that project's package paths;
source checks retain the repository-root working directory and shared lock.
Runtime package-location overrides point
to all nine exact, clean root package revisions without changing pinned
dependencies. A focused build is not a root-package or `InfoGeometry.All`
build. The preexisting missing Homotopy/Atlas paths and uninitialized GIFT
gitlink remain separate root-package integration constraints. A fresh
`python3 tools/infra/ci_bootstrap.py paths` check returned exit 1 with those
three constraints on 12 November 2026.
