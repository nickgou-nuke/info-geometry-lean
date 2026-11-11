# Yang–Mills assessment and an ordered transfer-compression bridge

## Scope and provenance

This note records a source review of *Validation of the OpenAI Yang–Mills
construction* (November 10, 2026, 35 pages), supplied as `assessment-1.pdf`, and
a bounded contribution to this repository. The attachment's SHA-256 is
`8e658c00900bf723cbe90436eb1f78fca4f287e008a85c21fdceaf59e61db219`.

External sources were read at these immutable revisions:

- [OpenAI-YM-20261028, `3456e5e75cf8d4cd558955a5c7638fba2d68f464`][submission].
- [YM assessment checks, `55ba9fc36293b3f4d52c6b1f813169a0be76ee98`][checks].

The local comparison starts at upstream `main`,
`c143c264bc18bbf41d692be4e270b5b7f7405702`. The new owner is
[PeirceTransferDynamics.lean][transfer]; its public axiom requests are in
[PeirceTransferDynamicsAudit.lean][audit].

**Release status: draft source, pending native verification.** Complete proof
scripts have been written, but the shared build lock was occupied during this
task. Source review and static gates do not establish Lean elaboration or an
axiom footprint. The external assessment's historical build report is also not
a build performed in this session. No Yang–Mills mass-gap theorem is claimed.

## 1. What the assessment actually supports

### Quantifiers and a common witness

The public [ChallengeSpec.lean][challenge] defines `JointExistence` with the
following order of quantifiers:

```lean
∀ g : GaugeGroup, g.IsSimple →
  ∃ C : WilsonFamily g, WilsonRegularity C ∧
    ∀ p : ℕ → ℕ, StrictMono p →
      ∃ q : ℕ → ℕ, StrictMono q ∧
        ∃ T : Hierarchy C, T.Properties (p ∘ q)
```

One Wilson family is chosen before an arbitrary requested increasing volume
sequence. A refinement and a hierarchy can then depend on that sequence.
`Properties` combines Wilson convergence, reconstruction, an operator-product
expansion, and a trace test. This quantifier order supplies neither equality of
the hierarchies obtained from different sequences nor convergence of the whole
volume sequence. It also does not quantify over every regulator construction.

The selected public theory and the phase family must be distinguished.
`Hierarchy.Reconstructed` contains the selected theory's axioms and its
relationship to the phase mixture. The stronger `YangMills.constructed` in
[Construction.lean][construction] retains one `Final`, one almanac, the lattice
and calibration data, and an explicit every-phase axiom clause. The latter
claim should be attributed to that stronger endpoint, rather than inferred
from the selected-theory clause alone.

[CombinedAcceptance.lean][combined] uses `YangMills.constructed` once and
assembles the review clauses for the resulting **same** family, refinement,
table, and `Final`. This matters: independent existential theorems cannot be
conjoined by silently identifying their witnesses. Likewise,
`YMReview.OPE.from_source` in [OPECheck.lean][ope] translates the OPE for an
already chosen hierarchy. It can be applied to that hierarchy's OPE field
without selecting a new theory. This is a legitimate composition of existing
interfaces, not an additional analytic existence result.

### Boundaries that remain visible

| Reported result | Boundary retained by the assessment |
|---|---|
| Wilson lattice construction and selected subsequential limits | No all-volume convergence, infrared uniqueness, or regulator universality follows; see pp. 4–7 and 13. |
| A phase mixture and component reconstruction | The compressed ground-state algebra is commutative. This does not make the full field algebra commutative; see p. 8. |
| Clustering in components | It does not imply clustering of the mixed state. Under additional mixed clustering, continuity and full support can force phase agreement within that mixture; this still does not compare different volume subsequences; see p. 9. |
| Positive short-distance trace asymptotics and a nonfree test | The stated exclusion concerns a specified finite free-kernel class. It is not a classification of every Gaussian composite description; see pp. 10–11. |
| OPE estimates | Truncation is by field-label degree, not loop order. No all-orders perturbative matching is asserted; see p. 12. |
| Independent OS comparison | The selected centered scalar trace is checked on diagonal-flat Schwartz tests, which vanish to all orders on collision diagonals. These are distinct from separated compact tests, unrestricted Wightman tests, and Euclidean contact extensions; see p. 17. |
| A positive eighth-root two-point probe | Positivity of this probe is not a positive lower bound on a Hamiltonian spectrum; see p. 18 and [TwoPointPhysicalObservable.lean][probe]. |

The assessment explicitly leaves a uniform mass gap, infrared uniqueness,
continuum probability-measure questions, Wilson-loop/area-law questions, and
particle-spectrum questions open (p. 13). Its historical clean-build and axiom
audit figures on pp. 14–15 concern the assessed external revision. Its external
toolchain and Mathlib pins on p. 21 differ from this repository's pins; this
contribution neither imports that entire source tree nor changes our pins.

## 2. Precise primitives extracted from the proposed interpretation

The structural vocabulary becomes useful only after fixing its carrier and
operations. Here the initial carrier is an arbitrary associative ring `R`.

| Structural role | Mathematical object | Necessary qualification |
|---|---|---|
| Binary distinction | An idempotent `p`, with `q = 1 - p` | `p * p = p`; it becomes an orthogonal projection only with additional star/Hilbert structure. |
| Four relational blocks | `p*a*p`, `p*a*q`, `q*a*p`, `q*a*q` | Multiplication order is retained; off-diagonal arrows are not identified. |
| A directed round trip | `(p*a*q)*(q*b*p)` | Reversal generally changes the operator and may place it in the other corner. |
| Failure of compression to preserve multiplication | `p*(a*b)*p - (p*a*p)*(p*b*p)` | This is exactly the directed round trip, by the existing compression owner. |
| Repeated evolution | `t^n`, with `t*p = p` and `p*t = p` | Vacuum preservation is an explicit hypothesis, not a consequence of idempotency. |
| Quantitative decay | A norm bound on `q*t*q` | The strict inequality needed for decay must be proved or supplied separately. |

For any `x`, the existing square-defect identity can be written

\[
p(x^2-x)p-\bigl((pxp)^2-pxp\bigr)=pxqxp.
\]

Thus compression can create an idempotency defect even when `x` is idempotent.
The cut itself has no such defect: `p²-p=0` by hypothesis. In a suitable star
algebra, adjoint choices turn directed round trips into positive Gram terms.
Positivity alone supplies no strictly positive lower bound.

Applying these identities at another stage requires actual stage maps and
compatibility laws. Repeating a metaphor or nesting a compression does not
construct a direct limit, a completed Hilbert space, or a physical theory.
Likewise, a thermodynamic component phase is not a scalar phase multiplier of
a Weyl word. No identification between those meanings of “phase” is used here.

## 3. New theorem: ordered evolution through the complementary corner

Let `R` be a ring, let `p,t,a,b : R`, and assume

\[
p^2=p,\qquad tp=p,\qquad pt=p,\qquad q=1-p.
\]

The new owner supplies a proof script for the following exact statement for
every natural number `n`:

\[
\boxed{
p(a t^n b)p-(pap)(pbp)=(paq)(qtq)^n(qbp).
}
\]

It imposes no commutation between either observable and the cut, between the
observables and the transfer, or between the two observables. Its Lean statement
is:

```lean
theorem compression_transfer_power_eq (p t a b : R) (hp : p * p = p)
    (htp : t * p = p) (hpt : p * t = p) (n : ℕ) :
    p * (a * t ^ n * b) * p - (p * a * p) * (p * b * p) =
      (p * a * (1 - p)) * ((1 - p) * t * (1 - p)) ^ n * ((1 - p) * b * p)
```

The proof uses the existing
`PeirceCompressionDefect.compression_mul_defect`, the fixed-corner identities
`p*t^n=p` and `t^n*p=p`, and `q*t*q=t-p`. If `p*z=0`, induction gives
`t^n*z=(t-p)^n*z`; taking `z=q*b*p` yields the ordered factorization.

The zero-time case is essential. In the ambient ring, `(q*t*q)^0=1`, whereas
`q*t^0*q=q`. The proof equates the fully sandwiched expressions, not these two
middle factors in isolation.

For a `NormedRing`, the owner adds

\[
\|p(a t^n b)p-(pap)(pbp)\|
\le \|paq\|\,\|qtq\|^n\,\|qbp\|.
\]

The zero-power case is simplified before applying submultiplicativity. Positive
powers use Mathlib's `norm_pow_le'`. Consequently no `NormOneClass`, star
structure, or completeness assumption is needed. An explicit bound
`‖q*t*q‖ ≤ r` yields the same estimate with `r^n`; its nonnegativity follows
from the bound. The hypothesis `‖q*t*q‖ < 1` then yields convergence of the
connected compressed words to zero, using the real geometric-sequence limit
and a norm squeeze.

### Dependency order

This is a dependency presentation of the source, not a new formalized causal
poset or a certificate of successful compilation. The existing compression
identity is imported; all new declarations remain pending native verification.

| Level | Statement | Required earlier input |
|---|---|---|
| 0 | `p²=p`, `tp=p`, `pt=p`; ring operations | Explicit hypotheses and native typeclasses |
| 1 | Fixed left/right powers; `excitation_compression_eq_sub` | Level 0 and induction/ring algebra |
| 2 | `pow_mul_annihilated` | Fixed left powers and `p*z=0` |
| 3 | `compression_transfer_power_eq` | Levels 1–2 and existing `compression_mul_defect` |
| 4 | `norm_compression_transfer_power_le` | Level 3, norm multiplication, positive-power norm inequality |
| 5 | `norm_compression_transfer_power_le_of_bound` | Level 4 and the supplied real bound |
| 5 | `compression_transfer_power_tendsto_zero` | Level 4, strict contraction, geometric convergence |

The two level-5 conclusions are separate consequences. The convergence proof
does not need the arbitrary-bound wrapper.

## 4. Meaning for vacuum correlations and the remaining analytic estimate

For bounded operators on an actual Hilbert space, let `p` be the orthogonal
rank-one projection onto a unit vacuum vector `Ω`. Then `p*a*p = ω(a)*p`
with the corresponding vacuum expectation and scalar action. Under the two
vacuum-fixing hypotheses, the displayed compressed difference represents

\[
\bigl(\omega(a t^n b)-\omega(a)\omega(b)\bigr)p.
\]

This scalar interpretation needs the rank-one projection. For an arbitrary
idempotent or a higher-rank ground-space projection, it remains an operator
compression identity. Application to unbounded fields also needs a domain or
bounded-observable construction. Neither identification is formalized by the
new generic owner.

For a nonnegative self-adjoint Hamiltonian `H` with the specified vacuum,
`H*p=p*H=0` makes `H` reduce to the complementary sector. The off-diagonal
observable blocks remain significant even though the Hamiltonian reduces the
vacuum decomposition.

A prospective mass-gap application would identify the actual OS transfer as
`T(τ)=exp(-τH)` and prove, at a fixed physical time `τ>0`,

\[
\|Q T(\tau)Q\|\le r<1,\qquad 0<r.
\]

With those spectral and identification hypotheses, spectral calculus gives a
lower bound `Δ = -log(r)/τ` on the complementary spectrum. This explanation is
conditional mathematics, not a Lean theorem added by this PR. The required
uniform bound for the assessed Yang–Mills theory is still open.

At cutoff time step `a`, the scale-sensitive target is instead
`‖Q T_a Q‖ ≤ exp(-a Δ)` for one positive physical `Δ`, uniformly through the
relevant cutoff and volume limits. A fixed contraction factor per shrinking
step would be a stronger, differently scaled assertion. Pointwise finite-stage
positivity, qualitative clustering, or a UV coefficient does not supply this
uniform estimate. A single two-point probe also need not detect every
low-energy sector.

## 5. What this repository already provides

The bounded search inspected definitions, assumptions, imports, and consumers.
Compiler-generated declaration-DAG inventories were unavailable in this
checkout; this is not an exhaustive repository-wide absence claim.

| Existing owner | Source-backed content | Remaining distinction |
|---|---|---|
| [Core/PeirceCompressionDefect][compression] and [Core/PeirceCompressionCStar][cstar] | Exact ordered multiplication defect; adjoint and mixed norm bounds | The new contribution adds fixed-vacuum evolution powers and conditional decay. |
| [OperatorAlgebra/PeirceHodgeCoercivity][hodge] | Full real-matrix Hilbert–Schmidt coercivity for an orthogonal `p` and `γ≥0`, from `K - γ(1-p) ⪰ 0` | The lower bound is an input. |
| [Analysis/RealPositiveOperatorGap][gap] | Genuine finite-dimensional positive-operator gaps on the kernel complement | The kernel is not automatically a vacuum line, and stagewise positivity is not uniformity. |
| [Analysis/RealPositiveOperatorScaling][scaling] | `not_exists_uniform_positive_coercive_bound` under positive rescaling, when a nonzero kernel-complement vector exists | The repository already exhibits the uniformity obstruction. |
| [Canonical/LieJordanHodgeColimit][colimit] | `uniform_coercivity_at_limit` and `uniform_coercivity_descends` on the actual algebraic limit | A common constant and compatibility/intertwining hypotheses must be supplied. |
| [Canonical/Cl11CARPeirceMassCoercivityBridge][car] | A concrete CAR model and constant-2 limit coercivity | No identification with the assessed Yang–Mills Hamiltonian is supplied. |
| [Canonical/FilteredGNSHilbertColimit][gns] | Completed Hilbert direct limit, stage isometries, dense union for a compatible state family | Generic GNS completion exists; its identification with the external construction is a separate obligation. |

The ring-level curvature and Bianchi identities in
[PeirceDefectBridge.lean][curvature] also retain noncommutative content. Their
inner-derivation interpretation does not itself construct a four-dimensional
spacetime field theory. Existing trace positivity and concrete positive-energy
examples likewise must not be promoted to a uniform spectral theorem.

## 6. A separate semantic obstruction in older seed interfaces

This section is an explicit mathematical source-audit argument, independently
reviewed, **not a newly compiled Lean obstruction theorem**. It does not enter
the new transfer owner's imports.

[KMSSinkhornSeedState.lean][kms] defines

```lean
def CommutatorOrthogonalOnOmega (Ω : DoubledSpace F) : Prop :=
  ∀ A B : AlgebraEnd F,
    inner ℝ (((A * B - B * A) Ω)) Ω = 0
```

The actual [doubled carrier][doubled] is `WithLp 2 (F × F)` with its positive
Hilbert inner product. [AlgebraEnd][algebraend] is the full bounded real-linear
endomorphism algebra. The quantifier does not restrict `A,B` to a smaller
observable algebra or require them to be self-adjoint.

For `Ω=(x,ξ)≠0`, set `v=(-ξ,x)`. Then `v` is orthogonal to `Ω` and has the
same norm. The rank-one bounded real-linear maps

\[
A(u)=\langle v,u\rangle\Omega,\qquad
B(u)=\langle\Omega,u\rangle v
\]

belong to that algebra. Write `s=‖Ω‖²>0`. Direct calculation gives

\[
AB\Omega=s^2\Omega,\qquad BA\Omega=0,\qquad
\langle(AB-BA)\Omega,\Omega\rangle=s^3>0.
\]

Hence the stated condition forces `Ω=0`. Both
`ExpectationSeedStructuralWitness` and [FiniteYangMillsBridge][finitebridge]
store this condition together with `Ω≠0`; those hypotheses are mathematically
incompatible on their declared carrier. This finding is confined to those
interfaces. It does not invalidate the independent algebra, coercivity, or
GNS constructions above.

The latter bridge also defines `hasStrictMassGap B` as positivity of a stored
real field and stores that positivity as a hypothesis. Its
`spectralGapFromLogDet` is a maximum of real parameters. That predicate supplies
no relation to a Hamiltonian spectrum. A future repair needs a correctly
specified observable/state interface and a spectral identification; changing
the label of the stored scalar cannot supply either.

## 7. Verification and delivery boundary

The draft adds only the transfer owner, its five public axiom requests, and
this note. Existing physical interfaces, repository pins, and external source
trees are unchanged. The proof scripts use native `Ring`, `NormedRing`, and
`Filter.Tendsto` with narrow owner/Mathlib imports.

The exact static-gate results and independently observed source hashes belong
in the PR verification record. The remaining native checks are a focused build
and an axiom audit under the maintained shared lock. Five `#print axioms`
commands in a file are requests for evidence, not their successful output.
An all-owner audit must also cover the three private helpers after elaboration.

Native entry point when the shared lane is available:

```bash
PATH=/home/agent/.elan/bin:$PATH \
  python3 verification/language-symmetry/check.py build \
  InfoGeometry.Core.PeirceTransferDynamicsAudit
```

A successful focused build would certify this module's declared mathematical
scope. It would not reproduce the external assessment, certify every tracked
repository file, prove the older-interface obstruction in Lean, or close the
open Yang–Mills identification and uniform-gap obligations.

[submission]: https://github.com/yang-mills-group/OpenAI-YM-20261028/tree/3456e5e75cf8d4cd558955a5c7638fba2d68f464
[checks]: https://github.com/yang-mills-group/YM/tree/55ba9fc36293b3f4d52c6b1f813169a0be76ee98/submissions/openai-20261028/checks
[challenge]: https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/ChallengeSpec.lean
[construction]: https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/Construction.lean
[combined]: https://github.com/yang-mills-group/YM/blob/55ba9fc36293b3f4d52c6b1f813169a0be76ee98/submissions/openai-20261028/checks/CombinedAcceptance.lean
[ope]: https://github.com/yang-mills-group/YM/blob/55ba9fc36293b3f4d52c6b1f813169a0be76ee98/submissions/openai-20261028/checks/OPECheck.lean
[probe]: https://github.com/yang-mills-group/YM/blob/55ba9fc36293b3f4d52c6b1f813169a0be76ee98/submissions/openai-20261028/checks/TwoPointPhysicalObservable.lean
[transfer]: ../lean/InfoGeometry/Core/PeirceTransferDynamics.lean
[audit]: ../lean/InfoGeometry/Core/PeirceTransferDynamicsAudit.lean
[compression]: ../lean/InfoGeometry/Core/PeirceCompressionDefect.lean
[cstar]: ../lean/InfoGeometry/Core/PeirceCompressionCStar.lean
[hodge]: ../lean/InfoGeometry/OperatorAlgebra/PeirceHodgeCoercivity.lean
[gap]: ../lean/InfoGeometry/Analysis/RealPositiveOperatorGap.lean
[scaling]: ../lean/InfoGeometry/Analysis/RealPositiveOperatorScaling.lean
[colimit]: ../lean/InfoGeometry/Canonical/LieJordanHodgeColimit.lean
[car]: ../lean/InfoGeometry/Canonical/Cl11CARPeirceMassCoercivityBridge.lean
[gns]: ../lean/InfoGeometry/Canonical/FilteredGNSHilbertColimit.lean
[curvature]: ../lean/InfoGeometry/OperatorAlgebra/PeirceDefectBridge.lean
[kms]: ../lean/InfoGeometry/Canonical/KMSSinkhornSeedState.lean
[doubled]: ../lean/InfoGeometry/Krein/DoubledSpace.lean
[algebraend]: ../lean/InfoGeometry/Canonical/SinkhornKMSCore.lean
[finitebridge]: ../lean/InfoGeometry/Canonical/YangMillsFiniteBridge.lean
