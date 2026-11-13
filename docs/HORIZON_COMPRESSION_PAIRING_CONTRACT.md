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

Verification date: 12 November 2026. The selected theorem surface is kernel
verified at commit `f618bcb3a5bce952d7c68ddd82f04dfe33e0e573`, tree
`8f57f2f363db690ca87227964bbf5419cbfb7d79`. The public inventory contains
77 declarations: 72 theorems and five definitions. The audit companion names
every public declaration exactly once.

### Compiler and independent evidence

- Independent A-A source and evidence review: PASS for the complete ten-file
  diff against `a392af178af1fe2bcba2ba39eb405700c6ee103c`.
- Independent QA-A disposition: `ACCEPTED_WITH_LIMITED_SCOPE` for the five
  new owner/audit Lean files. The `All.lean` import edit was statically screened
  but the aggregate module was not compiled.
- Compiler: Lean 4.34.1, commit
  `5045d0056413266e57c625dcd7c365b10e377c52`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
  Root and focused toolchain/dependency pins are unchanged.

| Verification | Run / attempt | Job | Result |
| --- | --- | --- | --- |
| Initial kernel verification | 43197259546 / 1 | [131111274229](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43197259546/job/131111274229) | PASS |
| Independent QA-A rerun | 43197259546 / 2 | [131115495570](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43197259546/job/131115495570) | PASS |

Both attempts completed successfully at the same source commit. QA-A requested
the second attempt once, independently downloaded its evidence, verified its
archive digest, and reconciled the actual fresh compiler/axiom records with
the current source inventory. The coordinator also inspected the completed
job metadata and actual compiler log.

Evidence archives:

- [Initial verification](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43197259546/artifacts/13934116504),
  SHA-256 `437bd5703d7aa2a2fc63098c8c5aa726ce222cf816d14ec309938656708eb2ef`.
- [Independent QA-A rerun](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43197259546/artifacts/13935030345),
  SHA-256 `70c3c1eb7253e4eeafa160469076418e1aa4065ce84b85b59a1ab0057c1a0779`.

The evidence covers the explicit owner-audit target, all five sequential fresh
Lean elaborations, and reconciliation of the actual fresh axiom output with
the complete public inventory. Every declaration uses only the permitted
foundational axioms `propext`, `Classical.choice`, and `Quot.sound`, or a subset
of them. Exact-head, dependency-revision, source-integrity, and evidence-upload
checks also passed. A cache hit did not replace the fresh owner elaborations:
each fresh owner wrote the `.olean` consumed by the following owners and audit.

Four linter warnings in the fresh owner checks remain: two unused
simplification arguments and two unused-section-instance warnings. A-A and
QA-A reviewed them as nonmaterial to the theorem statements and proofs. The
dependency build also reports warnings in existing imported owners; this is
not a warnings-as-errors certificate.

### Reproduction commands

The successful workflow used the existing serialized focused verifier. From
the repository root, its decisive commands were:

```bash
set -euo pipefail
python3 verification/language-symmetry/check.py exe cache get
python3 verification/language-symmetry/check.py env lean --version
python3 verification/language-symmetry/check.py build \
  InfoGeometry.OperatorAlgebra.HorizonCompressionPairingAudit

horizon_sources=(
  lean/InfoGeometry/OperatorAlgebra/UnitaryCornerCompression.lean
  lean/InfoGeometry/OperatorAlgebra/TripotentMiddlePairing.lean
  lean/InfoGeometry/OperatorAlgebra/TripotentCornerDynamics.lean
  lean/InfoGeometry/Canonical/HorizonCompressionCounterexamples.lean
  lean/InfoGeometry/OperatorAlgebra/HorizonCompressionPairingAudit.lean
)
for horizon_source in "${horizon_sources[@]}"; do
  horizon_relative="${horizon_source#lean/}"
  horizon_output="$PWD/verification/language-symmetry/.lake/build/lib/lean/${horizon_relative%.lean}.olean"
  mkdir -p "$(dirname "$horizon_output")"
  python3 verification/language-symmetry/check.py env lean --root="$PWD/lean" \
    -o "$horizon_output" "$PWD/$horizon_source"
done
```

The workflow separately checks source/audit inventory equality, exactly one
actual axiom record for each public declaration, and the allowed axiom set.
Its source is `.github/workflows/horizon-compression-pairing.yml`; the public
job logs and uploaded evidence retain the results.

### Verified source manifest

These hashes identify the compiled owners and audit. The later documentation
record update does not change these sources, the verifier, workflow, or pins.

| Source under `lean/InfoGeometry/` | SHA-256 |
| --- | --- |
| `OperatorAlgebra/UnitaryCornerCompression.lean` | `7a058ead23a482eea743bf923ae54c7555118accb21cb3147dba872036bbb86c` |
| `OperatorAlgebra/TripotentMiddlePairing.lean` | `d2c6e7849262ad8a411101ed0e47bc14c94f921ce7226abadb5857e6f4263306` |
| `OperatorAlgebra/TripotentCornerDynamics.lean` | `643675a2c37593a3d7425960439e14bb6279b8d2f584e4b0d45808c50de6b589` |
| `Canonical/HorizonCompressionCounterexamples.lean` | `53b703e33539d5b6a63eb3778d9d3706f7c2fa57a3555230fc1979c372920d62` |
| `OperatorAlgebra/HorizonCompressionPairingAudit.lean` | `4d341a0a61aa6c6f84207544b161261e4e8b6dacb1f0e87b6c77b5fdcc3766bd` |

### Independent static checks

- Strict refutation of all six changed Lean files: exit 0, no reported traps.
- Static Gate 4 on the five new Lean files: exit 0, explicitly
  `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`. Its static result is distinct from
  the compiler evidence above.
- Warning-strict semantic-vacuity scan: exit 1, with 13 `trivial_surface`
  warnings. Independent QA inspected the direct compression laws, projector
  adjoint formulas, and dense-frame calculations and found no vacuous premise
  or carrier substitution. The warnings and short proofs remain visible.
- Complete declaration/audit inventory, dependency-pin integrity, and
  `git diff --check`: passed.

QA-A independently repeated these static checks against the unchanged
`f618bcb3a5bce952d7c68ddd82f04dfe33e0e573` checkout, checked the full committed
diff against the implementation base, and verified all nine focused dependency
revisions. It reproduced exactly the same 77-declaration inventory and 13
reviewed semantic warnings. No local compiler was started and no tracked
source was changed during that independent cycle.

### Integration scope and remaining constraints

The existing focused `verification/language-symmetry` project is reused with
explicit targets. Its missing `DAG` library registration is added because the
selected native owner closure imports `DAG.Basic`. Its cache command runs from
the focused project directory so dependency archives hydrate that project's
package paths; source checks retain the repository-root working directory and
shared lock. CI uses the pinned focused manifest without local package-location
overrides.

A focused build does not certify the root package or `InfoGeometry.All`.
The root path preflight
`python3 tools/infra/ci_bootstrap.py paths --report <report.json>` returned exit 1
on 12 November 2026: the HomotopyHypothesis and Atlas path dependencies lack
sources/configuration, and the GIFT gitlink is uninitialized. These preexisting
root-package constraints are outside this change.

Two inspected general CI jobs also fail before their Lean checks: the
[style job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43194302403/job/131101170393)
reports the existing `PellisFineStructure.lean` / `PellisfineStructure.lean`
case collision, and
[reviewed integration](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43194302456/job/131101170890)
reports the missing submodule URL
for `external_refs/auto-ontology`. The two colliding files, `.gitmodules`, and
that gitlink are unchanged by this branch. These observations do not diagnose
all other repository workflows.

The branch remains a draft under the previously authorized publication
exception for those existing integration constraints. It is not merged and
does not claim that the root pre-push gate or whole-repository CI passed.
