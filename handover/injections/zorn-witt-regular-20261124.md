# Zorn primal–dual regular operators: source and theorem contract

## Intake and provenance

- Source: the user's 2026-11-24 mathematical narrative and attached
  `Pasted text(20261124-084336).txt`.
- Exact attachment: `zorn-witt-regular-20261124-intake.txt` beside this record.
- Attachment SHA-256:
  `cf125e1522387dee1f391edeb82e4fd06e197465858685761b385c133d7383c6`.
- Source baseline: `66b240304293c9a99ae996d7c6714b558cbacf75`, the published
  head of PR #437, `codex/neutral-legendre-pauli-20261124`.
- Proposed branch: `codex/zorn-witt-regular-20261124`.
- Classification: finite representation-level algebra, risk R4 because the
  source multiplication is nonassociative. Statements that the attachment
  was already checked are intake claims, not compiler evidence.
- Roles: root authors/integrates the regular-norm owner and verification
  entrypoint; `audit_math` generates the isolated Witt-coordinate and exact
  determinant candidates;
  `source_scout` independently reviews the mathematical source and scope;
  `final_qa` performs independent acceptance checks. No author accepts their
  own proof packet.

The preserved attachment is evidence, not an instruction file or a promoted
Lean source. Its duplicate carrier and proof script are not installed.

## Formal objects and conventions

The carrier is the existing `InfoGeometry.Canonical.ZornMatrix ℝ`. Its module
structure and product come from `Canonical/ZornSpinor.lean`. The operator is
the existing `Lie.SplitOctonionEllCircularPeirceBasis.leftRegularRepresentation`
from `Lie/CanonicalZornRegularOperators.lean`, a linear map into
`Module.End ℝ (ZornMatrix ℝ)`. Endomorphism multiplication is composition.
The source product is not assumed associative.

The existing `Canonical.ZornClifford.zornNormFun` is
`a * b - dot x y`; its `zornConj` swaps `a,b` and negates both spatial slots.
The real four-vector pairing is the existing
`Lie.SplitOctonionWittVectorCovectorBridge.wittPairing`:
`x₀p₀ - (x₁p₁ + x₂p₂ + x₃p₃)`.

The four-vector-to-Zorn map is to be composed from the existing
`SplitOctonionWittPairingTransportBridge.toCoord` and
`canonicalToCoord.symm`. This is an actual linear equivalence, not a new
carrier or a new multiplication. Primal and dual elements are its values on
`(x,0)` and `(0,p)`. Hyperplane incidence uses the existing native functional
`toDualPlus p` and `LinearMap.ker`. The kernel is a proper hyperplane only
when `p ≠ 0`; at `p = 0` it is the whole four-dimensional space.

This is the Cartesian/diagonal Zorn identification in the attachment. It is
distinct from the separate Ell-circular Peirce frame; no equality of those
two basis transports is assumed.

An 8-by-8 matrix is `LinearMap.toMatrix b b` of the existing operator for an
actual `Module.Basis (Fin 8) ℝ (ZornMatrix ℝ)`. A basis change preserves the
determinant. No coordinate matrix is substituted for a different operator.

## Claim ledger

| Intake atom | Current owner or exact correction | Packet treatment |
| --- | --- | --- |
| Additive and module structure on split octonions | `Canonical.ZornMatrix`, transported from product coordinates | Reuse; no new instances |
| Full-carrier linear lift is injective | `leftRegularRepresentation_apply_one`, `leftRegularRepresentation_injective` | Reuse; this is linear injectivity |
| Two dual four-vectors give eight Zorn coordinates | Existing `toCoord` and `canonicalToCoord` equivalences | Compose them and prove the norm/regular-action readouts |
| Norm equals the primal–dual Lorentz pairing | Existing `zornNormFun`, `wittPairing`, and native coordinate equivalences | Prove their compatibility |
| General polarized left alternativity | `ZornVectorMatrix.associator_left_alternative`, existing vector-carrier `ZornLeftCAR.leftMultiplication_anticommutator`, canonical `canonical_left_linearized` | Expose the needed canonical regular-operator laws without a new operator |
| Chiral squares give nilpotents/idempotents | Actual canonical source product on the two selected four-planes | Prove `L_X²=x₀ L_X` and `L_P²=p₀ L_P` |
| Cross anticommutator is a scalar for general four-vectors | False without removing time/idempotent terms | Prove `L_X L_P + L_P L_X = x₀ L_P + p₀ L_X - η(x,p) I` |
| Conjugate contractions | `ZornClifford.mul_zornConj_mul`, `zornConj_mul_mul` over a commutative ring | Package both as equalities in native `Module.End` |
| Operator is invertible iff pairing is nonzero | Field-specific consequence; not valid from nonzero alone over arbitrary rings | Prove over ℝ, with explicit inverse and an incidence-kernel consumer |
| Singular iff incidence | Native matrix unit/determinant equivalence plus the unit theorem | Prove the exact zero-set statement |
| `det(L_Z)=N(Z)^4` | No exact owner found in the bounded source search; imaginary owner proves only `det(L_X)^2=Q(X)^8` | Added source-reviewed candidate `CanonicalZornRegularExactDet`; kernel validation is pending, and singularity does not assume this formula |
| Seven imaginary left actions yield a Clifford representation | `SplitOctonionCliffordAction.splitOctonionLeftCliffordRepresentation` | Reuse the actual `CliffordAlgebra` algebra homomorphism |
| Full `Cl(4,3)` action in `M₈(ℝ)` is faithful | Countertheorem `splitOctonionLeftCliffordRepresentation_not_injective`: source dimension 128, target dimension 64; kernel dimension at least 64 | Reject full-algebra faithfulness; keep generator-map injectivity |
| Nonassociativity disappears in operators | False: composition is associative but `L_a L_b = L_(ab)` generally fails | Reuse the associator-defect owners |
| Displayed defect on `(q₄,q₅,q₆)` is `+2q₇` | With the attachment's cross product and `q₇=U₋−U₊`, it is `−2q₇` | Correct the sign; the attachment's weaker inequality remains mathematically valid |
| Three negative-square left operators form a quaternion triple on the full module | The quaternion composition law is stronger than pairwise anticommutation; `ZornLeftCAR.gamma_operator_product_ne` supplies a counterexample | Describe three anticommuting real complex structures; do not infer the full-module quaternion relation |
| Minkowski, Euclidean, and neutral signatures are interchangeable | Full norm has signature (4,4); diagonal restriction is (1,3); spatial parity matched restriction is positive definite | State the chosen subspace/map; do not identify these forms globally |
| Point/momentum interpretation is a physical law | No dynamics or physical model supplied | Interpretation only |

The noninjectivity correction is already carried by
`Lie/SplitOctonionCliffordNoninjective.lean`, including
`leftClifford_finrank`, `canonicalZornEnd_finrank`, and
`splitOctonionLeftCliffordRepresentation_kernel_finrank_ge`. It is not a new
classification theorem in this packet.

## Smallest missing implications and consumers

1. `CanonicalZornRegularNorm`: lift existing source-level identities through
   the existing regular representation; prove an explicit conjugate inverse
   when the real norm is nonzero, its converse, and the determinant zero set.
2. `CanonicalZornWittRegularBridge`: compose existing equivalences; specialize
   norm, chiral squares, the true mixed anticommutator, invertibility, and
   singularity to the primal–dual pairing and the kernel of `toDualPlus`.
   A closed chiral-sum defect computes the corrected coefficient `−2`
   on the actual eight-dimensional carrier, and a closed upper/lower pair
   witnesses noncommutative operator composition.
3. `CanonicalZornRegularExactDet`: derive the actual native left matrix in
   the existing Cartesian basis, expand its sparse determinant one size at
   a time, and use native basis independence to obtain `N(Z)^4` in any
   genuine eight-element basis. This candidate includes the null cone.

The proof dependencies run from native multiplication and conjugation to the
regular-operator identities; from these to units/singularity; and from the
existing coordinate/duality equivalences to incidence. The full Clifford
noninjectivity result is a separate dimension argument. Neither geometric
analogy nor the requested determinant formula is used as an unproved edge.

## Explicit scope boundaries

No new octonion carrier, no associative ring instance on it, no complex scalar
unit, no new Clifford quotient or faithful full-Clifford embedding, no physical
momentum law, no affine normalization, no manifold/Grassmannian construction,
and no determinant fourth-power theorem was claimed by the initial contract.
The later exact determinant candidate is recorded below; its source review
does not establish kernel acceptance.
The native signature convention is the quadratic-square convention: four
positive and three negative imaginary generators. A scalar pairing on two
four-vectors does not make every full Zorn operator an imaginary Clifford
generator.

## Verification record

Initial disposition: **PENDING**. The source baseline is clean and matches the
published PR #437 tree. A nonblocking maintained-lock probe at
2026-11-24 08:48:16 UTC returned `BuildLockBusyError`; the external owner was
`shared-formalism:2`. No new Lake invocation has occurred at contract creation.
All nine pinned package HEADs, URLs, and clean working trees passed read-only
preflight; no packages are copied or changed. This is environment evidence,
not compilation or theorem acceptance.

Final source hashes, independent reviews, exact gate commands, actual compiler
and axiom-audit results, and any remaining blockage will be appended after
the candidate is fixed and checked.

### Exact determinant candidate added after the initial contract

The first two new owners passed independent source review and six static gates
in run-001. The exact determinant was initially separate proof debt. A complete
two-theorem candidate was then generated in an isolated file and independently
reviewed by `source_scout`. The native matrix signs and pinned matrix/determinant
API calls passed that source review. A required parser repair moved the scoped
heartbeat option before the theorem documentation comment; the mathematical
statement and proof body are unchanged. The repaired source was integrated as
`Lie/CanonicalZornRegularExactDet.lean`.

The scoped limit of 1,200,000 heartbeats is a bounded proposal, not a measured
runtime guarantee. All three new owners require fresh compilation and an axiom
audit. The expanded checker selects four owners with 27 public heads and ten
named upstream declarations: 37 expected records, zero observed at this point.
The determinant zero-set and incidence proofs remain independent of this new
finite determinant calculation.

### Independent run-002 source/static receipt

Disposition: **QA_BLOCKED for kernel acceptance; source/static checks PASS**.
The final frozen-snapshot comparison completed at 2026-11-24 09:12:31 UTC.
All eight staged files, the unchanged Clifford boundary owner, and all
control files matched the reviewed snapshot and index. There were no
unstaged differences. The three new owners contain 22 theorem candidates
with complete proof bodies and one linear-equivalence definition.

- Independent mathematical/source review: PASS for all three new owners.
- Six static gates: all exit 0 across all four selected owners.
- Forbidden proof constructs, vacuity warnings, semantic-content findings,
  and OpenGauss findings: all zero in the selected sources.
- Independent inventory: 9 + 12 + 2 + 4 = 27 owner heads, plus ten reused
  declarations; 37 expected axiom records and zero observed records.
- Workflow delta: only the exact-determinant trigger path was added. Every
  executable block is byte-identical to the run-001 syntax-checked version.
  That earlier review passed YAML parsing, five shell syntax checks, and
  two embedded Python syntax checks. No actionlint result is claimed.
- Verifier delta: one target and the corresponding docstring count; existing
  gate semantics and the reused verifier defaults are unchanged.
- Fresh Lean elaborations, Lake invocations, axiom checks, and root integration:
  zero in both local QA runs. No compiler was queued or launched.

Run-001 recorded an active external shared-lock holder at 09:04:31 UTC
(`legendre-incidence:2`). Run-002 did not repeat that probe or infer that the
same holder remained active. This is a local validation blockage, not a
proof failure and not theorem acceptance. The GitHub workflow will provide
the next actual compiler evidence for the published revision.

Exact static commands (repository-root working directory):

```bash
python3 tools/quality/proof_proxy_staged_gate.py --strict lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean lean/InfoGeometry/Lie/CanonicalZornWittRegularBridge.lean lean/InfoGeometry/Lie/CanonicalZornRegularExactDet.lean lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean
python3 tools/quality/semantic_vacuity_gate.py lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean lean/InfoGeometry/Lie/CanonicalZornWittRegularBridge.lean lean/InfoGeometry/Lie/CanonicalZornRegularExactDet.lean lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean --fail-on error --json-out /tmp/real-dirac-publication-recovery/zorn-intake/qa/run-002/semantic-vacuity.json
python3 tools/quality/semantic_content_audit.py --file-prefix lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean --file-prefix lean/InfoGeometry/Lie/CanonicalZornWittRegularBridge.lean --file-prefix lean/InfoGeometry/Lie/CanonicalZornRegularExactDet.lean --file-prefix lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean --gate --json-out /tmp/real-dirac-publication-recovery/zorn-intake/qa/run-002/semantic-content.json --md-out /tmp/real-dirac-publication-recovery/zorn-intake/qa/run-002/semantic-content.md
python3 tools/infra/opengauss_screener.py lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean lean/InfoGeometry/Lie/CanonicalZornWittRegularBridge.lean lean/InfoGeometry/Lie/CanonicalZornRegularExactDet.lean lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean --strict --json
python3 tools/infra/opengauss_cli.py refute lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean lean/InfoGeometry/Lie/CanonicalZornWittRegularBridge.lean lean/InfoGeometry/Lie/CanonicalZornRegularExactDet.lean lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean --strict --json
python3 tools/infra/opengauss_cli.py review lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean lean/InfoGeometry/Lie/CanonicalZornWittRegularBridge.lean lean/InfoGeometry/Lie/CanonicalZornRegularExactDet.lean lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean --gate GATE_4 --json
```

Frozen implementation hashes:

| Path | SHA-256 |
| --- | --- |
| `lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean` | `3140b8ff4a9f4c9673596e558ea082622c5be70d2c980a723827b161349662f5` |
| `lean/InfoGeometry/Lie/CanonicalZornWittRegularBridge.lean` | `5e0f52cd147dc72b9987349ea26234a6bfb5658027fdbe9327880e761eab2d76` |
| `lean/InfoGeometry/Lie/CanonicalZornRegularExactDet.lean` | `8320933207fc0c8607fc3f5b411d5852681798355527ded68afe3a1cef7c1167` |
| `verification/zorn-witt-regular/check.py` | `4f188ad61f52c45428e3c9a263915f89c6af24ef8442a0dfbc2995c2b28e0c84` |
| `.github/workflows/zorn-witt-regular.yml` | `946840adb9cb136173967920f36c1a6a952fdd923f65d6930d2a665da03e461d` |

Evidence receipt hashes (local independent QA, not compiler evidence):

| Receipt | SHA-256 |
| --- | --- |
| `run-002/static-gate-receipts.json` | `fa4e1d173b0390edc8e581e960ea7318f90b5fc18ec2e74c26b46432ed167764` |
| `run-002/independent-inventory.json` | `792fefcd51c3e21c3d9c5127a59d470663c5d3f268e2b89170e53168575a5dae` |
| `run-002/delta-review.json` | `1f252ba0fb4296c848f7aa7c8619265bc18d96ee3a88a342c2f7e4fdbaa131c6` |
| `run-002/final-inspection.json` | `20e15a6ac202ef2643d158c17d650ed8e11950138ae622f5c39f905fa0149afd` |

The raw attachment remains byte-identical at 22,525 bytes. No dependency
pin, gate implementation, existing source owner, package source, or shared
cache was changed by this packet. Publication for review does not establish
kernel acceptance, root integration, or merge readiness.

### First published CI attempt and checkout repair

GitHub Actions run `45363178386`, job `138338108096`, failed at checkout on
2026-11-24 at 09:16:57 UTC. Source checkout itself succeeded, but
`actions/checkout@v4` then recursively inspected submodules while removing
credentials. It rejected the existing gitlink `external_ref/open-math-harness`
because `.gitmodules` has no URL for it. Toolchain installation, cache hydration,
compilation, and axiom checks were all skipped; no verification artifact was
created. This failure provides no Lean proof result.

The workflow now uses the repository's existing public exact-revision checkout
pattern: initialize an ordinary Git checkout, fetch the trusted `GITHUB_SHA`
without recursing into submodules, check it out detached, and assert exact HEAD
equality. GitHub metadata confirms the repository is public. This requires no
token or persistent credentials and preserves every gitlink, dependency pin,
source file, and proof gate. It also preserves validation of GitHub's PR merge
revision. No missing submodule URL was guessed or installed.

### Actual compiler result and conjugation-zero proof repair

The replacement workflow run `45372272026` checked merge commit
`0677beb96a6caeb25a73b8c7de94b055687ba186`, whose tree
`eabd89fec8438ef8e8fe6b99d579230444c60930` exactly matches the repaired parent
head. Public checkout, Lean 4.34.1 installation, artifact hydration, and
package-source/pin validation passed. The focused build ran from 10:17:55
to 10:27:10 UTC on 2026-11-24 and exited 1.

There was one concrete elaboration error:
`CanonicalZornRegularNorm.lean:122:6`. Simplifying the double-conjugation
equality produced a conjunction of four coordinate equalities, while the
goal remained the structure equality `Z = 0`. The owner also emitted the
`unnecessarySimpa` diagnostic at line 129, which would matter to its later
fresh warning-as-error check. The fresh checks and axiom audit did not run:
37 expected records, zero observed records. The other two new owners could
not be accepted through their failed dependency. All recorded source and
control hashes remained unchanged during this actual run.

The uploaded artifact `14911375401` has SHA-256
`57b8cc4b3afe82eedd28c631214b29c39d563047f03fbea8daf3e62dbe6db398`.
Its build log has SHA-256
`deae7d268573fecb3916a7491b146e93e72cd549145bbec3b468feef11f1f840`.
These are compiler-failure evidence, not acceptance receipts.

`audit_math` produced an isolated two-site source repair and `source_scout`
independently reviewed it: PASS. Root inspected and integrated the exact
candidate. The repaired norm owner has SHA-256
`c8828faadc1a5a83c44a5c88a3cbad26887b403798da5e93cb8ac807e1f0aac5`.
It derives `Z = 0` by the native `ZornMatrix.ext` rule, projecting the two
swapped scalar coordinates and cancelling negation on the spatial coordinates.
The scalar contradiction now uses the compiler-recommended `simp at hscalar`.
All nine theorem statements, hypotheses, imports, and declaration counts are
unchanged. No gate, pin, package source, or cache is changed by this repair.
Fresh validation of the repaired source remains pending.


### Independent static receipt for the two-site CI repair

All six maintained static gates scoped to the changed norm owner returned
exit 0, with zero vacuity, semantic-content, or OpenGauss findings. The final
comparison at 10:32:18 UTC confirmed the repaired source hash, all nine
unchanged theorem statements/imports, required headers, absence of forbidden
constructs, exactly two staged paths, no unstaged differences, and unchanged
captured control/source/index hashes throughout the check. Existing owners
and workflow controls were not modified or unnecessarily rechecked.

Exact commands ran serially from the repository root:

```bash
python3 tools/quality/proof_proxy_staged_gate.py --strict lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean
python3 tools/quality/semantic_vacuity_gate.py lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean --fail-on error --json-out /tmp/real-dirac-publication-recovery/triality-intake/qa/parent-repair-run-001/semantic-vacuity.json
python3 tools/quality/semantic_content_audit.py --file-prefix lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean --gate --json-out /tmp/real-dirac-publication-recovery/triality-intake/qa/parent-repair-run-001/semantic-content.json --md-out /tmp/real-dirac-publication-recovery/triality-intake/qa/parent-repair-run-001/semantic-content.md
python3 tools/infra/opengauss_screener.py lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean --strict --json
python3 tools/infra/opengauss_cli.py refute lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean --strict --json
python3 tools/infra/opengauss_cli.py review lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean --gate GATE_4 --json
```

- `static-gate-receipts.json` SHA-256: `c7f09b54143c8f4d4681c02b103dff167a0521fe11f5158cd45c26791b52e309`.
- `final-inspection.json` SHA-256: `00fb7de6df8502ea94ccb8c74259d845ea73044253814d987c860fdd57a993ae`.

This receipt is a source/static PASS for the exact repair. No local compiler,
new lock probe, workflow rerun, or axiom audit occurred in this static lane.
A new published CI run must establish whether the repaired proof elaborates
and whether dependent owners and all 37 axiom records pass.

## Second compiler receipt and block-determinant repair

The current-head focused run `45375944598`, job `138382168259`, actually built
the repaired norm owner with SHA-256
`c8828faadc1a5a83c44a5c88a3cbad26887b403798da5e93cb8ac807e1f0aac5`.
It then failed in the determinant owner: the original matrix readout exceeded
the default 200,000-heartbeat budget, and the Laplace expansion exceeded its
1,200,000-heartbeat budget at the five-dimensional minors. The Witt owner
built with six tactic warnings at four source sites. Fresh warning-as-error
checks and the 37-record axiom audit did not run.

Artifact `14914884707` has SHA-256
`7a81db59661cc8b07c473725594b132327e729ef3ac1f9f5540487a6d626b077`.
Its build log has SHA-256
`edd544f2e7b0d54d5f17e3fa9a8fe84c589bf049fc15320fb892b2b4532e7470`.
The CI recorded tree `ca50c2b1c781ae8e6a1184d31e84909b9a79cd91`, matching
the parent head under review.

Root replaced the determinant proof with exact finite block algebra, and
`source_scout` independently reviewed the candidate. The actual matrix is
`[[a I₄, B], [C, b I₄]]`, with a direct proof of `C * B = (x · y) I₄`.
For `a ≠ 0`, multiplying on the right by `[[I₄,-B],[0,a I₄]]` gives a
block-triangular matrix; cancellation of `a^4` yields the determinant.
For `a = 0`, the signed exchange `[[0,-I₄],[I₄,0]]` has determinant one and
reduces the calculation to `det(-C * B)`. Both branches give the fourth
power of the native norm. No corner invertibility assumption, analytic
limit, or raised heartbeat budget remains. The operator-to-matrix proof now
compares the action on arbitrary coordinate vectors in eight rows.

The determinant candidate SHA-256 is
`ad1e4526d472b76e0097e2d248058713dde64fb697c095a2e2b39c15a437acbe`.
Both public theorem statements are unchanged. Private helpers expose the
block calculation locally, and the native Mathlib Schur-complement import
supplies the determinant of a block matrix with identity in its first corner.

`source_scout` repaired exactly the four reported Witt proof-script sites;
`audit_math` independently reviewed the delta. Scalar `simp`/`ring` steps
are sequential and the two unreachable vector `ring` tails are removed.
Its SHA-256 is
`4db8f9c4dd672a1f0b2d57224a659970d4ad688c1857c7ed7f299fc700fb15bb`.
All public statements, hypotheses, and counts are preserved.

A local pinned-runtime feasibility check at the unchanged prior snapshot
did not produce a theorem result. The first launch was stopped by an
inherited allocation bound before elaboration; a second launch under normal
limits exited with SIGKILL after 131 seconds, before emitting a module
result. QA sent no termination signal to the started Lake. The recorded
maximum waited-child RSS does not establish the cause of SIGKILL. Both
temporary packages-directory overrides were restored byte-for-byte; all
nine package revisions, URLs, clean-source checks, and source/control hashes
remained correct. No axiom records were observed. These are infrastructure
outcomes, separate from the new proof candidates' pending kernel acceptance.

### Explicit matrix noncommutativity

The first static run on the block refactor found T16 on its private Cartesian
matrix helper. Semantic vacuity/content were clean, while four of the six
gates rejected the missing closed matrix witness. The response adds the
actual upper-zero and lower-zero chiral left-action matrices: `(A * B) 0 0`
is one and `(B * A) 0 0` is zero. Two equality fields identify these witnesses
with the native basis-dependent `LinearMap.toMatrix` expressions.

`source_scout` authored the isolated insertion, and root and `audit_math`
independently reviewed it. The updated determinant owner SHA-256 is
`43bfb3117e2076450d387ca2f0aa731444463bb44568dcd51b05e25293f4059d`.
All preceding candidate bytes are preserved. Its two existing statements
remain unchanged and one new theorem records the actual noncommutativity.
The packet now has 28 public owner heads plus 10 reused declarations,
therefore 38 expected axiom records. No gate criterion was changed.

The second run confirmed that the maintained gate requires a witness for
each concrete matrix carrier used by products. The eight-dimensional witness
does not cover the four-dimensional off-diagonal blocks. A second closed
theorem therefore uses the actual upper blocks for `chiralUpperBasis 0` and
`chiralUpperBasis 1`; their ordered products differ at entry `(1,2)` by one
versus zero. Its two equality fields expose the exact four-by-four matrices.
Root independently reviewed `source_scout`'s isolated 16-line insertion.
The final determinant-owner SHA-256 is
`746827d3e234185eeb0c6b724c18ee7e916acee63498ca5325ac56031efdbf00`.
The original two public statements are still unchanged. There are now
29 public owner heads plus 10 reused declarations: 39 expected axiom records.

### Final static disposition for this repair

Run 003 passed all six maintained gates on the two changed owners: strict
proof proxy, semantic vacuity, semantic content, strict OpenGauss screener,
strict refutation scan, and static GATE_4. All commands returned zero, with
zero vacuity/content findings and zero screener traps. The frozen comparison
confirmed the source/control bytes, four staged paths, and the unchanged
original public statements. The independent inventory confirmed 29 owner
heads plus 10 reused declarations, 39 expected and zero observed axiom
records. Report SHA-256:
`83bdd312fe6ef907f228c7847e1b2c3c0511eb114bd26e76e5eac3524e4fea47`.

This is static acceptance of the exact source hashes above. Fresh compiler
and axiom acceptance of the structural repair remain pending. No verification
gate, dependency pin, package source, or shared-cache policy was changed.
