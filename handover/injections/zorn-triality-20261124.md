# Real Zorn Clifford faithfulness, infinitesimal triality, and derivations

## Frozen intake and scope

Source: the user's attached `Pasted text(20261124-100242).txt`, 10,981 bytes,
SHA-256 `c9797ebd16fbf315a70670359e68b973be892a3b607dbe6f0f36305508e08636`.
The exact text is preserved beside this contract. It is evidence, not promoted
Lean code or an instruction file. The source baseline is published PR #441,
commit `4c45f2bd932592fa86820f2e3360085f9e060c38`; the additive CI checkout
repair is published at `461226dbffc3a0b7149115a87a7ae1b690098f04`, which is the
extension branch base. The branch is `codex/zorn-triality-20261124`.

This is finite real algebra on the existing canonical eight-dimensional Zorn
carrier and its doubled sixteen-dimensional real module. The risk class is R4
because nonassociative multiplication, Clifford faithfulness, and triality
must be distinguished. No physical or analytic dynamics is inferred.

## Exact conventions

The canonical product has minus the lower-vector cross product in its upper
slot and plus the upper-vector cross product in its lower slot. The intake
uses the opposite pair of signs. The existing linear equivalence
`ZornPinorReconstruction.orientation` negates BOTH spatial slots and satisfies
`orientation_sourceProduct`; this is a transport between products, not an
automorphism of a single fixed product. It preserves the reduced norm.

The transported source quaternion units are `lower_i - upper_i`; the source
hyperbolic units are `-(upper_i + lower_i)`. Their norm signs are +1 and -1,
respectively, while their element squares have the opposite signs. The native
Dirac gamma has conjugate off-diagonal blocks and squares to the norm. Its
signature is therefore (4,4), separately from the undoubled imaginary-left
action of Cl(4,3) on the eight-dimensional module.

## Existing owners and smallest missing implications

- Reuse `Canonical.ZornMatrix`, `ZornClifford.zornNorm`, `.zornConj`,
  `.diracGammaLinear`, `.diracGamma_sq`, and `.zornCliffordRepresentation`.
  The existing representation is a genuine algebra homomorphism obtained from
  Mathlib's universal Clifford algebra. No new carrier or gamma is created.
- Reuse `Lie.SplitOctonionEllCircularPeirceBasis.leftRegularRepresentation`
  as the native left action and curried bilinear product.
- Use the existing quadratic form's `polarBilin`; its value is the UNHALVED
  polarization N(x+y)-N(x)-N(y), exactly the intake convention.
- Construct the missing real bivector endomorphisms with the intake factors:
  vector action one half of the polar wedge, and chiral spin actions one
  quarter of the two conjugate-left commutators.
- Prove the actual product law TPlus(a,b)(v*s) = TV(a,b)(v)*s + v*TMinus(a,b)(s),
  and construct the existing `CompositionTriality.TrialityTriple` with fields
  (TPlus, TV, TMinus). Prove norm-skewness explicitly; membership in the generic
  triality carrier alone does not imply orthogonality.
- Reuse `ZornVectorMatrix.matrixDerivation M htrace` and the lightweight
  `CanonicalZornDerivation.vectorToCanonicalEnd` transport. The rotation and
  boost correspond to matrices [[0,1,0],[-1,0,0],[0,0,0]] and
  [[0,-1,0],[-1,0,0],[0,0,0]]. Prove equalities from the triality combinations
  to these existing derivations, plus the exact action/square witnesses.
- The intake theorem labelled faithful proves only square and CAR relations.
  To prove the stronger claim, construct a norm isometry to the existing
  split-Clifford tower through native Witt/neutral coordinates; compose with
  `splitTowerEquivMatrix 4`; transport matrix-ring simplicity; prove injectivity
  of the EXISTING real Zorn Clifford representation. Equal dimensions alone
  are not used as an injectivity argument.

## Claim classification

| Intake claim | Treatment |
| --- | --- |
| Chiral product/sign audit and primal-dual norm | Reuse exact source-product orientation and existing basis/norm owners |
| Left/right alternativity and conjugate contractions | Reuse existing source identities; no second L/R API |
| Doubled gamma square and CAR | Reuse existing square theorem; derive native polarization |
| Faithfulness of full real Cl(4,4) action | Explicit isometry/simplicity proof source constructed; kernel validation pending |
| Infinitesimal triality with factors 1/4 and 1/2 | Native proof source constructed on existing operators; kernel validation pending |
| TV is norm-skew | Prove scalar identity and use native skew-adjoint structure if direct |
| D12 and B12 are derivations | Identify with existing trace-zero matrix derivations |
| D12 squared is -I and B12 squared is +I everywhere | Not asserted: intake checks their action on one indicated quaternion axis; the full operators kill scalar poles |
| G2 group classification / exponentiated action | Outside this packet; finite derivation membership is the target |

## Roles and verification

`audit_math` audits the intake then generates the isolated real triality owner.
`source_scout` searches owners then generates the isolated faithfulness owner.
Root integrates and generates the explicit derivation consumer. Each source is
reviewed by a different actor from its author. `final_qa` owns the serialized
verification lane. No proof holes, custom axioms, native_decide, unsafe bypass,
or altered dependency pins are permitted.

Initial status: PENDING. The prior PR's first CI failed in checkout credential
cleanup before Lean ran. A fresh local nonblocking lock probe at 10:04:50 UTC
found an active external holder. Neither observation proves or refutes any
mathematical statement. Exact source hashes, independent reviews, commands,
compiler results, and axiom records will be appended for the final snapshot.

## First reviewed source snapshot

The three focused owners are integrated with no new Zorn carrier, product,
gamma action, or dependency pin. All statements are source candidates until
the focused compiler and axiom checks accept the exact snapshot.

| Owner | SHA-256 | Public declarations | Independent source review |
| --- | --- | --- | --- |
| `Canonical/ZornInfinitesimalTriality.lean` | `38828721a6dd15ccaa5f5e672299ce0be595caf92e50ae30508946c9acb6b610` | 4 definitions, 10 theorems | `source_scout` reviewed `audit_math`'s candidate: PASS |
| `Canonical/ZornCliffordFaithful.lean` | `0983f81dee30ff0d7c5ccdce53531b3638e464f1e37ff8b26546955343983cb2` | 5 definitions, 10 theorems | `audit_math` reviewed `source_scout`'s candidate: PASS |
| `Canonical/ZornTrialityMatrixDerivations.lean` | `126a8d1e97defa39b50f29a20c320f9dd4c1b59052e6390daaa1ababa8dbaf66` | 2 definitions, 18 theorems | `source_scout` reviewed root's final candidate including the two axis transports: PASS |

The exact full representation is upgraded with `AlgEquiv.ofBijective` and
`zornCliffordEndEquiv_apply` identifies it with the existing algebra map on
every element. The matrix classification establishes simplicity first;
dimension equality is used only for surjectivity. The triality triple has the
actual product-law proof, and the two explicit derivations are identified
with the native trace-zero matrix constructor. These independent semantic
reviews are not compiler receipts.

The focused checker selects these three owners and the unchanged full
Cl(4,3) noninjectivity owner. Its planned inventory is 53 owner heads and
18 reused declarations, hence 71 expected axiom records. Actual records and
outcomes must be read from the fresh runner report.

At 10:16:53 UTC the parent replacement workflow run `45372272026` had passed
exact public checkout, revision recording, cache restore, and toolchain
installation and was hydrating pinned artifacts. The initial checkout defect
was therefore repaired in execution; no Lean acceptance had yet been observed.

## First independent static run

Run-001 completed serially at 10:19:29 UTC, with final snapshot comparison at
10:20:51 UTC. Four of the six gates failed on one concrete issue: T16 required
a closed noncommutativity witness for the real 3-by-3 coefficient matrices in
`ZornTrialityMatrixDerivations`. The proof-proxy gate, OpenGauss screener,
refutation scan, and GATE_4 returned exit 1. Semantic vacuity and semantic
content returned exit 0. The GATE_4 reports on other selected owners propagated
the same staged-hook failure; they did not identify independent source traps.
No gate implementation or criterion was changed.

The source inventory independently confirmed 53 owner heads and 18 reused
declarations, with zero observed axiom records. There were no forbidden proof
constructs. Five nonblocking vacuity warnings concern definitional application
readouts: four native operator/block equations and the equality identifying
the upgraded algebra equivalence with its original action. The checker API
and AST, YAML, six shell blocks, and two embedded Python blocks passed their
static checks. All eight staged paths and preserved control hashes matched
the inspected worktree; the raw attachment matched its source byte-for-byte.
No Lean compiler was launched or queued in this run.

The response is to add actual noncommutativity proofs for the rotation and
boost, including their commutator on a native axis and a closed certificate
for the exact two coefficient matrices. These are mathematical additions,
not a relaxation of the gate. The next snapshot must be independently
reviewed and checked before a successful static disposition is recorded.

Independent configuration review also approved four added workflow trigger
paths: the existing Witt pairing transport, Clifford action, Zorn vector
matrix owner, and root `lakefile.lean`. This changes trigger coverage only;
all executable workflow blocks, dependency pins, and gate semantics remain
unchanged.

## Noncommutativity repair snapshot

`audit_math` generated three additional theorems in an isolated candidate and
`source_scout` independently reviewed the exact delta: PASS. Root also
inspected the insertions and integrated the candidate with both old and new
source hashes checked. Every preexisting line of the derivation owner is
preserved. Its new SHA-256 is
`62b21451b69ea70cad4056a04715170a0629e0e456905909fea0418c1cf86a43`.
The triality and faithfulness owner hashes above remain unchanged.

The additions establish the following exact source statements:

- A closed real `Matrix (Fin 3) (Fin 3)` noncommutativity certificate whose
  two witnesses are fixed by equalities to the existing rotation and boost
  coefficient matrices. Entry `(0,0)` of the two products is -1 and +1.
- The native commutator identity `(D * B - B * D) q[0] = (-2 : ℝ) • f[0]`.
- `D * B ≠ B * D` in `Module.End ℝ (ZornMatrix ℝ)`, witnessed by upper
  coordinate 0 on `q[0]`, where the two actions give +1 and -1.

No full coefficient-matrix commutator equality is asserted by the first
theorem; its one-entry witness suffices for noncommutativity. The native
operator theorem retains the actual noncommutative action on the complete
eight-dimensional carrier. Zorn multiplication is still not assumed
associative.

The repaired derivation owner has 21 theorems and two definitions. The new
packet therefore has 41 theorems and 11 definitions; including the four
existing noninjectivity declarations gives 56 owner heads. With 18 reused
declarations the new expected axiom inventory is 74, still with zero observed
records at this source-review stage. The repaired static run is pending.


## Final independent source/static receipt

Run-002 completed with all six scoped static gates at exit 0. The final
snapshot comparison at 2026-11-24 10:24:44 UTC confirmed all eight staged
paths and every captured source/control hash matched the inspected worktree
and index. There were no unstaged differences. The three parent Lean owners
also remained byte-identical to their previously reviewed hashes.

Disposition: **source/static PASS; QA_BLOCKED for local kernel acceptance**.
The single T16 blocker from run-001 is resolved by the added mathematical
witnesses. Semantic-content findings and OpenGauss violations are zero. The
same five nonblocking lexical warnings concern definitional application
readouts; the independent source review explains their actual scope.
GATE_4 reports `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`.

The independently computed inventory is 56 public owner heads plus 18
separate reused declarations: **74 expected records and zero observed
axiom records**. There are no forbidden constructs in the selected sources.
The four added trigger paths all exist; every executable workflow block is
byte-identical to run-001's syntax-checked version. Existing pins, shared
verifier defaults, gate implementations, and control files are unchanged.

A fresh maintained nonblocking lock probe at 10:24:12 UTC returned BUSY,
with external owner `real-matrix-split:83`. No build was queued or compiler
started. The pinned runtime exists, but approximately 840 MB free in `/tmp`
and 805 MB in `/workspace` also constrain a fresh local dependency build.
No shared cache, package source, or lock holder was modified. This is an
observed local execution blockage, not a proof failure or theorem acceptance.
The parent remote workflow is a separate packet and cannot certify this one.

Exact static commands, run serially from the repository root:

```bash
python3 tools/quality/proof_proxy_staged_gate.py --strict lean/InfoGeometry/Canonical/ZornInfinitesimalTriality.lean lean/InfoGeometry/Canonical/ZornTrialityMatrixDerivations.lean lean/InfoGeometry/Canonical/ZornCliffordFaithful.lean lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean
python3 tools/quality/semantic_vacuity_gate.py lean/InfoGeometry/Canonical/ZornInfinitesimalTriality.lean lean/InfoGeometry/Canonical/ZornTrialityMatrixDerivations.lean lean/InfoGeometry/Canonical/ZornCliffordFaithful.lean lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean --fail-on error --json-out /tmp/real-dirac-publication-recovery/triality-intake/qa/run-002/semantic-vacuity.json
python3 tools/quality/semantic_content_audit.py --file-prefix lean/InfoGeometry/Canonical/ZornInfinitesimalTriality.lean --file-prefix lean/InfoGeometry/Canonical/ZornTrialityMatrixDerivations.lean --file-prefix lean/InfoGeometry/Canonical/ZornCliffordFaithful.lean --file-prefix lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean --gate --json-out /tmp/real-dirac-publication-recovery/triality-intake/qa/run-002/semantic-content.json --md-out /tmp/real-dirac-publication-recovery/triality-intake/qa/run-002/semantic-content.md
python3 tools/infra/opengauss_screener.py lean/InfoGeometry/Canonical/ZornInfinitesimalTriality.lean lean/InfoGeometry/Canonical/ZornTrialityMatrixDerivations.lean lean/InfoGeometry/Canonical/ZornCliffordFaithful.lean lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean --strict --json
python3 tools/infra/opengauss_cli.py refute lean/InfoGeometry/Canonical/ZornInfinitesimalTriality.lean lean/InfoGeometry/Canonical/ZornTrialityMatrixDerivations.lean lean/InfoGeometry/Canonical/ZornCliffordFaithful.lean lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean --strict --json
python3 tools/infra/opengauss_cli.py review lean/InfoGeometry/Canonical/ZornInfinitesimalTriality.lean lean/InfoGeometry/Canonical/ZornTrialityMatrixDerivations.lean lean/InfoGeometry/Canonical/ZornCliffordFaithful.lean lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean --gate GATE_4 --json
```

Final implementation/control fingerprints:

| Path | SHA-256 |
| --- | --- |
| `lean/InfoGeometry/Canonical/ZornInfinitesimalTriality.lean` | `38828721a6dd15ccaa5f5e672299ce0be595caf92e50ae30508946c9acb6b610` |
| `lean/InfoGeometry/Canonical/ZornTrialityMatrixDerivations.lean` | `62b21451b69ea70cad4056a04715170a0629e0e456905909fea0418c1cf86a43` |
| `lean/InfoGeometry/Canonical/ZornCliffordFaithful.lean` | `0983f81dee30ff0d7c5ccdce53531b3638e464f1e37ff8b26546955343983cb2` |
| `verification/zorn-triality/check.py` | `968902051df6708bc9cd32fe619eee481752296e42978970bd5e8f7ec2cd1dcc` |
| `.github/workflows/zorn-triality.yml` | `76bdb1b31380b7130a47bbf06a3c062e70149342d2ab0b211f70a1ac13bc54a9` |

Independent local receipt fingerprints (not compiler receipts):

| Receipt | SHA-256 |
| --- | --- |
| `run-002/static-gate-receipts.json` | `3584129457e86adee43efc81064f6009eb3ae6f1f717b8725a94f3ad46638d70` |
| `run-002/independent-inventory.json` | `46616c10d4813a18543cb2f3994a8083ef8185cf5d998d3b5503d61182bbde75` |
| `run-002/final-inspection.json` | `1b0f912b17c96ce03361f0b19bd4ec93cc567ce723544b86552f8ad13c53c9d3` |

Fresh elaboration, the actual axiom audit, root integration, and pre-push build
acceptance remain pending. The focused GitHub workflow is the next compiler
lane for this exact packet. Publication is for review and does not establish
kernel acceptance or merge readiness.

## Published parent failure and additive dependency repair

The initial extension was published as PR #447 at
`b52644e3a187674fee664c05ca5eecc95772e723`, with reviewed tree
`45a9dc49e02e6a72aa01361f1e2c04f788fff042`. Its actual pre-commit hook passed.
The first focused extension workflow is run `45374849384`.

The parent's replacement run `45372272026` subsequently failed in actual
Lean elaboration at the conjugation-zero step of `CanonicalZornRegularNorm`.
The original compiler error and artifact hashes, independent source repair,
and six passing static checks are recorded in the parent contract. Parent
PR #441 now contains the additive two-site repair at
`30fb78352e609a860bd6d406f1352a4a863738e1`, tree
`ca50c2b1c781ae8e6a1184d31e84909b9a79cd91`. The repaired norm owner hash is
`c8828faadc1a5a83c44a5c88a3cbad26887b403798da5e93cb8ac807e1f0aac5`.
This extension incorporates that parent through an additive merge; it does
not rewrite the original extension commit or alter any theorem statement.
The new parent focused run is `45375944598`.

The observed pinned-linter diagnostics also motivated a source check of the
new faithfulness owner. The imported, default-on `HaveILetI` linter warns on
tactic `letI` when the remaining goal is a proposition. All six local
bindings in this owner meet that condition. Its pinned documentation states
that ordinary `let` registers local instances, so the isolated repair changes
exactly six `letI` tokens to `let`. Local types and values, imports, all ten
theorem statements, and all five definitions are unchanged; no global instance
is added and no linter is disabled. `source_scout` authored the correction and
`audit_math` independently reviewed it: PASS.

The final faithfulness source hash is
`da3aa065b84246d67063cd9a6b1a7b0fe029c4b0437fcce3142d0226b8b16910`.
This is a source-backed correction for a concrete warnings-as-errors risk,
not an observed compiler result for that owner. The three new owners still
have 41 theorems and 11 definitions; the focused inventory remains 74
expected axiom records. Fresh compilation and actual axiom acceptance remain
pending for the updated extension.


### Final static receipt for the additive dependency update

At 10:36:29 UTC on 2026-11-24 the six maintained static gates scoped to the
changed norm and faithfulness owners had all returned exit 0. Semantic-content
and OpenGauss findings were zero. The one nonblocking lexical warning in
this two-source scope is the existing definitional equivalence-action readout.
The full extension inventory remains 56 owner heads plus 18 reused names,
74 expected axiom records and zero observed records.

Independent comparison confirmed both repaired source hashes, unchanged
public statements/imports/counts, exactly six local-binding token replacements
in the faithfulness source, four staged paths, no unstaged differences or
unmerged entries, merge parent `30fb78352e609a860bd6d406f1352a4a863738e1`, and
unchanged captured source/control/index hashes throughout this check.

Exact commands ran serially from the repository root:

```bash
python3 tools/quality/proof_proxy_staged_gate.py --strict lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean lean/InfoGeometry/Canonical/ZornCliffordFaithful.lean
python3 tools/quality/semantic_vacuity_gate.py lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean lean/InfoGeometry/Canonical/ZornCliffordFaithful.lean --fail-on error --json-out /tmp/real-dirac-publication-recovery/triality-intake/qa/child-update-run-001/semantic-vacuity.json
python3 tools/quality/semantic_content_audit.py --file-prefix lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean --file-prefix lean/InfoGeometry/Canonical/ZornCliffordFaithful.lean --gate --json-out /tmp/real-dirac-publication-recovery/triality-intake/qa/child-update-run-001/semantic-content.json --md-out /tmp/real-dirac-publication-recovery/triality-intake/qa/child-update-run-001/semantic-content.md
python3 tools/infra/opengauss_screener.py lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean lean/InfoGeometry/Canonical/ZornCliffordFaithful.lean --strict --json
python3 tools/infra/opengauss_cli.py refute lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean lean/InfoGeometry/Canonical/ZornCliffordFaithful.lean --strict --json
python3 tools/infra/opengauss_cli.py review lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean lean/InfoGeometry/Canonical/ZornCliffordFaithful.lean --gate GATE_4 --json
```

- `static-gate-receipts.json` SHA-256: `8a2a25c31b9c5cd7295f95bb01976dab4d0bd2858c901243740fbee5f2e4bb50`.
- `final-inspection.json` SHA-256: `bddfeb652faad2bb08c162a1f014f7409f3f23db9a4ff8fa80142d52adc2059a`.

No compiler, lock probe, workflow syntax rerun, or remote job rerun occurred
in this static lane. The updated source is ready for publication and the
fresh focused CI check; kernel and actual axiom acceptance remain pending.
