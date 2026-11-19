# Verification: nonincident pairing and neutral cross duality

## Accepted native scope

The second fresh native run passed, and independent QA recorded
**`ACCEPTED_WITH_LIMITED_SCOPE`** on 2026-11-17. All **39 repository modules**
in the selected dependency closure compiled with exit 0, with **no reused
module artifacts**. The complete-owner axiom audit covered **387 declarations
across nine owners**. The run produced **27 inherited module warnings and
zero introduced warnings**; the axiom audit produced no warnings or errors.

This acceptance covers the frozen source closure and the nine audited
owners. It does not certify a whole-repository build, a rebuild of all
Mathlib from source, or the publication-tree pre-push gate. The exact
mathematical claims and unproved geometric and physical boundaries remain in
[the theorem contract](NONINCIDENT_PARA_TWISTOR_CONTRACT.md).

The authoritative manual decision is the
[independent acceptance record](verification/nonincident-para-twistor-20261117/independent-acceptance.json).
Raw checker, supervisor, and earlier source-review receipts retain their
original statuses, including intermediate pending-review states; they were
not rewritten to manufacture the final decision.

## Source revision and runtime

- Upstream baseline: `08c34e03f610b452e03422037949196dc7d92d6d`.
- Initial restored source commit: `06f9bc1eadb6903781c2c91879f567b732b58b74`.
- First native-attempt source commit: `1b1ecdd405b25a81f0c8177ac405c6cee4de7de1`.
- **Accepted local proof-source commit:** `53c1a356af329891440ca67e8a116570c36a72ab`.
- Lean: `leanprover/lean4:v4.34.1`, compiler commit
  `5045d0056413266e57c625dcd7c365b10e377c52`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Official Linux Lean archive SHA-256:
  `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`.
- Original intake SHA-256:
  `36f218938a18f175c8961fae548b39dfa0fd1ed8e8ae8e0929d3cf2095134799`.

The 36,589-byte intake is preserved unchanged in
[the source text](sources/nonincident_para_twistor_20261116.txt).
The patch adds **32 explicit theorem declarations and seven definitions**.
That source inventory is separate from the 387 declarations in the native
complete-owner audit, which includes existing, generated, and private
owner declarations.

The runtime was recreated from the existing pins. The official archive
digest was checked before extraction, and `lake exe cache get` completed
under the canonical shared build lock. The pinned Mathlib checkout had no
tracked changes. The native run used its isolated copied-source output and
the pinned dependency libraries; the exact import search path is retained in
[native-environment.json](verification/nonincident-para-twistor-20261117/native-environment.json).

### Binding the evidence to source bytes

All 39 source hashes in the
[native report](verification/nonincident-para-twistor-20261117/native-report.json) were checked against the
frozen inputs, copied sources, live sources, and committed blobs at the
accepted local proof-source revision. The four promoted owners also match
the fourth static run and independent v3 source review:

| Promoted owner | SHA-256 |
|---|---|
| `Canonical/ParaComplexNeutralForm` | `ac8ea0b4ec1b2c45bc4995388eedcc27e5ef7e0fd61d862a6181f896dc7ab605` |
| `LinearAlgebra/RegularDyadCompression` | `a85dafe5d2f3fa1114a085500bd0ebf917088f9bd81ae3f545c90f278e30c780` |
| `Optics/SheetWittCircularBasis` | `dcd4fbde48e869da4d03e6512562c245f7162e373df6146a364f7deccd256d69` |
| `Twistor/NonincidentLogPairing` | `57af40272b06c8ce41522c58659d686d9c70dbcfacd42e37511c3217dbdb2cdb` |

The native report's `local_revision` identifies the local proof freeze.
The eventual publication commit may additionally contain documentation and
receipt files. Applicability to that publication is established by matching
its source blobs to the recorded hashes, rather than assuming that a later
commit ID was itself the native compilation input. The final publication
record must retain this source-identity check. Documentation and evidence
packaging do not enlarge the compiled or audited scope.

## Fresh native command and results

The recorded checker command was executed from
`/workspace/scratch/933d64e28eca/repo`:

```bash
/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python3 -u tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/933d64e28eca/runtime/mathlib \
  --lean /workspace/scratch/933d64e28eca/runtime/lean/bin/lean \
  --output /workspace/scratch/933d64e28eca/verification-independent-attempt-2 \
  --target InfoGeometry.Canonical.ParaComplexNeutralForm \
  --target InfoGeometry.LinearAlgebra.RegularDyadCompression \
  --target InfoGeometry.Optics.SheetWittCircularBasis \
  --target InfoGeometry.Twistor.NonincidentLogPairing \
  --target InfoGeometry.Twistor.RealDualTwistor \
  --target InfoGeometry.Twistor.RealProjectiveAmbitwistor \
  --target InfoGeometry.Canonical.ModularZ2CubeGrading \
  --target InfoGeometry.Twistor.TwistorConstituentKinematics \
  --target InfoGeometry.Twistor.TwoTwistorGramMass
```

The invocation contains all nine target arguments and neither
`--incremental` nor `--skip-audit`. The maintained checker copied and hashed
the dependency closure, compiled under the shared build lock, and ran the
complete-owner native audit. Its durable process receipt records exit 0 on
2026-11-17 at 12:02:59 UTC, no received signals, and completion of the owned
process group. The exact invocation, freeze, exit, and supervision evidence
are retained in [supervision.json](verification/nonincident-para-twistor-20261117/supervision.json).

The checker report is `passed` with `audit_required: true`. Every one of the
39 module records has `returncode: 0` and `reused: false`. Independent QA
reconciled the copied-source and compiled-artifact hashes, maintained and
supplemental manifests, dependency graph, target order, pinned runtime, and
unchanged verification helpers.

### Complete-owner declaration audit

Each owner name below has prefix `InfoGeometry.`.

| Audited owner | Native declaration count |
|---|---:|
| `Canonical.ParaComplexNeutralForm` | 88 |
| `LinearAlgebra.RegularDyadCompression` | 29 |
| `Optics.SheetWittCircularBasis` | 48 |
| `Twistor.NonincidentLogPairing` | 53 |
| `Twistor.RealDualTwistor` | 55 |
| `Twistor.RealProjectiveAmbitwistor` | 9 |
| `Canonical.ModularZ2CubeGrading` | 28 |
| `Twistor.TwistorConstituentKinematics` | 36 |
| `Twistor.TwoTwistorGramMass` | 41 |
| **Total** | **387** |

The inventory includes **four private declarations** and generated
declarations. Independent QA reconciled all **407 nonempty audit marker
lines** with the owner inventories and final totals. The complete-owner
enumeration covers the nine owners above; it does not enumerate every
declaration owned by all 39 compiled modules.

The actual collected foundational axioms are exactly `propext`,
`Classical.choice`, and `Quot.sound`, matching the permitted set. Unsafe or
partial selected-owner declarations are rejected by the unchanged audit.
The [raw axiom log](verification/nonincident-para-twistor-20261117/axioms.log) has zero warnings and zero errors;
the [generated audit source](verification/nonincident-para-twistor-20261117/native-audit-source.txt) is preserved.
The checker does not store a separate audit-subprocess exit field: it
requires audit-subprocess success before emitting its passed audited report.
The durable exit-code receipt is therefore the checker process's exit 0,
not an invented additional subprocess receipt.

## Warning provenance and first-attempt correction

The second run emitted **27 module warnings, all inherited, with zero
introduced warnings**. The new logarithmic module emitted no warnings.
The [source-baseline comparison](verification/nonincident-para-twistor-20261117/warning-source-baseline.json)
classifies the closure as 35 modules byte-identical to upstream, three
extended existing owners, and one new owner. Twenty-three warnings occur in
byte-identical whole modules; four occur in preserved original bodies of
the extended dyad and optical owners.

The independent review matched every current diagnostic, its source line,
and its repository prerequisites to the upstream baseline. The 27 inherited
diagnostics also match the completed first attempt after normalizing only
the absolute output-directory prefix. This is source and diagnostic
provenance; no separate upstream baseline compilation is claimed. Complete
module logs are in [module-logs.json](verification/nonincident-para-twistor-20261117/module-logs.json), and the
individual dispositions are retained in the
[independent acceptance record](verification/nonincident-para-twistor-20261117/independent-acceptance.json).

| Native warning category | Count |
|---|---:|
| Deprecated imports | 4 |
| Unused simplification arguments | 10 |
| Unnecessary `simpa` | 4 |
| Unnecessary sequence focus | 1 |
| Unused section variables | 8 |
| **Total inherited warnings** | **27** |

The first fresh attempt at `1b1ecdd405b25a81f0c8177ac405c6cee4de7de1`
compiled its 39 modules and passed the native axiom audit, but independent
QA **rejected** it under the zero-introduced-warning condition. Two diagnostics
reported that the trailing `ring` in `hasDerivAt_logPairing_readout` was
unreachable and unused. Its raw native success was not treated as acceptance.

The reviewed correction removed only `<;> ring` after `field_simp [h]`.
It changed no declaration statement, hypothesis, conclusion, import, or
carrier assumption. The cleanup was committed as
`53c1a356af329891440ca67e8a116570c36a72ab`; fresh static checks, a new freeze,
and the second complete native run followed. Earlier receipts remain
historical evidence for their earlier source bytes. Acceptance of the
current sources comes from the second run and its separate manual decision.

## Independent source review and static checks

Generation, source audit, and final acceptance used separate agent roles.
The independent v3 source review inspected the four final owners, including
actual ordered endomorphism multiplication, derived compatibility fields,
both exact radial biconditionals, the genuine iterated derivative, and the
one-line warning cleanup. Its source-semantic disposition is PASS with
retained advisories. Its original pending-native status reflects the time
of that source review; the later native decision is recorded separately.

The fourth-run [static bundle](verification/nonincident-para-twistor-20261117/static.json) preserves all 15
JSON receipts and raw logs, commands, source hashes, exit statuses,
individual finding dispositions, runtime-bootstrap evidence, and the path
preflight. The four source hashes match before and after that run.

| Static check | Exit | Result retained |
|---|---:|---|
| OpenGauss screener, strict | 1 | Three inherited T17 warnings; zero errors |
| OpenGauss refutation screen, strict | 1 | The same three warnings; zero errors |
| Semantic-vacuity gate, threshold `error` | 0 | Complete four-file coverage; 17 warnings; zero errors |
| Four strict placeholder audits | 0 each | Nine soft findings; zero hard findings |

The strict screens remain **WARN**, because strict mode promotes warnings
to exit 1. No finding was suppressed or relabeled as warning-free. The T17
subjects are the inherited `Datum`, `NondegenerateDatum`, and
`CommutingInvolutions` structures; their nontrivial models and restrictive
hypotheses were examined without adding dummy unconditional inhabitants.

Of the 17 semantic findings, nine concern inherited defining hypotheses,
five are evaluation APIs for constructed maps, two specialize inherited
projector laws, and one derives covariance under the actual contragredient
action. The nine placeholder findings concern six visible section-parameter
declarations and three short proofs. No material vacuity, assumed-conclusion
recycling, or substantive omission relative to the theorem contract was
identified. These dispositions do not erase the raw warnings.

### Source-commit hooks

The installed pre-commit hook recorded `proof_proxy_staged_gate: ok` on all
three local proof-source commits. The exact commands, exit receipts, and
logs are preserved in
[source-commit-hooks.json](verification/nonincident-para-twistor-20261117/source-commit-hooks.json).

| Source commit | Preserved log | Result |
|---|---|---|
| `06f9bc1eadb6903781c2c91879f567b732b58b74` | `initial-commit.log` | Commit exit 0; hook passed |
| `1b1ecdd405b25a81f0c8177ac405c6cee4de7de1` | `proof-repair-commit.log` | Commit exit 0; hook passed |
| `53c1a356af329891440ca67e8a116570c36a72ab` | `warning-cleanup-commit.log` | Commit exit 0; hook passed |

These are pre-commit receipts. The exact publication-commit pre-push result
is a separate obligation.

## Evidence index

All paths below are relative to this document.

| Evidence | Purpose |
|---|---|
| [static.json](verification/nonincident-para-twistor-20261117/static.json) | Fourth-run static receipts, v3 source review, setup and path-preflight evidence |
| [native-report.json](verification/nonincident-para-twistor-20261117/native-report.json) | Second-run targets, 39 module results, source/artifact hashes, counts and axiom summary |
| [axioms.log](verification/nonincident-para-twistor-20261117/axioms.log) | All 407 native audit marker lines |
| [native-environment.json](verification/nonincident-para-twistor-20261117/native-environment.json) | Isolated native import search path |
| [native-evidence-sha256.json](verification/nonincident-para-twistor-20261117/native-evidence-sha256.json) | Maintained native evidence manifest |
| [native-audit-source.txt](verification/nonincident-para-twistor-20261117/native-audit-source.txt) | Exact generated complete-owner audit source |
| [module-logs.json](verification/nonincident-para-twistor-20261117/module-logs.json) | All compiled-module diagnostics |
| [supervision.json](verification/nonincident-para-twistor-20261117/supervision.json) | Invocation, freeze, process completion and independent mechanical inspection |
| [independent-acceptance.json](verification/nonincident-para-twistor-20261117/independent-acceptance.json) | Final scoped manual acceptance and warning provenance |
| [warning-source-baseline.json](verification/nonincident-para-twistor-20261117/warning-source-baseline.json) | Upstream source and prerequisite comparison |
| [bundle-sha256.json](verification/nonincident-para-twistor-20261117/bundle-sha256.json) | Exported evidence-bundle hashes |
| [source-commit-hooks.json](verification/nonincident-para-twistor-20261117/source-commit-hooks.json) | The three source-commit hook receipts |

The second native report SHA-256 is
`afed7f85fa01d100829faa620d15563b59e35e304603a83e857f369971022994`.
The final independent acceptance SHA-256 is
`96e6d1693ce117b75be9f7da2e9d41062d8a79453aabcf0ce7e72477db214af2`.

## Root integration and publication

The preserved maintained direct-path dependency preflight, recorded against
the upstream baseline, returned exit 1:

| Dependency | Observed state |
|---|---|
| `HomotopyHypothesis` | Missing directory/configuration; untracked path dependency |
| `Atlas` | Missing directory/configuration; untracked path dependency |
| `GIFT` | Uninitialized gitlink without Lake configuration; pin `e6f3c3ac2140c2324fb2ae029c32233e73aa5e92` |

That receipt checks direct path availability and provenance; it is neither
a root Lean build nor a transitive dependency audit. The native selection
above does not certify full-root integration. The exact publication-commit
pre-push command and its observed result will be recorded in the PR
description, separately from this selected-closure acceptance. No successful
pre-push result is asserted here.

No toolchain pin, dependency pin, checker implementation, or gate policy was
changed by this patch. Publication is a draft PR with the remaining root
integration limits disclosed.
