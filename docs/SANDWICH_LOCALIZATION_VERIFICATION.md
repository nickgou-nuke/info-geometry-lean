# Verification: two-sided localization and endogenous Peirce operators

Recorded 2026-11-13, with root-job state observed at 12:29:15 UTC.

## Accepted scope

The nine mathematical owners at proof commit
`436cdbed57deb267d6e90c2040d8ad5db57d52bf` compile successfully with their
complete 38-module repository import closure. The native declaration audit
accepted 355 distinct owned declarations, including definitions, instances,
private declarations and generated declarations. Every one of the 162 named
theorem/lemma declarations, including all 15 private theorems, occurs exactly
once in the ownership audit. Every selected owner has nonzero coverage.

The union of transitive axiom dependencies is exactly
`propext`, `Classical.choice`, and `Quot.sound`. The maintained audit rejects
unsafe/partial declarations and any other axiom. The complete-range staged proof
gate and independent semantic review are separate completed checks; they are
not substituted for kernel execution.

This acceptance covers the exact selected mathematical sources. Whole-repository
acceptance remains withheld. Completed broader root gates failed, and newer
source-lane jobs were active or queued at the observation time documented below.

## Immutable execution identity

| Item | Value |
|---|---|
| Repository | `nickgou-nuke/info-geometry-lean` |
| Draft PR | [#356](https://github.com/nickgou-nuke/info-geometry-lean/pull/356) |
| Dependency base, PR #334 | `b76d9e1e6da2ba8c1d7505ca791ef81c57d0db92` |
| Checked proof head | `436cdbed57deb267d6e90c2040d8ad5db57d52bf` |
| Actual PR merge checkout | `fc49365c7a55eb721fb3a9e9ffe90aadfe8f3392` |
| Identical head/merge tree | `876c9b59f273084ba8405bcac708cd65d3d0bb46` |
| Lean | `4.34.1` |
| Compiler commit | `5045d0056413266e57c625dcd7c365b10e377c52` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Focused run | [43423042151](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43423042151) |
| Successful kernel job | `131877494159` |
| Original kernel artifact | [14035182640](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43423042151/artifacts/14035182640) |
| Artifact ZIP SHA256 | `8bbfca8b8e3de21566f842161289601b85e965dd41996f3243a044efc46fc957` |
| Decoded kernel job-log SHA256 | `2d786355e3d952ff4fc90e45c1deb9dc7eeaee205d3c12b283ce5e8ccfbfaf3f` |

The tested merge has exactly the dependency base and checked proof head as its
parents, and its tree is identical to the proof head. The later commit containing
this report and its evidence changes documentation/data only; the checked Lean
owners, checker, workflow, gates and pins remain unchanged.

The executed command was:

```bash
python3 project/tools/quality/check_sandwich_localization.py \
  --mathlib-root pinned-mathlib --output verification
```

The task wrapper delegates to the maintained source-closure compiler and native
ownership audit. Compilation is serialized under the maintained build lock in
an independent runner. No local Lean compilation was performed while another
task held the shared local build lock. No dependency pin or cache-cleaning change
was used to obtain the result.

## Coverage by owner

| Owner, relative to `InfoGeometry` | Named theorems | Audited owned declarations |
|---|---:|---:|
| `Algebra.SandwichLocalization` | 17 | 37 |
| `Algebra.SandwichLocalizationActions` | 12 | 52 |
| `Algebra.SandwichLocalizationStar` | 12 | 38 |
| `Algebra.SandwichBalancedTensor` | 28 | 71 |
| `Algebra.OneSidedLocalizationBoundary` | 3 | 5 |
| `OperatorAlgebra.PeirceSpine.SandwichCayley` | 7 | 14 |
| `OperatorAlgebra.PeirceSpine.EndogenousKernelBridge` | 16 | 29 |
| `OperatorAlgebra.PeirceSpine.PeirceDefectIdentities` | 7 | 14 |
| `OperatorAlgebra.PeirceSpine.KernelBridgeMatrixWitness` | 60 | 95 |
| **Total** | **162** | **355** |

All 38 snapshotted repository source files match their recorded SHA256 values. All nine selected
files match the independently reviewed immutable source snapshots. The successful
check retains nine advisory warning lines in the new owners and 28 warning lines
over the closure; it is not a warnings-as-errors result.

## Exact current staged check

The unchanged `proof_proxy_staged_gate.py` was executed on the actual nonempty
nine-file task range, with the final proof tree in the real index. The temporary
HEAD move to the dependency base was used only to expose that staged range;
index-tree equality and the exact file list were checked before execution.
HEAD/index were restored. The restored HEAD/tree, empty staged mathematical
delta and unchanged nine owner bytes were independently verified.

The staged proof gate exited zero; its preserved log binds this check to the
final proof head/tree. The coordinator separately observed exit zero from
`git diff --cached --check`; that whitespace command is not recorded in the
staged-gate log. Earlier
incremental repair scans are not used as a substitute for this complete-range
check.

## Independent review

A separate semantic reviewer fetched all nine complete final owners and the
contract from the immutable GitHub proof commit and confirmed byte equality with
the reviewed snapshots. The mathematical authoring coordinator and candidate
author did not provide that semantic verdict.

Execution QA independently downloaded the exact kernel artifact, verified its ZIP
digest, all source hashes, all 38 compilation results, all 355 distinct declaration
records and exact coverage of all 162 named theorems. The QA receipt discloses its
role, including authorship of the initial thin checker/workflow, whose execution
bodies and subsequent scheduling changes received separate review.

## Broader root gates: failed and pending, not accepted

The latest completed broader source run at the recorded observation time is
[43421170036](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43421170036),
source job `131871247180`, for proof head `fb2918d3bfb971d5225e81bae0cee1121ad531cf`
and checked merge `5e5b36d1347a55986b18841b4209928e3ee8e89b`.
It is an earlier revision, and is not represented as a root-gate certificate for
the final proof head.

Its actual task-range staged gate passed. Both maintained root commands exited one:

```bash
bash scripts/quality/post_build_gate.sh --incremental --base=b76d9e1e6da2ba8c1d7505ca791ef81c57d0db92 --head=5e5b36d1347a55986b18841b4209928e3ee8e89b
bash scripts/quality/post_build_gate.sh --full
```

Their Lake attempts stopped at the missing local path dependency
`external_refs/homotopy-hypothesis-lean4`. Bounded source inspection found no
tracked remote/revision or gitlink for this dependency or the manifest's local
`Atlas` path package. Historical local-machine references do not supply a
reproducible pin. Initializing the separately pinned GIFT submodule would not
resolve the preceding HomotopyHypothesis/Atlas block.

The nine-file debt scan and full 28,121-file debt scan reported zero gaps; those
are lexical results, not a whole-project compilation. The thresholded vacuity
scan exited zero while reporting 72,651 findings, including 862 global errors
and 71,789 warnings. Its 33,087 `lean/` prefix findings must not be described as
a clean scan. Theory-report generation emitted sort/broken-pipe diagnostics.
An already captured earlier report also lists an orphan file and ten forbidden
quarantine imports in unchanged `lean/InfoGeometry.lean`; a report-generation
exit zero did not make those findings pass.

Run 4 source job `131874764267` at `f079edae966d5d20fe96ab04119f3e545b8863d0` had passed its staged gate,
failed its incremental gate and entered its full gate. The successful proof
run's source job `131877493835` was still pending. Neither pending execution nor
earlier-revision root results is counted as final root acceptance. These jobs
were active or queued at that checkpoint; no cancellation or manual rerun
had been used.

## Preserved evidence

The files in [verification/sandwich-localization-20261113](verification/sandwich-localization-20261113)
retain the raw successful status, raw ownership audit, actual audit program,
compiler version, exact per-module compilation logs, independent archive inspection,
independent QA receipt, complete-range staged log, job logs and hash manifest.
The decoded kernel and earlier root job logs are stored as JSON string values,
with their exact UTF-8 byte counts and SHA256 values, preserving original
whitespace and line endings. The original archive remains linked above.

The [theorem contract](SANDWICH_LOCALIZATION_CONTRACT.md) records the exact carriers,
hypotheses and mathematical limits. In particular, the two denominator indices
are a directed system rather than an automatically defined direct-sum grading;
the integral unitary reverses the signed cycle without asserting that its square
is one; and the finite nonzero charge square does not reconstruct the whole
ambient degree-two sector.
