# Krein / Zorn boundary validation record

## Status

Prepared against upstream main
`08c34e03f610b452e03422037949196dc7d92d6d` on 2026-11-17.
The exact theorem scope is specified in
[the contract](KREIN_OCTONION_BOUNDARY_CONTRACT.md).

**Candidate source; kernel acceptance pending.** The successful checks below
do not yet establish Lean compilation, a clean transitive axiom footprint,
or root-package integration. The upstream PR should remain a draft until
the required checks have completed.

## Change inventory

| File under `lean/InfoGeometry/` | Public theorem count | Purpose |
|---|---:|---|
| `Algebra/ZornAssociativeCollapse.lean` | 6 | An explicit native associator forces all additive multiplicative associative images to vanish. |
| `Krein/KreinAdjointBoundary.lean` | 11 | Null Gram/range-isotropy equivalence, adjoint commutation boundary, and the doubled diagonal idempotent. |
| `Krein/DoubledKreinWitnesses.lean` | 20 | Ordered transfers, both pairings and their signs, noncommutation, and the real eigenvector obstruction. |
| `Order/KreinOctonionDependencyPoset.lean` | 15 | Exact finite reachability, covers, acyclicity, terminal join, and obstructions to grading and general joins. |
| `KreinOctonionAudit.lean` | 0 | 69 distinct axiom-inspection commands: 52 new public theorems and 17 reused owner theorems. |

No toolchain, dependency pin, build configuration, hook, existing mathematical
owner, or umbrella import is changed.

## Source recovery and review provenance

The preceding session's scratch checkout was no longer available. The four
mathematical owner files were reconstructed from retained exact source text.
An independent reviewer checked each against the SHA-256 value recorded for
its previously reviewed candidate snapshot; all four matched. The audit leaf
was regenerated and checked against the full declaration inventory.

After recovery, source review identified an ambiguous scalar argument in
`diagonalProjector_fixes_diagonal`. The proof now explicitly applies
`two_smul ℝ`; this preserves the statement and fixes the scalar type at the
declared real Hilbert carrier. Recovery hashes refer to the pre-edit snapshots.

This establishes recovery of the reviewed source snapshots. It does not
establish identity with an unavailable later local Git commit, recover a
compiler result, or certify any new proof. All current validation must be
reported from current commands.

## Pinned environment

- Lean toolchain: `leanprover/lean4:v4.34.1`.
- Observed runtime: Lean 4.34.1, release commit
  `5045d0056413266e57c625dcd7c365b10e377c52`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`, matching the
  repository manifest.
- Focused import closure: nineteen canonical local modules. A copied-source
  focused check, if successful, is separate from the root-package gate.
- Compilation uses the maintained repository lock
  `/tmp/info-geometry-build.lock`; no other compiler process is terminated.

## Validation results

| Check | Current result | Scope |
|---|---|---|
| Source recovery hashes | PASS | All four reviewed mathematical source snapshots recovered byte for byte. |
| Independent semantic source review | PASS at recovered snapshot | Mathematical statements, native carriers, hypotheses, and interpretation limits. |
| Comment/string-aware forbidden-proof-token scan | PASS | No `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, or `sorryAx` token in the four new owners. |
| Semantic vacuity gate | PASS, exit 0, no findings | Four new mathematical owners only. |
| Audit command inventory | PASS | Every new public theorem included once; seventeen reused names resolve in the pinned source. |
| Targeted Mathlib cache hydration | PASS, exit 0 | Exact pinned sources and dependencies; 3,173 cached modules decompressed under the shared lock. |
| Focused Lean compilation | PENDING | The nineteen-module copied-source check is queued under the shared compiler lock. |
| Elaborated axiom output | PENDING | Audit source exists; no completed current compiler output is claimed. |
| Staged proof gate | PASS, exit 0 | Repeated by the installed pre-commit hook after the scalar-type clarification. |
| Root targeted Lake build | BLOCKED, exit 1 | Package initialization stopped at the absent `HomotopyHypothesis` directory, before compiling the new modules. |
| Five-file axiom/debt source scan | PASS | Five clean files; zero `sorry`/`axiom`/`admit` gaps. This is not an elaborated axiom audit. |
| Repository semantic-content scan | PASS | 27,280 selected Lean files; zero current findings. Lexical scope only. |
| Tracked Lean scope and quarantine audits | PASS | Both maintained source audits completed successfully. |
| Installed pre-push gate | FAILED, exit 1 | The targeted root build was blocked by missing `HomotopyHypothesis`; all subsequent source audits passed. |

A current nonwaiting invocation of `run_locked_lake_build.py` with the five
targets returned exit 2 before compilation: the shared lock was held by
`clifford-dirac`. Targeted cache hydration is queued rather than bypassing
that lock. This is a scheduling result, not a Lean elaboration failure.

The installed pre-push hook was subsequently invoked for the actual new-ref
record at local commit `dc769a9bb0903bbc11f293072cb6ca489a0d62d2`.
The five Lean blobs in that gate snapshot and the published candidate are
identical; subsequent changes update this validation record only.
Its locked five-target build acquired the shared lock, checked out the pinned
Mathlib and LeanCopilot dependencies, and returned:

```text
error: HomotopyHypothesis: package directory not found:
  external_refs/homotopy-hypothesis-lean4
[locked-lake-build] lake build exited with code 1
```

The other missing root path packages were inspected separately. Atlas has no
configured repository/revision in the root path manifest. An attempt to
initialize the recorded GIFT submodule failed because its server rejected
the pinned commit `e6f3c3ac2140c2324fb2ae029c32233e73aa5e92`
(`upload-pack: not our ref`). No substitute revision was selected; the
failed worktree initialization was returned to its prior empty state.

These integration observations do not establish a failure of the new theorem
statements. They also do not waive the repository's required acceptance gate.

The source checks used the following maintained semantic gate:

```bash
python3 tools/quality/semantic_vacuity_gate.py \
  lean/InfoGeometry/Algebra/ZornAssociativeCollapse.lean \
  lean/InfoGeometry/Krein/KreinAdjointBoundary.lean \
  lean/InfoGeometry/Krein/DoubledKreinWitnesses.lean \
  lean/InfoGeometry/Order/KreinOctonionDependencyPoset.lean \
  --json-out /workspace/scratch/50ddde16aff2/verification/semantic-vacuity.json \
  --fail-on error
```

## Required acceptance checks

From a fully provisioned checkout with the pinned dependencies:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Algebra.ZornAssociativeCollapse \
  InfoGeometry.Krein.KreinAdjointBoundary \
  InfoGeometry.Krein.DoubledKreinWitnesses \
  InfoGeometry.Order.KreinOctonionDependencyPoset \
  InfoGeometry.KreinOctonionAudit

python3 tools/infra/run_locked_lean.py \
  lean/InfoGeometry/KreinOctonionAudit.lean

python3 tools/quality/proof_proxy_staged_gate.py

bash scripts/quality/post_build_gate.sh --incremental \
  --base=08c34e03f610b452e03422037949196dc7d92d6d --head=HEAD
```

The installed pre-push hook also invokes the no-argument quality script for a
new branch. Although its message calls that step a full root-package gate,
the script's default mode is incremental. This report does not infer broader
coverage from that label. An actual `--full` run is a separate check.

## Remaining acceptance debt

1. Complete current Lean elaboration and repair any genuine errors without
   weakening the contract or inserting proof placeholders.
2. Inspect all 69 axiom outputs; source inventory alone is insufficient.
3. Run the staged and push gates for the exact published tree.
4. Keep exceptional-group, quantization, and physical claims at the explicit
   scope boundary recorded in the contract.
