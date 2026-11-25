# Zorn/Souriau validation status

Prepared on 2026-11-24. Proof/workflow checkpoint:
`da6b9ba80a64adf3f16fd5c33d261265958492fc`, tree
`bda3e8e96d66e50622a11c248d3a4e55b225cb65`.
Integration base: PR #441 at
`4c45f2bd932592fa86820f2e3360085f9e060c38`.

## Completed evidence

- Independent source review of all six new Lean owners, including re-review
  of the right-only refinement and the parent left-unit consumer.
- Independent evidence-map and validation-workflow QA.
- Source inventory of 61 public declarations; all six source hashes are
  recorded in `verification/zorn-souriau/SOURCE_REVIEW.md`.
- Scoped source gates passed: staged proof integrity, semantic content,
  source axiom/debt, tracked Lean scope, and whitespace checks.
- Placeholder screening found zero hard findings and two reviewed soft
  arithmetic-proof flags, retained in the source-review record.
- The tracked pre-commit hook passed at both task checkpoints.
- Workflow YAML, shell syntax, and embedded Python syntax checks passed.

These are source results. They do not establish kernel acceptance.

## Native attempt

The initial focused diagnostic started Lake and returned outer exit code
`247` without a Lean success or proof diagnostic. No termination cause was
established. A complete retry was then started with:

```bash
env -u LEAN_PATH -u LEAN_SRC_PATH -u LEAN_SYSROOT \
  LEAN_NUM_THREADS=1 \
  PATH=/workspace/scratch/058543be00a5/lean-runtime/lean-4.34.1-linux/bin:"$PATH" \
  python3 -B verification/zorn-souriau/check.py \
  --packages /tmp/para-twistor-noether-20261124/exact-pin-packages.json
```

Its receipt identifies run `run-1795511897409918891-2`. At this checkpoint it
remains **queued on the shared build lock**, with no compiler command, HEAD,
or input snapshot yet recorded. The driver file and all helpers already
loaded by that process are unchanged across the integration-base update.
The driver snapshots the current files and HEAD only after acquiring the
lock and rejects changes during the resulting native transaction.

The receipt is `artifacts/zorn-souriau/native/result.json`. Its later contents,
or an actual hosted run, must supply the native result; this document does
not predict one. Fresh warnings-as-errors checks and the transitive axiom
audit remain required after a successful target build.

## Root publication environment

The maintained read-only preflight was actually run:

```bash
python3 -B tools/infra/ci_bootstrap.py paths \
  --report /tmp/zorn-souriau-audit-20261124/root-path-preflight.json
```

It exited **1** and recorded these root-package blockers:

| Package | Observed failure |
|---|---|
| `HomotopyHypothesis` | Missing `external_refs/homotopy-hypothesis-lean4/lakefile.lean`; no tracked source or initialized Gitlink provenance |
| `Atlas` | Missing `external_refs/atlas-lean/lakefile.toml`; no tracked source or initialized Gitlink provenance |
| `GIFT` | Missing `external_refs/gift-framework-core/lakefile.lean`; Gitlink `e6f3c3ac2140c2324fb2ae029c32233e73aa5e92` is uninitialized |
| `InfoGeometryCore` | Tracked source and required configuration present |

The report's checkout revision is `afd5c7978cde9aae794f6e6c8a0d3c0f75afbaa5`;
the subsequent proof/workflow checkpoint does not change these package
declarations, path-package sources, or preflight implementation. A bounded
inspection of the three other known checkouts found no complete provider for
the missing root dependencies. Atlas and HomotopyHypothesis have no exact
upstream URL/revision supplied by the inspected path configuration.

No root publication-hook pass is claimed. The focused workflow checks the
six owners and their imports; it does not repair or waive root integration.
No second compiler transaction was queued behind the existing native retry.

## Publication boundary

The changes are ready for source review, with native acceptance pending.
The repository's `AGENTS.md` requires the publication gate and forbids
bypassing it. The earlier explicit draft-publication exception applied to
PR #439's separate snapshot. No new exception is assumed here. A draft
publication of this change with the unresolved gate requires its own
explicit authorization.

The prepared focused workflow will check the actual published PR head when
triggered. Creating that workflow is not evidence that it has run or passed.
