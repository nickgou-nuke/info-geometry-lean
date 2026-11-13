# Graded Clifford unrolling verification

The theorem contract is in
[docs/CLIFFORD_GRADED_UNROLLING_CONTRACT.md](../../docs/CLIFFORD_GRADED_UNROLLING_CONTRACT.md).
This draft reuses the maintained focused project from PR #338 with the
repository's exact dependency pins; it does not introduce a second manifest.

From the repository root:

```bash
python3 verification/freed-pin-compatibility/check.py exe cache get Mathlib
python3 verification/freed-pin-compatibility/check.py build \
  InfoGeometry.Clifford.Cl11GradedUnrollingAudit
python3 verification/freed-pin-compatibility/check.py env lean \
  -DwarningAsError=true \
  "$PWD/lean/InfoGeometry/Clifford/Cl11GradedUnrollingAudit.lean"
```

The final command uses an absolute source path because Lake selects the focused
project directory. The maintained wrapper uses the shared build lock.

The audit imports exactly the eleven mathematical owners listed in
`lean/InfoGeometry/Clifford/Cl11GradedUnrollingAudit.lean`. It uses native module
ownership to inspect every declaration owned by them, including private and
generated declarations. It rejects unsafe or partial owned declarations and
transitive axiom dependencies outside `propext`, `Classical.choice`, and
`Quot.sound`. Every owner must have a positive audited declaration count.

The tracked audit source exactly matches the canonical
`tools.quality.reviewed_audit_source.audit_source` output for these eleven owners,
including its ownership selection and required completion markers. Source identity
and the fresh Lean execution are separate checks; the audit criteria were not
weakened to accept generated declarations.

## Checked selected-owner result

At `3a183d7a527cfea5ede84c301bc4b1e681a0028e`, the
[focused CI job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43421680904/job/131872938214)
completed the build of all eleven owners and their required imports, followed by
a fresh source execution of the exhaustive audit with warnings treated as errors.

| Check | Result |
| --- | --- |
| Selected-owner kernel build | PASS: all eleven mathematical owners and required imports. |
| Exhaustive owned-declaration audit | PASS: `470` declarations; positive counts for all eleven owners, including private and generated declarations. |
| Observed axiom dependencies | `[propext, Classical.choice, Quot.sound]`. The allowed set is exactly `propext`, `Classical.choice`, and `Quot.sound`. |
| Canonical audit source | Exact match to `tools.quality.reviewed_audit_source.audit_source`. |

The [checked evidence receipt](checked-evidence.json) identifies the checked
revision and run. The workflow's `cl11-graded-unrolling-evidence` artifact contains
`build.log`, `axioms.log`, and `source-evidence.json` with the exact commit,
toolchain, selected owners, and source hashes. Lean remains pinned to `v4.34.1`
and Mathlib to `d13f23b723b8a846827a245b89c10fc7d3f11612`. The workflow may reuse
build traces; its final declaration audit runs afresh.

Recursive real Clifford constructions are explicitly `noncomputable` where
required. Computational train, indexing, and parity folds use native `Nat.rec`;
the generic semiring train operations retain their computational scope. This
implementation avoids newly owned unsafe recursive runtime helpers while leaving
the exhaustive audit, owner selection, and foundational-axiom allowlist unchanged.

## Separate checks and outstanding failures

| Check | Recorded result | Evidence and scope |
| --- | --- | --- |
| Staged source gate, 2026-11-13 UTC | FAIL: one T16 finding | `Cl11RecursiveUnrolling.lean:44`; imported and nested matrix-carrier recognition remains unresolved. |
| Root SorryGate, 2026-11-13 UTC | FAIL: 91 debt files, 878 findings | [Run 43421680575, job 131872936887](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43421680575/job/131872936887); repository-wide debt gate. |
| Local full acceptance | INCOMPLETE | The local prerequisite build ended with wrapper exit 247 after subprocess exit 137. |

The remaining T16 finding is on `Matrix (Fin 2) (Fin 2) (RealMatrix n)`.
`realBlock_noncommuting` is an explicit native witness that compiled in the
preceding focused checks and belongs to the checked owner. The scanner's imported
and nested carrier recognition does not accept this specialization. The gate
remains failed, with its criteria unchanged. The root
SorryGate failure is separately unresolved. No local full-repository acceptance
is claimed; the focused result does not clear either separate gate. The PR remains a draft while those acceptance
requirements are unresolved.

## Historical recovery evidence

[recovery-evidence.json](recovery-evidence.json) remains unchanged. It records
source recovery, distinguishes exact hash matches from reconstructed intervals,
and preserves the original input's recovered SHA-256. The checked evidence receipt
records the later execution result separately. Independent source review and
source identity checks remain distinct from kernel and axiom acceptance.

This focused selection covers its named owners and imported dependencies.
Root integration, optional packages, and unrelated repository files remain
separate checks under the repository runbook.
