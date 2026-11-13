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

The audit imports all eleven mathematical owners and iterates over every declaration
owned by them, including private and generated declarations. It rejects unsafe
or partial declarations and all axioms except `propext`, `Classical.choice`,
and `Quot.sound`. Every owner must have a positive audited declaration count.

Its body follows the existing generator
`tools.quality.reviewed_audit_source.audit_source`, including native ownership
selection and the required completion markers. A fresh comparison to that
generator and a completed Lean audit remain part of acceptance.

The focused GitHub workflow records the exact source commit, toolchain and
source hashes and uploads build/axiom logs. A workflow definition or a queued
run is not evidence of success. The source recovery record is in
[recovery-evidence.json](recovery-evidence.json).

## Current local result

The initial focused build stopped on an exhausted workspace filesystem before
checking the new proofs. A retry using native Lake path relocation reached
Lake but terminated before theorem diagnostics; the execution environment then
became unavailable. Source files were recovered through conversation records
and independently retained hashes, with reconstructed intervals distinguished
in the recovery evidence. The original input text's SHA-256 was also recovered
exactly.

After recovery, the matrix-rank factorization owner compiled locally. The first
[focused CI run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43406594970)
reported concrete elaboration errors in four new owners. The follow-up sources
repair those diagnostics and add the homogeneous inverse and actual local
Clifford-core contraction.

The second [focused CI run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43408976175),
on `4ad3bced5caf5f76b969b1d0237869609911f5be`, compiled
`SplitCliffordMatrixEquiv`, `Cl11GradedUnrolling`, `MatrixRankFactorization`,
and `RankMinimalTensorTrain`. It still failed in `ExactTensorTrain`,
`Cl11PureTensorObstruction`, and `Cl11RecursiveUnrolling`, preventing the
downstream owners and exhaustive audit from running. Further proof repairs
address those exact diagnostics; their presence is not a successful build.

The third [focused CI run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43411000804),
on `b6c097c737975c74ef8d6798b32921e0658410fc`, compiled six selected owners:
the preceding four, `ExactTensorTrain`, and `Cl11PureTensorObstruction`.
`TensorTrainMatricization` and `Cl11RecursiveUnrolling` still reported errors;
the remaining dependent owners and exhaustive audit were blocked. The next
revision also includes positive-length terminal-boundary normalization and
its native local-core reconstruction/minimality bridge. Independent review
of those sources is recorded separately from their pending kernel result.

A completed kernel build of the full selected closure, exhaustive
declaration-axiom audit, and root integration acceptance remain pending.
Independent source review and source identity checks do not substitute for
those checks. The workflow retains native build traces between revisions;
Lake invalidates changed sources, and the final declaration audit runs afresh.

The tracked staged source gate was executed and retains one T16 finding on
the nested matrix coefficient carrier in `Cl11RecursiveUnrolling`. The owner
contains the explicit native witness `realBlock_noncommuting`; the scanner's
imported-carrier resolution does not recognize this specialization. The gate
is recorded as failed, independently of the pending Lean result.

This focused selection covers its named owners and imported dependencies.
Root integration, optional packages, and unrelated repository files remain
separate checks under the repository runbook.
