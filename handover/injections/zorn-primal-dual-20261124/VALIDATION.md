# Validation checkpoint — 2026-11-24

## Disposition

**Source-reviewed implementation; not kernel verified.**

The six new Lean owners have passed independent mathematical/source review.
No new owner has completed native compilation in this task, and the axiom
audit has not executed. This checkpoint must not be treated as a successful
build, proof certificate, pre-commit approval, or pre-push approval.

The task branch is `codex/zorn-primal-dual-operators-20261124`, based on
`fe24e350b08fdea04f74c0748ef9fd9417c47529`. At the pre-publication checkpoint
recorded here, changes were staged locally and no task commit, push, or pull
request existed. The subsequent explicit request to publish this checkpoint
is for a draft PR with native verification pending. Publication does not imply
native acceptance or a successful local proof or push gate.

## Observed checks

| Check | Observed result |
|---|---|
| Mathematical/source review | PASS at the owner hashes in `SOURCE_REVIEW.md`; the later proof-body repairs preserve every statement and hypothesis. |
| Checker source review | No blocking trust issue found in the bounded independent review. |
| Toolchain probe | Native Lean v4.34.1, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`. |
| Dependency inspection | Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; all eight actual dependency search-path packages matched the root manifest and had clean tracked sources. |
| First native attempt | Existing `InfoGeometry.Algebra.ZornVectorMatrix` compiler child terminated with return code `-9` (SIGKILL), with no Lean diagnostic. No module completed. Resource pressure was observed, but the receipt itself establishes only the signal termination. |
| Single-thread retry | Waited for the maintained shared build lock, then was externally stopped while still queued. Tool exit code was 130. No Lean compilation or axiom-audit command began. |
| Axiom audit | NOT RUN. `Audit.lean` is implemented but has no successful execution receipt. |
| Staged proof gate | Attempt terminated with exit code 137; no passing result. It must be rerun serially before committing. |
| Semantic-vacuity scan | Earlier source snapshot produced one `trivial_surface` warning at `incident_iff_not_isUnit`; independent semantic review accepted the actual bridge theorem as nonvacuous. This is not a claim that the final source passed a new scan. |
| Whitespace / patch integrity | `git diff --cached --check` passed. The complete patch passed `git apply --reverse --check` against the current task tree. Neither check validates Lean theorems. |
| Full root build / public umbrella compilation | NOT RUN. Added public imports were source-reviewed only. |

The first failed native run ID was `18cedb46b7f6412eb62f5df0da4c9e37`.
The queued retry ID was `df833b8d4ffc4303b623ffc5c7c0bed4`. External
termination of the retry did not execute the driver's cleanup: its raw
receipt still says `running` and has no completed command records. It is an
**incomplete, non-success receipt**. The separately recorded orchestration
result is exit 130. No compiler process for this task remains queued.

## Resource and serialization boundary

The shared workspace filled during preparation. This task's own independent
checkout was reduced using Git sparse checkout and relocated to
`/tmp/info-geometry-zorn-primal-dual-20261124`. The complete `lean`, `tools`,
`scripts`, `skills`, `verification`, `handover`, and `docs` directories and the
relevant policy/hook directories remain present. Shared dependency caches and
other work were not modified.

The repository's `AGENTS.md` requires serialized validation through the shared
build lock and forbids stopping another running Lake process without explicit
authorization. Another Lake build continued to hold the lock during the retry.
The local proof and push gates were not bypassed. Source review is therefore
the strongest completed acceptance evidence for these new owners.

## Reproduce the native check

With the pinned toolchain and dependencies available, run from the repository
root:

```bash
python3 verification/zorn-primal-dual/check.py --force
```

The exact environment-specific invocation prepared here was:

```bash
python3 verification/zorn-primal-dual/check.py \
  --lean /workspace/scratch/058543be00a5/lean-runtime/lean-4.34.1-linux/bin/lean \
  --packages /workspace/scratch/058543be00a5/info-geometry-lean/.lake/packages \
  --force
```

The default closure contains 38 repository modules: the six new owners,
their prerequisites, and the two existing seven-generator Clifford owners.
The checker uses one Lean worker, checks source and environment stability,
inherits the shared lock into compiler children, records per-module logs,
and treats warnings in new owners as errors.

After compilation, `Audit.lean` inventories all declarations owned by the six
new modules and two reused Clifford modules, including private/generated
declarations. It rejects unsafe/partial declarations and any transitive axiom
outside `propext`, `Classical.choice`, and `Quot.sound`. This describes the
audit's intended check, not an executed result.

## Remaining acceptance steps

1. Complete native compilation and repair any elaboration or linter diagnostics.
2. Execute the declaration/axiom audit successfully.
3. Re-review any resulting proof changes and complete independent native QA.
4. Run the staged proof gate successfully before committing.
5. If publication is requested, satisfy the repository's separate pre-push gate.

The patch is a complete, inspectable implementation candidate for those steps.
Its mathematical source review does not remove the need for them.
