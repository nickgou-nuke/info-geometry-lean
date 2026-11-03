# Agent policy for `proofs/`

Inherit [the root agent policy](../AGENTS.md). This directory contains Lean
proof sources, task witnesses, copied references, and tooling. Determine the
ownership and build role of each file before editing it; the directory name
does not make its contents either accepted theorems or disposable scratch.

## Build scope

The root [lakefile](../lakefile.lean) declares `lean_lib proofs` with
`srcDir := ".."` and ``globs := #[.submodules `proofs]``, and marks it as a default
target. A tracked Lean source under this directory can therefore affect the
root-package build. Do not add incomplete proposals here on the assumption
that the build ignores them. Preserve the actual imports, namespace, and
dependency pins; do not create an independent package to evade the root
validation contract.

Run from the repository root and serialize checks:

```bash
python3 tools/infra/run_locked_lean.py proofs/task_name.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock proofs.task_name
```

Replace `task_name` with the actual file/module. For nested files, use the
corresponding dotted module path. A file check uses the available import
artifacts; a targeted Lake build manages the target's dependencies. When the
change requires checking the whole registered library, select `proofs`
explicitly. The changed-owner helper defaults to `InfoGeometry.` and must not
be used as evidence that a `proofs/` change was checked.

The [post-build gate](../scripts/quality/post_build_gate.sh) contains routing
for modified and deleted proof sources. Follow that gate and the root
[runbook](../RUNBOOK.md) when preparing a change for publication. Report the
actual target set and result; do not infer a full build from a narrow check.

## Proofs and supporting artifacts

Read the owner declarations and record exact assumptions before making a
mathematical claim. Apply the root acceptance rules: complete native proofs,
truthful hypotheses and carriers, axiom review, and no placeholder or scalar
surrogate used to conceal missing operator content. Graph/index evidence can
guide discovery but cannot certify a theorem. Inspect available graph
provenance; a full graph rebuild is not a prerequisite for a source search.

The [Python theorem queue](../tools/infra/agent_orchestrator_queue.py) uses
`proofs/<task-id>.lean` and `proofs/<task-id>.sp` as paired task files and writes
run reports under `artifacts/agent_orchestrator/`. A SymPy witness is supporting
evidence, not a Lean proof. Preserve its task identifier and provenance, and
state whether each requested stage actually ran.

Treat copied repositories and reference implementations according to their
ownership. Do not edit third-party sources or promote their statements into
repo-owned proof claims without an explicit task and source review. The
presence of older launchers and TypeScript copies here does not establish a
working root Pi installation; see the
[integration status](../docs/CANONICAL_AGENT_PIPELINE.md#pi-integration-status).

Create delegated repair proposals in new candidate files outside active owner
paths. Review and integrate the smallest justified change. Checkpoint only
task-owned paths, preserve unrelated work, and do not publish, schedule work,
or contact external services merely because this instruction file exists.
