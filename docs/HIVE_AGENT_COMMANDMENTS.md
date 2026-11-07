# Hive agent checklist

This checklist applies the [root agent policy](../AGENTS.md). Use the
[canonical pipeline](CANONICAL_AGENT_PIPELINE.md) for current commands and
integration status, and the [runbook](../RUNBOOK.md) for validation coverage.
It does not grant permission to contact services, publish changes, or schedule
work outside the active task.

## Working rules

1. **Identify the checkout.** Work from its root, inspect the commit/remote and
   current changes, and preserve unrelated work. A workstation path is an
   example rather than a repository invariant.
2. **Read source before making a claim.** Follow the
   [deep-search protocol](REPO_DEEP_SEARCH_PROTOCOL.md), inspect actual owners,
   imports, hypotheses, instances, and consumers, and qualify the search scope.
   Graphs and reports guide discovery; they do not establish a theorem.
3. **Write an exact theorem contract.** State the carrier, operations, reused
   results, assumptions, intended implication, and remaining debt. A field
   assuming a conclusion is not a construction of that conclusion. Compilation
   validates the declared proposition, not its prose interpretation.
4. **Preserve mathematical acceptance.** Do not introduce proof holes, custom
   axioms, `native_decide`, unsafe proof bypasses, vacuous wrappers, or scalar
   surrogates for requested noncommutative content. Check actual axiom
   dependencies; the permitted foundational axioms are `propext`,
   `Classical.choice`, and `Quot.sound`. State any finite-model or conditional
   restriction explicitly.
5. **Reuse the correct owner.** Consult the
   [categorical map](CATEGORICAL_INFRASTRUCTURE_MAP.md) for categorical work.
   Distinguish finite-stage algebra, categorical colimits, completions, and
   analytic consequences. A name or analogy does not supply a missing map.
6. **Serialize validation and preserve caches.** Inspect active compiler
   processes. Use the shared-lock wrappers and keep builds/tests sequential.
   Never clean/delete Lake caches, alter pins incidentally, or build through a
   linked worktree/symlinked Lake root. See the
   [cache policy](../WARNING_DO_NOT_RUN_CACHE.md).
7. **Checkpoint only task-owned work.** Review the diff and stage the intended
   paths. Do not stage unrelated files or commit generated debris by default.
   Delegate repairs to new candidate files; review before integrating them.
8. **Treat runtime capabilities as optional.** Resolve Arango endpoints and
   credentials from configuration; observe availability and provenance. Keep
   the DAG, Hive queue, and aiClaw memory lanes distinct. The
   [Pi integration is currently blocked](CANONICAL_AGENT_PIPELINE.md#pi-integration-status)
   by tracked-path/import problems; the Archon wrapper has additional local
   prerequisites. Do not present either as a successful runtime from source
   inspection alone.
9. **Keep candidate and source roles separate.** Guard browser sends through
   the selected adapter's shared lane; do not stack prompts or overwrite an
   owner from an oracle response. SymPy witnesses, GEPA output, and graph
   candidates require review. Confirm worker state and stage outcomes before
   reporting progress.
10. **Report exactly what was checked.** Name the revision, affected owners,
    commands, exit results, proof/axiom/semantic scope, and unresolved issues.
    A changed-owner build is not a full default-target build, and neither
    certifies every historical file or a physical interpretation.

## Lean checks

Run from the repository root, substituting an actual owner:

```bash
python3 tools/infra/run_locked_lean.py src/InfoGeometry/Path/To/File.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Path.To.Module
```

The [Lake wrapper](../tools/infra/run_locked_lake_build.py) selects changed
`InfoGeometry` owners when no target is supplied. Use an explicit module or
library for the task; request `--all-default-targets` only when that broader
coverage is needed. The current [lakefile.toml](lakefile.toml), rather than a
historical job count, defines the default targets.

## Quality Management System (QMS)

Theorem-bearing work follows [docs/ALCHEMICAL_QMS_SOP.md](ALCHEMICAL_QMS_SOP.md)
(QMS-SOP-ALC-001, v4.1) with role separation:

- **G-A (Generation Agent)** — writes candidate packets, never declares acceptance or reviews its own work.
- **A-A (Audit Agent)** — independently reads artifacts, classifies gaps G1–G5, recommends CAPA; never authors the artifact under audit.
- **QA-A (Acceptance Quality Agent)** — runs compile/build/audit gates, accepts or rejects; never writes theorem content for the artifact.
- **Orchestrator** — routes work and records status; never uses its own coordination notes as proof authority.

QMS CLI entry point: `python3 tools/qms/run_qms.py` with subcommands
`intent`, `owner-search`, `generation`, `compile`, `capa`, `accept`,
`quick-gate`, and `capa-index`. Artifacts go to `artifacts/qms/<task-id>-*.json`
and `artifacts/qms/capa/`.

## Staged proof header and hooks

The [pre-commit hook](../.githooks/pre-commit) runs
[proof_proxy_staged_gate.py](../tools/quality/proof_proxy_staged_gate.py).
Its current header rule checks staged Lean source blobs and requires this
header at byte zero:

```lean
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
```

Install tracked hooks in a development checkout with:

```bash
scripts/install_git_hooks.sh
```

The installer sets `core.hooksPath` to `.githooks`. The
[pre-push hook](../.githooks/pre-push) separately checks the commit/worktree
relationship and invokes the [post-build gate](../scripts/quality/post_build_gate.sh).
A hook's presence in the tree does not show that it is installed or that a
particular change passed. Do not bypass a failing gate; report and resolve the
concrete failure within the task's scope.

## Queue and evidence ownership

The [Python theorem queue](../tools/infra/agent_orchestrator_queue.py) uses
`task_queue.json`, paired `proofs/<task-id>.lean` / `proofs/<task-id>.sp`
files, and reports under `artifacts/agent_orchestrator/`. Preserve the paired
witnesses and source hashes, and inspect the actual Formalist/Critic outcomes.
The [canonical pipeline](CANONICAL_AGENT_PIPELINE.md#python-theorem-queue-and-optional-archon-wrapper)
documents the separate Python, Archon, Hive, and native-session routes.
Select one scheduler for a task; keep all Lean compilation serialized.

Do not infer a running memory service, successful authentication, complete
ingestion, or current graph from a configuration default. Do not print secret
values. A service failure and a mathematical proof failure are distinct facts
and must be reported separately.
