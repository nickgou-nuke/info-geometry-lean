---
name: info-geometry-repo
description: Use when working inside the InfoGeometry Lean 4 repository and you need the repo-specific bootstrap sequence, DAG/semantic-export workflows, trusted graph paths, or the current bridge/frontier map across KK, AnalyticalIndex, OperatorAlgebraBridge, WeylTransport, and GrandSynthesis.
---

# InfoGeometry Repo

Use this skill when the task is about this repository's structure, theorem topology, DAG tooling, semantic block export, bridge closing, or safe workflow choices for heavy Lean modules.

## First Read

Read these first:

1. `/home/goutev/LEAN4/info-geometry-lean/README.md`
2. `/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md`

Then read only the specific reference file(s) you need from `references/`.

## Core Mental Model

The repo has two layers:

1. domain layer
- `lean/InfoGeometry/...`
- theorem library, canonical synthesis modules, KK layer, gauge/transport/index modules

2. tooling layer
- `lean/DAG/`
- `lean/scripts/DAG/Exploration/`
- `tools/semantic_block_export.py`

Do not mix these graph views:

1. declaration DAG
- global topology, SCCs, dominators, bottlenecks

2. block export
- source attribution, slices, quiver emission

3. semantic block graph
- purified human-facing theory structure using `primaryProduces`

For large files, semantic block export through the external stdlib server path is the trusted route.

## Default Workflow

1. Identify the task type:
- whole-repo topology
- single heavy-file semantic export
- categorical diagnostics
- bridge/frontier analysis

2. Build only what you need first.

3. Prefer semantic block export for heavy capstone modules.

4. Treat generated `reports/dag/` artifacts as disposable outputs, not tracked source.

## Trusted Heavy-File Export Path

Use:

```bash
python3 tools/semantic_block_export.py \
  <input.lean> \
  <output.json> \
  --server-mode stdlib \
  --inject-rpc-import \
  --skip-wait-for-diagnostics \
  --timeout 900
```

Why:
- separate `lean --server` process
- avoids in-process `[init]` collisions
- gives the trusted semantic block JSON for Mathlib-heavy files

## Current Frontier Map

The current vertical bridge picture is:

- KK core: `InfoGeometry.KK.KasparovCycle`
- first large frontier: `InfoGeometry.Canonical.AnalyticalIndex`
- vertical operator layer: `InfoGeometry.Canonical.OperatorAlgebraBridge`
- large transport/synthesis layers: `WeylTransport`, `GrandSynthesis`

Thin adjunct modules such as `CompactOperatorBridge`, `Product`, and `KasparovCompactOperator` are not the main articulation hubs.

## Use References

- For commands and standard runs: read `references/commands.md`
- For module/frontier orientation: read `references/module-map.md`
- For prompt-ready bridge exploration over the current KK -> AnalyticalIndex -> GrandSynthesis frontier:
  read `references/frontier-prompt.md`
- For the split creative/critical LLM evaluation workflow over the current trusted frontier:
  read `references/frontier-prompt-creative.md` and `references/frontier-prompt-critical.md`
- For the current first-strike candidate bridge lemmas on that frontier:
  read `references/bridge-candidates.md`

## Agent Discipline

- Build before assuming a path is stable.
- Prefer local graph evidence over intuition.
- Use LLM reasoning as frontier proposal, not as proof authority.
- The right output is: candidate bridge statements, closure gaps, and attack plans.
- The Lean kernel decides what is true.
