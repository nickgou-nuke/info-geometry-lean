---
name: info-geometry-repo
description: Use when working inside the InfoGeometry Lean 4 repository and you need the repo-specific bootstrap sequence, DAG and semantic-export workflows, trusted artifact paths, or the current split between root substrates, representation bridges, and capstone consumers.
---

# InfoGeometry Repo

Use this skill when the task is about this repository's structure, theorem topology, DAG tooling, semantic block export, bridge discovery, or safe workflow choices for heavy Lean modules.

When the task is specifically about canonical theorem ownership, wrapper elimination, file splitting, or graph-guided module disentanglement, also read `/home/goutev/LEAN4/info-geometry-lean/skills/lean-canonicalization-policy/SKILL.md`.

## First Read

Read these first:

1. `/home/goutev/LEAN4/info-geometry-lean/README.md`
2. `/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md`
3. `/home/goutev/LEAN4/info-geometry-lean/tools/README.md`

Then read only the specific reference file(s) you need from `references/`.

## Core Mental Model

The repo has two maintained layers:

1. domain layer
- `lean/InfoGeometry/...`
- theorem library, substrate modules, canonical bridge modules, KK and quantum consumers

2. tooling layer
- `lean/DAG/`
- `tools/infra/`
- `tools/frontier/`
- `tools/docs/`

Do not mix these graph views:

1. declaration DAG
- atomic theorem-level truth and dependency structure

2. structural topology
- condensation, dominators, witness paths, and rooted structure

3. source-sink correspondence
- packet and carrier incidence built downstream in Python

4. semantic block export
- human-facing heavy-file structure for frontier work

5. semantic quotient and projection coloring
- shell-versus-trunk separation and lower-cluster ownership projected upward

Artifact placement matters:
- `artifacts/dag/full_graph.json` and `artifacts/dag/index/decls.jsonl` are the public authoritative atomic declaration-DAG inputs.
- `artifacts/dag/structural-topology.json` is the authoritative structural layer.
- `artifacts/dag/source-sink-bipartite.json` is the authoritative source-sink correspondence object.
- `reports/dag/*.md` and `reports/dag/*.json` are derived readable outputs.

If those layers disagree, trust the atomic DAG first, then the structural topology, then the source-sink correspondence artifact, and regenerate the reports.

## Hard Proof Policy

Treat vacuous success as failure for frontier accounting.

- Do not accept `sorry`, `admit`, `axiom`, placeholder contracts, or equivalent proof gaps on the stable theory path.
- Treat trivial transport, direct assumption unpacking, aliasing, and packaging as packaging, not proof progress.
- Only count a result as real closure when it builds a real witness or proves a nonvacuous relation from lower repo data.
- Never present a conditional wrapper or restated hypothesis as completed unification.

## Current DAG Pipeline Order

For the maintained DAG pipeline, use this exact order:

1. `python3 tools/infra/refresh_decl_graph.py`
2. `python3 tools/infra/refresh_blueprint_tags.py`
3. `python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags`
4. `python3 tools/infra/generate_theorem_surface_index.py`
5. `python3 tools/infra/generate_source_sink_compression.py`
6. `python3 tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json`
7. `python3 tools/infra/check_bipartite_bleed.py`
8. `python3 tools/infra/generate_structural_dedup.py`
9. `python3 tools/infra/generate_structural_fibers.py`
10. `python3 tools/infra/generate_semantic_quotient.py`
11. `python3 tools/infra/generate_projection_coloring.py`
12. `python3 tools/infra/select_openclaw_target.py`

Important:
- do not run `generate_source_sink_compression.py`, `generate_semantic_quotient.py`, or `generate_projection_coloring.py` before the theorem-surface index is fresh
- do not trust `reports/dag/*` until the whole sequence above has finished
- blueprint refresh belongs in the maintained path because stale `auto_blueprints.lean` breaks the auxiliary theorem surface

## Default Workflow

1. Identify the task type:
- whole-repo topology
- single heavy-file semantic export
- bridge/frontier analysis
- ownership split or canonicalization cleanup

2. Build only what you need first.

3. For full or umbrella builds, use `python3 tools/infra/run_locked_lake_build.py ...` and never start two of them concurrently.

4. Prefer direct file analysis before graph analysis.

5. For heavy files, prefer semantic block export over guessing from the raw declaration graph.

## Trusted Heavy-File Export Path

Use:

```bash
python3 tools/frontier/semantic_block_export.py \
  <input.lean> \
  <output.json> \
  --server-mode stdlib \
  --inject-rpc-import \
  --skip-wait-for-diagnostics \
  --timeout 900
```

## Current Structural Map

The current repo should be read through these spines:

- projective and relative-potential root:
  `ProjectiveStateCore`, `RelativeGeneratorCore`, `PositiveRayCore`, `RelativePotentialCore`, `RedLine`
- KMS and modular transport trunk:
  `Thermal`, `TomitaTakesaki`, `SinkhornKMSCore`, `KMSSinkhornSeedState`, `KMSSinkhornScalarPotential`, `KMSSinkhornWeightedTransport`
- geometry trunk:
  `RicciMongeAmpere`, `CalabiYauMetricRicci`, `CalabiYauRNMongeAmpere`, `CalabiYauWBridge`, `PerelmanW`
- singular and conformal trunk:
  `Drazin`, `MoorePenrose`, `SingularBoundaryCorrection`, `ConformalAlgebra`, `ConformalUnification`, `ConnesArakiCore`, `ConnesArakiTomita`
- IB and count trunk:
  `SinkhornFoundation`, `IBProjective`, `IBGaugeBridge`, `IBUpdate`, `CountSubstrateBridge`
- capstone and consumer layer:
  `AnalyticalIndex`, `GrandSynthesis`, `Rosetta`, `MasterSynthesis`, `DeepHorizon`, `YangMillsFinite`, `YangMillsContinuum`

## Use References

- For commands and standard runs: read `references/commands.md`
- For the current module ownership picture: read `references/module-map.md`
- For generic frontier prompts over the current repo state: read `references/frontier-prompt.md`
- For generic bridge/debt review prompts: read the other prompt files under `references/`

## Agent Discipline

- Build before assuming a path is stable.
- Prefer file and graph evidence over intuition.
- Use graph reports to choose the next file, not to replace code reading.
- The Lean kernel decides what is true.
