---
name: info-geometry-repo
description: Use when working inside the InfoGeometry Lean 4 repository and you need the repo-specific theorem spine, DAG workflow, trusted artifact order, or the current representation-depth model.
---

# InfoGeometry Repo

Use this skill for repo topology, DAG refresh, canonical bridge ownership, theorem-surface debt, representation-depth audits, and safe workflow choices on heavy files.

If the task is about canonical theorem ownership or wrapper elimination, also read `/home/goutev/LEAN4/info-geometry-lean/skills/lean-canonicalization-policy/SKILL.md`.

## Read First

Read these in order:
1. `/home/goutev/LEAN4/info-geometry-lean/README.md`
2. `/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Audit.lean`
3. `/home/goutev/LEAN4/info-geometry-lean/docs/OperationalIntent.md`
4. `/home/goutev/LEAN4/info-geometry-lean/docs/Theory.md`
5. `/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md`
6. `/home/goutev/LEAN4/info-geometry-lean/tools/infra/README.md`

Then read only the specific reference or source files you need.

## Core Mental Model

The repo has three maintained surfaces:
1. domain layer under `lean/InfoGeometry/`
2. Lean-native architecture enforcement under `lean/InfoGeometry/Meta/` and `lean/InfoGeometry/Audit.lean`
3. tooling layer under `lean/DAG/`, `tools/infra/`, and `tools/frontier/`

The repo is one theory with several presentations.
The main formal burden is not to collapse those presentations into one surface, but to enforce the morphisms between them honestly.
Read stable files as owner, translator, coherence, or capstone surfaces over the same underlying theory.

The stable theory spine is a representation-depth ladder:
- `L0` Count
- `L1` Projective/Gauge
- `L2` Operator
- `L3` Krein/Clifford
- `L4` Transport
- `L5` Thermodynamic/Attention

Stable files should be read as exactly one of:
- owner
- translator
- coherence file
- capstone consumer

The DAG and Python layers are maintained memory.
Use them to restore context, surface transport pressure, and choose what to read next.
Do not use them to replace Lean source or invent ontology absent from code.

## Trust Order

If surfaces disagree, trust in this order:
1. Lean source
2. the native audit entrypoint
3. atomic DAG artifacts under `artifacts/dag/`
4. structural and source-sink artifacts
5. derived reports under `reports/dag/`
6. conceptual docs

## Hard Proof Policy

Treat vacuous success as failure.
- no `sorry`, `admit`, `axiom`, or equivalent gaps on the stable path
- trivial transport and aliasing do not count as proof progress
- capstone claims are only real when composed from lower repo owners already present

## Maintained DAG Pipeline

Use this exact main sequence:
1. `python3 tools/infra/run_locked_lake_build.py InfoGeometry.Audit`
2. `python3 tools/infra/refresh_decl_graph.py`
3. `python3 tools/infra/refresh_blueprint_tags.py`
4. `python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags`
5. `python3 tools/infra/generate_theorem_surface_index.py`
6. `python3 tools/infra/generate_source_sink_compression.py`
7. `python3 tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json`
8. `python3 tools/infra/check_bipartite_bleed.py`
9. `python3 tools/infra/generate_structural_dedup.py`
10. `python3 tools/infra/generate_structural_fibers.py`
11. `python3 tools/infra/generate_semantic_quotient.py`
12. `python3 tools/infra/generate_projection_coloring.py`
13. `python3 tools/infra/select_openclaw_target.py`
14. `python3 tools/infra/canonical_policy_lint.py`

Stable spine supplements:
- `python3 tools/infra/check_representation_depth.py`
- `python3 tools/infra/generate_representation_depth_graph.py`

Process-flow supplements:
- `lake env lean --run lean/DAG/ProcessFlowExport.lean InfoGeometry.Audit artifacts/dag/process-flow`
- `python3 tools/infra/generate_process_flow_report.py`

## Default Workflow

1. Identify whether the task is source ownership, proof stabilization, graph refresh, or heavy-file frontier work.
2. Read the target file and direct consumers before trusting any report.
3. Use locked builds for umbrella targets.
4. Run the Lean-native audit before trusting Python layer reports.
5. Use DAG reports to choose the next file, not to replace code reading.
6. Prefer representation-depth reports for rendered layer grammar and hotspot reports for residual debt only.
7. Use process-flow artifacts when the question is about transport, boundary, defect, or coherence pressure.

## Heavy Files

For heavy files, prefer semantic block export over guessing from the raw declaration graph:

```bash
python3 tools/frontier/semantic_block_export.py           <input.lean>           <output.json>           --server-mode stdlib           --inject-rpc-import           --skip-wait-for-diagnostics           --timeout 900
```

## Agent Discipline

- build before assuming a path is stable
- prefer direct file evidence over graph rhetoric
- keep ownership low and theorem surfaces load-bearing
- preserve real morphisms across representation levels; do not flatten them away
- the Lean kernel decides what is true
- Python reports summarize; they do not legislate architecture
