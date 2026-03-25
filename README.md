# InfoGeometry in Lean 4

`info-geometry-lean` is a Lean 4 repository with two maintained layers:

1. a theorem library under `lean/InfoGeometry/`;
2. a declaration-graph and semantic-export toolchain under `lean/DAG/`, `tools/infra/`, and `tools/frontier/`.

The repository is not documented correctly by speculative synthesis notes, generated report snapshots, or stale hotspot counts. The authoritative current-state documents are the operational ones listed below.

## Read This First

1. [Installation.md](/home/goutev/LEAN4/info-geometry-lean/Installation.md)
2. [NEWCOMER_PATH.md](/home/goutev/LEAN4/info-geometry-lean/NEWCOMER_PATH.md)
3. [docs/README.md](/home/goutev/LEAN4/info-geometry-lean/docs/README.md)
4. [lean/DAG/README.md](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md)
5. [tools/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/README.md)
6. [blueprint/README.md](/home/goutev/LEAN4/info-geometry-lean/blueprint/README.md)

If you are working as an agent inside this repo, also use:
- [skills/info-geometry-repo/SKILL.md](/home/goutev/LEAN4/info-geometry-lean/skills/info-geometry-repo/SKILL.md)
- [skills/lean-canonicalization-policy/SKILL.md](/home/goutev/LEAN4/info-geometry-lean/skills/lean-canonicalization-policy/SKILL.md)

## What Is Maintained

### Lean library
The main publication umbrellas are:
- [InfoGeometry.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry.lean)
- [InfoGeometry/Library.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Library.lean)
- [InfoGeometry/Canonical/All.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/All.lean)
- [InfoGeometry/All.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/All.lean)

The current repository is organized around:
- substrate layers such as `Core`, `Convex`, `Measure`, `MeasureProjective`, `Projective`, `Krein`, `Singular`, and `Jordan`;
- canonical bridge layers under `lean/InfoGeometry/Canonical/`;
- derived quantum and KK consumers under `Quantum` and `KK`.

### Graph and audit tooling
The maintained graph workflow lives under:
- [lean/DAG](/home/goutev/LEAN4/info-geometry-lean/lean/DAG)
- [tools/infra](/home/goutev/LEAN4/info-geometry-lean/tools/infra)
- [tools/frontier](/home/goutev/LEAN4/info-geometry-lean/tools/frontier)

The authoritative graph artifacts live under:
- [artifacts/dag](/home/goutev/LEAN4/info-geometry-lean/artifacts/dag)

Derived readable outputs live under:
- [reports/dag](/home/goutev/LEAN4/info-geometry-lean/reports/dag)
- [docs/auto/index.md](/home/goutev/LEAN4/info-geometry-lean/docs/auto/index.md)

Those derived outputs must be regenerated. They are not hand-maintained source documents.

## Canonicalization Policy

The repository is being reorganized by the following structural rules:
- one concept, one owner file;
- umbrella files import and re-export, but should not own mathematics;
- wrapper-heavy public theorem surfaces should be internalized or split;
- direct file analysis comes before graph analysis;
- semantic quotient and projection coloring are used only after code is stable.

In practice this means that mixed umbrella files are split into lower owners. Recent examples include:
- `KMSSinkhornBridge` into seed-state, scalar-potential, and weighted-transport layers;
- `AQFTOperatorInterface` into signatures, Hilbert compression, readiness, and endpoints;
- `CalabiYauBridge` into metric/Ricci, RN/Monge–Ampère, and W layers;
- `ConnesArakiFramework` into generic carrier/core plus Tomita specialization.

## Build Entry Points

Use the locked wrapper for full or umbrella builds:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.All
python3 tools/infra/run_locked_lake_build.py InfoGeometry.All
```

For local quality checks, the repo-level entrypoint is:

```bash
lake script run strictCheck
```

## Maintained DAG Refresh Order

Use this exact order when refreshing the maintained graph reports:

```bash
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/refresh_blueprint_tags.py
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags
python3 tools/infra/generate_theorem_surface_index.py
python3 tools/infra/generate_source_sink_compression.py
python3 tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json
python3 tools/infra/check_bipartite_bleed.py
python3 tools/infra/generate_structural_dedup.py
python3 tools/infra/generate_structural_fibers.py
python3 tools/infra/generate_semantic_quotient.py
python3 tools/infra/generate_projection_coloring.py
python3 tools/infra/select_openclaw_target.py
```

Run these sequentially. Do not read `reports/dag/*` as current until the sequence has finished.

## Documentation Policy

The documentation corpus is split into three classes:
- authoritative operational docs: root READMEs, tooling READMEs, DAG docs, installation, newcomer path;
- conceptual notes under [docs/](/home/goutev/LEAN4/info-geometry-lean/docs), which are topic maps and non-authoritative synthesis notes;
- generated artifacts under `reports/`, `docs/auto/`, and `artifacts/dag/`.

If a document claims live repo state, it must be updated from code, not from prior prose.
