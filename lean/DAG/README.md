# DAG Subsystem

`lean/DAG/` is the Lean-side graph engine for this repository.

## What it exports

The maintained pipeline distinguishes four layers:

1. declaration DAG
   - atomic declaration-level truth
2. structural topology
   - SCC condensation, layers, dominators, witness paths
3. source-sink correspondence
   - packet/carrier incidence built downstream in Python
4. semantic block export
   - human-facing heavy-file structure for frontier work

These views should not be conflated.

## Current authoritative path

The current maintained declaration export is:

```bash
python3 tools/infra/refresh_decl_graph.py
```

which shells to:

```bash
lake env lean --run lean/DAG/Indexer.lean InfoGeometry.All InfoGeometry artifacts/dag/index artifacts/dag/full_graph.json artifacts/dag/structural-topology.json
```

The Python layer then builds:
- theorem-surface index
- source-sink bipartite correspondence
- causal and hotspot reports
- semantic quotient
- projection coloring

## Trust order

If graph layers disagree, trust in this order:
1. `artifacts/dag/full_graph.json` and `artifacts/dag/index/decls.jsonl`
2. `artifacts/dag/structural-topology.json`
3. `artifacts/dag/source-sink-bipartite.json`
4. `reports/dag/*`

## Semantic export

For heavy files, the trusted structure path is the external semantic-block export orchestrated from `tools/frontier/semantic_block_export.py`, not just the raw declaration graph.

## Intended use

Use the DAG subsystem for:
- causal order and rooted structure;
- ownership analysis;
- shell-versus-trunk separation;
- projection of lower-cluster structure onto upper theorem shells.

Do not use hotspot scores alone to decide refactors.
