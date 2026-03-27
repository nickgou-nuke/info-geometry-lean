# DAG Subsystem

`lean/DAG/` is the Lean-side graph export layer for this repository.
It is not the sole owner of architectural grammar anymore; depth legality now starts in:
- [Architecture.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Meta/Architecture.lean)
- [Audit.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Audit.lean)

## Graph Layers

Keep these graph views distinct:
1. declaration DAG: atomic declaration-to-declaration dependency truth
2. structural topology: SCC condensation, layers, dominators, witness paths
3. source-sink correspondence: packet and carrier incidence built downstream in Python
4. semantic export: heavy-file block structure for frontier work
5. representation-depth overlays: Lean-enforced depth grammar projected onto the authoritative DAG

## Authoritative Export Path

The declaration graph is refreshed with:

```bash
python3 tools/infra/refresh_decl_graph.py
```

which runs the Lean-side indexer and writes:
- `artifacts/dag/full_graph.json`
- `artifacts/dag/index/decls.jsonl`
- `artifacts/dag/index/edges.jsonl`
- `artifacts/dag/structural-topology.json`

Downstream Python tooling then derives source-sink, causal, theorem-surface, semantic quotient, and representation-depth reports.
Those reports should agree with the Lean-native audit, not replace it.

## Trust Order

If graph-derived surfaces disagree, trust:
1. Lean source and the native audit under `lean/InfoGeometry/Meta/` and `lean/InfoGeometry/Audit.lean`
2. `artifacts/dag/full_graph.json` and `artifacts/dag/index/decls.jsonl`
3. `artifacts/dag/structural-topology.json`
4. `artifacts/dag/source-sink-bipartite.json`
5. `reports/dag/*`

## Intended Use

Use the DAG subsystem for:
- causal order and rooted structure
- owner and dependency analysis
- theorem-surface and shell pressure analysis
- representation-depth legality and bicategorical reporting

Do not use a single hotspot heuristic as the whole theory map.
