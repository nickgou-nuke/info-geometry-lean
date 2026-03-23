# Declaration DAG Artifacts

This directory is the public authoritative home of the declaration-level DAG
artifacts used for causal-order analysis.

Current refresh path:

```bash
python3 tools/refresh_decl_graph.py
```

That wrapper calls:

```bash
lake env lean --run lean/DAG/Indexer.lean InfoGeometry.All InfoGeometry artifacts/dag/index artifacts/dag/full_graph.json
```

Authoritative inputs here:
- `artifacts/dag/full_graph.json`
- `artifacts/dag/index/decls.jsonl`

Derived reports live elsewhere:
- `reports/dag/true-root-order.{md,json}`
- `reports/dag/openclaw-targets.{md,json}`
- `reports/dag/missing-all-classification.{md,json}`
- `reports/dag/theorem-surface-index.{md,json}`
- `reports/dag/declaration-networkx.graphml`
- `reports/dag/module-networkx.graphml`
- `reports/dag/module-networkx.svg`
- `reports/dag/declaration-networkx-frontier.graphml`
- `reports/dag/module-networkx-frontier.graphml`
- `reports/dag/module-networkx-frontier.svg`
- `reports/dag/module-networkx-frontier-hotspots.graphml`
- `reports/dag/module-networkx-frontier-hotspots.svg`
- `reports/dag/module-networkx-frontier-hotspots.json`
- `reports/dag/frontier-burndown.md`
- `reports/dag/frontier-burndown.json`

Policy:
- treat `artifacts/dag/` as the documented public declaration-graph lane
- treat `.build/` as a transient Lean build cache and compatibility fallback only
- regenerate these artifacts; do not hand-edit them
