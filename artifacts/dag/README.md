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

Policy:
- treat `artifacts/dag/` as the documented public declaration-graph lane
- treat `.build/` as a transient Lean build cache and compatibility fallback only
- regenerate these artifacts; do not hand-edit them
