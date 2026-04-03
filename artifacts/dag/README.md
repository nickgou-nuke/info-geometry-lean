# DAG Artifacts

This directory is the authoritative home of the maintained graph artifacts.

## Authoritative files

- `full_graph.json` — declaration DAG: `{nodes: [string], forward: [[nat, string]]}`
- `structural-topology.json` — SCC-level metadata: depth, dominators, root witnesses, layers
- `source-sink-bipartite.json` — packet and carrier incidence
- `representation-depth-tags.json` — Lean-enforced depth grammar tags

### `index/`

- `decls.jsonl` — declaration metadata: name, kind, module, file, line, docstring
- `edges.jsonl` — dependency edges: src, dst, edge kind (type/value)
- `morphisms.jsonl` — recognized morphisms (Hom/Equiv/Iso/Map) with domain/codomain
- `types.jsonl` — type-node records

### `process-flow/`

- `flow-edges.jsonl` — edge-local transport evidence with 9 dependency roles
- `process-events.jsonl` — event aggregation over observed edges
- `flow-cocycles.jsonl` — derived cocycle reports
- `comparison-candidates.jsonl` — bounded path comparison candidates
- `lawful-path-candidates.jsonl` — bounded ancestry/path candidates
- `defects.jsonl` — localized defect evidence with severity scoring

## How they are refreshed

```bash
# Main declaration graph + index + structural topology
python3 tools/infra/refresh_decl_graph.py

# Downstream reports
python3 tools/infra/generate_theorem_surface_index.py
python3 tools/infra/generate_source_sink_compression.py

# Process-flow layer
lake env lean --run lean/DAG/ProcessFlowExport.lean InfoGeometry.Audit artifacts/dag/process-flow
python3 tools/infra/generate_process_flow_report.py
```

See [tools/infra/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/infra/README.md) for the full maintained refresh order.

## Policy

- Treat `artifacts/dag/` as the source of truth for graph data.
- Treat `.build/` as a transient build cache or fallback, not as documented graph truth.
- `tools/pathing.py` resolves these paths canonically with `.build/` fallback.
- Regenerate these artifacts; do not hand-edit them.
