# DAG Artifacts

This directory is the authoritative home of the maintained graph artifacts.

## Authoritative files

- `full_graph.json`
- `structural-topology.json`
- `index/decls.jsonl`
- `index/edges.jsonl`
- `source-sink-bipartite.json`

## How they are refreshed

```bash
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/generate_theorem_surface_index.py
python3 tools/infra/generate_source_sink_compression.py
```

and the rest of the maintained report stack from [tools/infra/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/infra/README.md).

## Policy

- Treat `artifacts/dag/` as the source of truth for graph data.
- Treat `.build/` as a transient build cache or fallback, not as documented graph truth.
- Regenerate these artifacts; do not hand-edit them.
