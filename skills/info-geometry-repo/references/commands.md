# Commands

## Core builds

Canonical umbrella:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.All
```

Full umbrella:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.All
```

Strict local check:

```bash
lake script run strictCheck
```

## Maintained DAG and blueprint workflow

Run the maintained pipeline in this exact order:

```bash
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/refresh_blueprint_tags.py
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags
python3 tools/infra/generate_theorem_surface_index.py
python3 tools/infra/generate_source_sink_compression.py
python3 tools/infra/generate_causal_report.py \
  --out reports/dag/true-root-order.md \
  --json-out reports/dag/true-root-order.json
python3 tools/infra/check_bipartite_bleed.py
python3 tools/infra/generate_structural_dedup.py
python3 tools/infra/generate_structural_fibers.py
python3 tools/infra/generate_semantic_quotient.py
python3 tools/infra/generate_projection_coloring.py
python3 tools/infra/select_openclaw_target.py
```

Optional LeanArchitect exports after the maintained refresh:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags:blueprint
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags:blueprintJson
```

## Trusted semantic block export

```bash
python3 tools/frontier/semantic_block_export.py \
  lean/InfoGeometry/Canonical/<Module>.lean \
  reports/dag/<Module>.semantic-block.stdlib.json \
  --server-mode stdlib \
  --inject-rpc-import \
  --skip-wait-for-diagnostics \
  --timeout 900
```

## Frontier discovery

Use `tools/frontier/skynet_v2.py` only against fresh semantic-block exports.
Do not treat old prompt packets or older report snapshots as live frontier evidence.

## Generated documentation

```bash
python3 tools/docs/generate_auto_docs.py
python3 tools/docs/update_repo_docs.py
```
