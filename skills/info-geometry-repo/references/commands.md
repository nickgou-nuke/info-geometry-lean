# Commands

## Core builds

Canonical umbrella:

```bash
lake build InfoGeometry.Canonical.All
```

Full rebuild:

```bash
lake build -R
```

DAG tooling:

```bash
lake build DAG semanticBlockExport semanticBlockServer
lake build scripts.DAG.Exploration.HarvestDiagnostics
lake build scripts.DAG.Exploration.LiftNaturalityDiagnostics
lake build scripts.DAG.Exploration.NaturalityPromoter
python3 -m py_compile tools/skynet_v2.py
```

## Trusted semantic block export

Template:

```bash
python3 tools/semantic_block_export.py \
  lean/InfoGeometry/Canonical/<Module>.lean \
  reports/dag/<Module>.semantic-block.stdlib.json \
  --server-mode stdlib \
  --inject-rpc-import \
  --skip-wait-for-diagnostics \
  --timeout 900 \
  --transcript reports/dag/<Module>.semantic-block.stdlib.transcript.jsonl \
  --stderr-log reports/dag/<Module>.semantic-block.stdlib.stderr.log
```

Known-good heavy examples:
- `GrandSynthesis`
- `AnalyticalIndex`
- `WeylTransport`
- `KasparovCycle`
- `OperatorAlgebraBridge`

## Frontier discovery

Reverse consumer search from the KK seed:

```bash
python3 tools/skynet_v2.py \
  --input reports/dag/KasparovCycle.semantic-block.stdlib.json \
  --input reports/dag/AnalyticalIndex.semantic-block.stdlib.json \
  --input reports/dag/OperatorAlgebraBridge.semantic-block.stdlib.json \
  --input reports/dag/GrandSynthesis.semantic-block.stdlib.json \
  --seed KasparovCycle.analyticalIndex \
  --walk reverse \
  --top 12 \
  --json-out reports/dag/skynet-v2-frontier-reverse.json \
  --md-out reports/dag/skynet-v2-frontier-reverse.md
```

Local bridge kernel around the seed:

```bash
python3 tools/skynet_v2.py \
  --input reports/dag/KasparovCycle.semantic-block.stdlib.json \
  --input reports/dag/AnalyticalIndex.semantic-block.stdlib.json \
  --input reports/dag/OperatorAlgebraBridge.semantic-block.stdlib.json \
  --input reports/dag/GrandSynthesis.semantic-block.stdlib.json \
  --seed KasparovCycle.analyticalIndex \
  --walk both \
  --top 12 \
  --json-out reports/dag/skynet-v2-frontier.json \
  --md-out reports/dag/skynet-v2-frontier.md
```

## Generated status page

```bash
python3 tools/generate_auto_docs.py
```

## End-to-end documentation refresh

Using current trusted semantic exports:

```bash
python3 tools/update_repo_docs.py
```

Including a fresh heavy-module semantic export pass:

```bash
python3 tools/update_repo_docs.py --refresh-exports
```

Self-optimization cycle sheet:

```bash
python3 tools/generate_self_optimization_report.py
```

Dry isolated optimization cycle:

```bash
python3 tools/run_optimization_cycle.py
```

## Declaration-level exports

Forward graph:

```bash
lake env lean --run lean/DAG/ExportForwardGraph.lean \
  InfoGeometry docs-map/module_graph.json InfoGeometry
```

Skeleton:

```bash
lake env lean --run lean/DAG/SkeletonExport.lean \
  InfoGeometry InfoGeometry docs-map/skeleton.json
```

## Categorical diagnostics

```bash
lake env lean --run lean/scripts/DAG/Exploration/HarvestDiagnostics.lean
lake env lean --run lean/scripts/DAG/Exploration/LiftNaturalityDiagnostics.lean
lake env lean --run lean/scripts/DAG/Exploration/NaturalityPromoter.lean
lake env lean --run lean/scripts/DAG/Exploration/SquarePromoter.lean
```
