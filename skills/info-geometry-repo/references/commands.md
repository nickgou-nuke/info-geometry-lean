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
