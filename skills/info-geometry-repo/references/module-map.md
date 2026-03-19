# Module Map

## Domain spine

- `lean/InfoGeometry/Canonical/GeneratedFlow.lean`
  Flow / response spine.

- `lean/InfoGeometry/Canonical/WeylGaugeField.lean`
  Local gauge layer.

- `lean/InfoGeometry/Canonical/WeylTransport.lean`
  Large transport/integration layer.

- `lean/InfoGeometry/KK/KasparovCycle.lean`
  Bounded KK core.

- `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`
  Large analytical-index frontier.

- `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean`
  Vertical bridge into operator-algebraic readiness.

- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
  Capstone synthesis layer.

## Current graph picture

Trusted semantic block exports already show:

- `KasparovCycle`
  small but dense KK core

- `CompactOperatorBridge`
  thin adjunct module

- `Product`
  thin adjunct module

- `KasparovCompactOperator`
  thin adjunct module

- `OperatorAlgebraBridge`
  small vertical bridge

- `AnalyticalIndex`
  large bridge frontier

- `GrandSynthesis`
  large capstone synthesis web

## Operational conclusion

If the task is “find the missing KK-to-geometry bridge”, do not spend the first pass inside:
- `CompactOperatorBridge`
- `Product`
- `KasparovCompactOperator`

Start from:
- `KasparovCycle.analyticalIndex`
- `Canonical.AnalyticalIndex`
- `OperatorAlgebraBridge`
- `GrandSynthesis`

## Tooling map

- `lean/DAG/`
  graph kernel and analysis engine

- `lean/scripts/DAG/Exploration/`
  report generators

- `tools/semantic_block_export.py`
  trusted heavy-file semantic export orchestrator
