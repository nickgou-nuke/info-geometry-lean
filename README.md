# InfoGeometry in Lean 4

This repository has two tightly coupled layers:

1. a Lean 4 theory library for information geometry, operator-algebraic structure, gauge transport, chiral/index constructions, and synthesis modules such as `GrandSynthesis`;
2. a semantic DAG engine that extracts declaration-level and source-block-level theory topology from Lean while filtering elaborator noise for heavy modules.

It is therefore both a theorem repository and a structural analysis environment for the theory itself.

## Verified Shape

Current repository scale:
- Lean files under `lean/`: `444`
- Lean LOC under `lean/`: `74,329`

Trusted semantic block exports already exist for large capstones:
- `GrandSynthesis`: `56` semantic block nodes, `90` edges, `30` skeleton nodes
- `AnalyticalIndex`: `59` semantic block nodes, `209` edges, `42` skeleton nodes
- `KasparovCycle`: `7` semantic block nodes, `26` edges, `4` skeleton nodes

These are produced through the external stdlib server path, not through fragile in-process elaboration.

## Repository Map

### Domain layer

- `lean/InfoGeometry/Canonical/GeneratedFlow.lean`
  Generator / flow / response spine.
- `lean/InfoGeometry/Canonical/WeylGaugeField.lean`
  Local Weyl-gauge layer.
- `lean/InfoGeometry/Canonical/WeylTransport.lean`
  Heavy transport/integration layer.
- `lean/InfoGeometry/KK/KasparovCycle.lean`
  Bounded KK core.
- `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`
  Large chiral/index-invariance web.
- `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean`
  Vertical bridge toward operator-algebra readiness.
- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
  Capstone synthesis layer.

### Tooling layer

- `lean/DAG/`
  Importable graph/topology engine.
- `lean/scripts/DAG/Exploration/`
  Lean report generators and entrypoints.
- `tools/semantic_block_export.py`
  External Python LSP/RPC orchestrator for trusted semantic block export.
- `reports/dag/`
  Generated graph artifacts. These are intentionally untracked.

## Build

Canonical umbrella build:

```bash
lake build InfoGeometry.Canonical.All
```

Full project rebuild:

```bash
lake build -R
```

DAG and semantic-export tooling:

```bash
lake build DAG semanticBlockExport semanticBlockServer
lake build scripts.DAG.Exploration.HarvestDiagnostics
lake build scripts.DAG.Exploration.LiftNaturalityDiagnostics
lake build scripts.DAG.Exploration.NaturalityPromoter
```

## Semantic DAG Export

For large Mathlib-heavy modules, use the trusted stdlib server path:

```bash
python3 tools/semantic_block_export.py \
  lean/InfoGeometry/Canonical/GrandSynthesis.lean \
  reports/dag/GrandSynthesis.semantic-block.stdlib.json \
  --server-mode stdlib \
  --inject-rpc-import \
  --skip-wait-for-diagnostics \
  --timeout 900 \
  --transcript reports/dag/GrandSynthesis.semantic-block.stdlib.transcript.jsonl \
  --stderr-log reports/dag/GrandSynthesis.semantic-block.stdlib.stderr.log
```

Why this path matters:
- it uses a separate `lean --server` process;
- it avoids host/guest `[init]` collisions on heavy files;
- it produces semantic block graphs filtered to `primaryProduces`, while preserving `auxProduces` in the causal substrate.

For advanced tooling details, read [lean/DAG/README.md](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md).

## How To Read The Theory Topology

There are three useful views:

1. declaration DAG
- best for SCCs, dominators, and global bottlenecks

2. block export
- best for source attribution and minimal slices

3. semantic block graph
- best for human-facing theory structure and bridge hunting

Current KK frontier picture:
- `KasparovCycle` is the real KK core
- `CompactOperatorBridge`, `Product`, and `KasparovCompactOperator` are thin adjunct modules
- the first large vertical frontier is `KasparovCycle.analyticalIndex -> Canonical.AnalyticalIndex`

## Agent Bootstrap

If you are using a coding agent, the minimal bootstrap sequence is:

1. read [docs/keyword_index.md](/home/goutev/LEAN4/info-geometry-lean/docs/keyword_index.md)
2. read [lean/DAG/README.md](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md)
3. build the canonical umbrella
4. decide whether the task is:
   global topology,
   single-file semantic export,
   bridge closing,
   or frontier analysis

There is also a repo-specific agent skill in `skills/info-geometry-repo/`.

## Release Integrity

The intended alpha-release policy is:
- keep the full `.git` history;
- exclude build garbage and generated DAG artifacts from the release archive;
- publish a source archive with checksum and signature;
- keep theorem source, DAG tooling, and orchestration scripts together as one reproducible unit.
