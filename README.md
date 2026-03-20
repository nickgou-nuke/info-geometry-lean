# InfoGeometry in Lean 4

This repository has two tightly coupled layers:

1. a Lean 4 theory library for information geometry, operator-algebraic structure, gauge transport, chiral/index constructions, and synthesis modules such as `GrandSynthesis`;
2. a semantic DAG engine that extracts declaration-level and source-block-level theory topology from Lean while filtering elaborator noise for heavy modules.

It is therefore both a theorem repository and a structural analysis environment for the theory itself.

If you are new to the repository, start with [NEWCOMER_PATH.md](/home/goutev/LEAN4/info-geometry-lean/NEWCOMER_PATH.md) before diving into the full DAG/tooling stack.
If you want the semantic “top view” of the theory, read [THEORY_CANOPY.md](/home/goutev/LEAN4/info-geometry-lean/THEORY_CANOPY.md).
If your interest is the deeper measure / RN / gauge substrate, also read [THEORY_CANOPY_RN_GAUGE.md](/home/goutev/LEAN4/info-geometry-lean/THEORY_CANOPY_RN_GAUGE.md).
If you want the shortest exact path through the Universal Volume / RN stack, read [UNIVERSAL_VOLUME_STACK.md](/home/goutev/LEAN4/info-geometry-lean/UNIVERSAL_VOLUME_STACK.md).
If you want the current trust/debt boundary for assumptions, wrappers, and surrogate surfaces, read [SURROGATE_INDEX.md](/home/goutev/LEAN4/info-geometry-lean/SURROGATE_INDEX.md).
If you want the current alias/vacuity debt boundary, read [VACUITY_INDEX.md](/home/goutev/LEAN4/info-geometry-lean/VACUITY_INDEX.md).
If you want the current thin-bridge audit for definitional identities and direct-forward bridge surfaces, read [BRIDGE_THINNESS_INDEX.md](/home/goutev/LEAN4/info-geometry-lean/BRIDGE_THINNESS_INDEX.md).

## Verified Shape

Current repository scale:
- Lean files under `lean/`: `444`
- Lean LOC under `lean/`: `74,329`

Trusted semantic block exports already exist for large capstones:
- `GrandSynthesis`: `56` semantic block nodes, `90` edges, `30` skeleton nodes
- `AnalyticalIndex`: `59` semantic block nodes, `209` edges, `42` skeleton nodes
- `KasparovCycle`: `7` semantic block nodes, `26` edges, `4` skeleton nodes

These are produced through the external stdlib server path, not through fragile in-process elaboration.

Current trusted multi-module frontier graph:
- `128` semantic block nodes
- `647` edges
- `319` cross-module edges

The first verified vertical bridge is:

`InfoGeometry.KK.KasparovCycle.analyticalIndex`
→ `InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`
→ `InfoGeometry.Canonical.GrandSynthesis.*`

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
- `tools/skynet_v2.py`
  Report-only semantic frontier explorer over trusted semantic block graphs.

## Current vs Legacy

Use this split when entering the repository for the first time.

| Surface | Status | What to use it for |
| --- | --- | --- |
| `lean/InfoGeometry/Canonical`, `lean/InfoGeometry/KK`, `lean/InfoGeometry/Library.lean` | Current | Main theorem library and publication surface |
| `lean/DAG`, `lean/scripts/DAG/Exploration` | Current | Graph extraction, semantic export, diagnostics, frontier analysis |
| `tools/semantic_block_export.py`, `tools/skynet_v2.py`, `tools/update_repo_docs.py` | Current | Trusted heavy-module export and auto-doc/frontier workflow |
| `docs/auto/index.md`, `lean/DAG/README.md`, `skills/info-geometry-repo/` | Current | Operational documentation and agent bootstrap |
| `archive/legacy/` | Archived but useful | Historical automation and scratch material worth mining for ideas, but not part of the supported build surface |
| `reports/dag/` | Generated / ignore for editing | Untracked analysis artifacts regenerated from the current code |

The archive is intentionally kept in-tree for provenance and idea recovery. Start with current surfaces first, then consult [archive/README.md](/home/goutev/LEAN4/info-geometry-lean/archive/README.md) only if you are explicitly researching historical approaches.

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
python3 -m py_compile tools/skynet_v2.py
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
The generated auto status page lives at [index.md](/home/goutev/LEAN4/info-geometry-lean/docs/auto/index.md).

## Frontier Discovery

The current frontier-discovery path is:

1. export trusted semantic block JSONs for heavy modules;
2. load them into `tools/skynet_v2.py`;
3. run diffusion from a named seed using `--walk forward|reverse|both`;
4. use the resulting frontier packet for candidate bridge statements, not proofs.

Example:

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

Operational rule:
- `forward` shows dependencies/bases,
- `reverse` shows downstream consumers,
- `both` shows the local bridge kernel around the seed.

To regenerate the tracked auto status page from current local artifacts:

```bash
python3 tools/generate_auto_docs.py
```

To refresh the frontier packets and the tracked auto status page in one step:

```bash
python3 tools/update_repo_docs.py
```

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
- reverse frontier discovery now reaches `GrandSynthesis` consumer theorems from the KK seed

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
For bridge work, the most relevant references are:
- `skills/info-geometry-repo/references/frontier-prompt.md`
- `skills/info-geometry-repo/references/bridge-candidates.md`

For historical context or discarded automation ideas, see [archive/README.md](/home/goutev/LEAN4/info-geometry-lean/archive/README.md).

## Release Integrity

The intended alpha-release policy is:
- keep the full `.git` history;
- exclude build garbage and generated DAG artifacts from the release archive;
- publish a source archive with checksum and signature;
- keep theorem source, DAG tooling, and orchestration scripts together as one reproducible unit.
