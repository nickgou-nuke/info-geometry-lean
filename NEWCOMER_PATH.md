# Newcomer Path

This document is the shortest practical path into the repository.

Use it if you are new to the codebase and need to answer three questions fast:

1. what is the repository for?
2. what should I read first?
3. what should I ignore until later?

## What This Repository Is

This repository has two active layers:

1. a large Lean 4 theorem library under `lean/InfoGeometry/`
2. a semantic DAG / frontier-analysis toolchain under `lean/DAG/`, `lean/scripts/DAG/Exploration/`, and `tools/`

So it is both:

- a formal mathematics / physics codebase
- a codebase that analyzes its own theorem topology

## The First 15 Minutes

Read these in order:

1. [README.md](/home/goutev/LEAN4/info-geometry-lean/README.md)
2. [THEORY_CANOPY.md](/home/goutev/LEAN4/info-geometry-lean/THEORY_CANOPY.md)
3. [UNIFICATION_INDEX.md](/home/goutev/LEAN4/info-geometry-lean/UNIFICATION_INDEX.md)
4. [lean/DAG/README.md](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md)
5. [docs/auto/index.md](/home/goutev/LEAN4/info-geometry-lean/docs/auto/index.md)
6. [THEORY_CANOPY_RN_GAUGE.md](/home/goutev/LEAN4/info-geometry-lean/THEORY_CANOPY_RN_GAUGE.md)

Then run the locked full build:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.All
```

If you only need the canonical publication surface first, use:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.All
```

## The Main Theory Routes

Choose one route instead of trying to read everything linearly.

### Route A: KK / analytical-index / synthesis

1. `lean/InfoGeometry/Canonical/GeneratedFlow.lean`
2. `lean/InfoGeometry/KK/KasparovCycle.lean`
3. `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`
4. `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean`
5. `lean/InfoGeometry/Canonical/GrandSynthesis.lean`

That route roughly follows:

`GeneratedFlow` -> `KasparovCycle` -> `AnalyticalIndex` -> `OperatorAlgebraBridge` -> `GrandSynthesis`

### Route B: modular / CPT / Rosetta

1. `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean`
2. `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean`
3. `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
4. `lean/InfoGeometry/Quantum/ModularAnomaly.lean`
5. `lean/InfoGeometry/Canonical/Rosetta.lean`

That route roughly follows:

`RealMajoranaCategory` -> `BogoliubovFockSuper` -> `TomitaTakesaki` -> `ModularAnomaly` -> `Rosetta`

### Route C: discrete shell / RG / phase boundary

1. `lean/InfoGeometry/Quantum/Hurwitz.lean`
2. `lean/InfoGeometry/Quantum/HurwitzRGFlow.lean`
3. `lean/InfoGeometry/Canonical/RGFlow.lean`
4. `lean/InfoGeometry/Quantum/KitaevChain.lean`

That route roughly follows:

`Hurwitz` -> `HurwitzRGFlow` -> `RGFlow` -> `KitaevChain`

## The Tooling Route

If your interest is the meta-tooling first, orient yourself through these files:

1. `lean/DAG/BlockExport.lean`
2. `lean/DAG/ServerExport.lean`
3. `lean/scripts/DAG/Exploration/SemanticBlockServer.lean`
4. `tools/frontier/semantic_block_export.py`
5. `tools/frontier/skynet_v2.py`

That route roughly follows:

Lean provenance extraction -> external semantic export -> frontier diffusion

## What Is Current

Use these as the active, supported surfaces:

| Area | Current entrypoints |
| --- | --- |
| theorem library | `lean/InfoGeometry/`, `lean/InfoGeometry/Library.lean`, `lean/InfoGeometry/Canonical/All.lean`, `lean/InfoGeometry/Quantum` |
| graph engine | `lean/DAG/` |
| Lean report wrappers | `lean/scripts/DAG/Exploration/` |
| trusted heavy-module export | `tools/frontier/semantic_block_export.py` |
| frontier analysis | `tools/frontier/skynet_v2.py` |
| auto docs refresh | `tools/docs/update_repo_docs.py` |
| agent bootstrap | `skills/info-geometry-repo/` |

## What To Ignore At First

Do not start here unless you have a specific reason:

| Surface | Why not first |
| --- | --- |
| `archive/` | useful for provenance and idea recovery, but not authoritative for current work |
| `reports/dag/` | generated artifacts, not source of truth |
| `archive/legacy/scripts/skynet.py` | historical automation path replaced by `tools/frontier/skynet_v2.py` |
| archived scratch Lean files | design archaeology, not current build surface |
| `lean/InfoGeometry/Unstable/` | quarantine area, not the canonical publication path |

## First Useful Commands

Build the full theorem surface:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.All
```

Build the canonical umbrella:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.All
```

Build the DAG/tooling surface:

```bash
lake build DAG semanticBlockExport semanticBlockServer
```

Refresh tracked frontier/docs artifacts from current local graph data:

```bash
python3 tools/docs/update_repo_docs.py
```

Run the trusted heavy-module semantic export path:

```bash
python3 tools/frontier/semantic_block_export.py \
  lean/InfoGeometry/Canonical/GrandSynthesis.lean \
  reports/dag/GrandSynthesis.semantic-block.stdlib.json \
  --server-mode stdlib \
  --inject-rpc-import \
  --skip-wait-for-diagnostics \
  --timeout 900
```

Run frontier discovery from the KK seed:

```bash
python3 tools/frontier/skynet_v2.py \
  --input reports/dag/KasparovCycle.semantic-block.stdlib.json \
  --input reports/dag/AnalyticalIndex.semantic-block.stdlib.json \
  --input reports/dag/OperatorAlgebraBridge.semantic-block.stdlib.json \
  --input reports/dag/GrandSynthesis.semantic-block.stdlib.json \
  --seed KasparovCycle.analyticalIndex \
  --walk reverse \
  --top 12
```

## Current Verified Stories

The synchronized newcomer mental models are now:

- KK/index/synthesis:
  `InfoGeometry.KK.KasparovCycle.analyticalIndex`
  -> `InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`
  -> `InfoGeometry.Canonical.GrandSynthesis.*`
- source-tension / Rosetta / modular anomaly:
  `Singular`, `RicciMongeAmpere`, `BogoliubovFockSuper`, `TomitaTakesaki`
  -> `InfoGeometry.Canonical.Rosetta.*`
  -> `InfoGeometry.Quantum.ModularAnomaly.*`
- discrete shell / RG / finite phase boundary:
  `InfoGeometry.Quantum.Hurwitz`
  -> `InfoGeometry.Quantum.HurwitzRGFlow`
  -> `InfoGeometry.Canonical.RGFlow`
  with finite topological phase crossing in `InfoGeometry.Quantum.KitaevChain`

## Second-Pass Architecture Notes

After this file, the best second-pass maps are:

1. [THEORY_CANOPY.md](/home/goutev/LEAN4/info-geometry-lean/THEORY_CANOPY.md)
2. [UNIFICATION_INDEX.md](/home/goutev/LEAN4/info-geometry-lean/UNIFICATION_INDEX.md)
3. [docs/keyword_index.md](/home/goutev/LEAN4/info-geometry-lean/docs/keyword_index.md)

Use those after this document, not before it.

## If You Are A Coding Agent

Start with:

1. this file
2. [README.md](/home/goutev/LEAN4/info-geometry-lean/README.md)
3. [THEORY_CANOPY.md](/home/goutev/LEAN4/info-geometry-lean/THEORY_CANOPY.md)
4. [lean/DAG/README.md](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md)
5. [skills/info-geometry-repo/SKILL.md](/home/goutev/LEAN4/info-geometry-lean/skills/info-geometry-repo/SKILL.md)

Then decide whether the task is:

- KK/index work
- modular/Rosetta work
- discrete phase/RG work
- graph extraction
- frontier discovery
- documentation refresh
- historical archaeology in `archive/`
