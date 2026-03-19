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
2. [lean/DAG/README.md](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md)
3. [docs/auto/index.md](/home/goutev/LEAN4/info-geometry-lean/docs/auto/index.md)

Then run:

```bash
lake build InfoGeometry.Canonical.All
```

That gives you the main theorem umbrella before you touch any graph tooling.

## The Main Theory Route

If your interest is the mathematics first, orient yourself through these files:

1. `lean/InfoGeometry/Canonical/GeneratedFlow.lean`
2. `lean/InfoGeometry/KK/KasparovCycle.lean`
3. `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`
4. `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean`
5. `lean/InfoGeometry/Canonical/GrandSynthesis.lean`

That route roughly follows:

`GeneratedFlow` -> `KasparovCycle` -> `AnalyticalIndex` -> `OperatorAlgebraBridge` -> `GrandSynthesis`

## The Tooling Route

If your interest is the meta-tooling first, orient yourself through these files:

1. `lean/DAG/BlockExport.lean`
2. `lean/DAG/ServerExport.lean`
3. `lean/scripts/DAG/Exploration/SemanticBlockServer.lean`
4. `tools/semantic_block_export.py`
5. `tools/skynet_v2.py`

That route roughly follows:

Lean provenance extraction -> external semantic export -> frontier diffusion

## What Is Current

Use these as the active, supported surfaces:

| Area | Current entrypoints |
| --- | --- |
| theorem library | `lean/InfoGeometry/`, `lean/InfoGeometry/Library.lean`, `lean/InfoGeometry/Canonical/All.lean` |
| graph engine | `lean/DAG/` |
| Lean report wrappers | `lean/scripts/DAG/Exploration/` |
| trusted heavy-module export | `tools/semantic_block_export.py` |
| frontier analysis | `tools/skynet_v2.py` |
| auto docs refresh | `tools/update_repo_docs.py` |
| agent bootstrap | `skills/info-geometry-repo/` |

## What To Ignore At First

Do not start here unless you have a specific reason:

| Surface | Why not first |
| --- | --- |
| `archive/` | useful for provenance and idea recovery, but not authoritative for current work |
| `reports/dag/` | generated artifacts, not source of truth |
| `archive/legacy/scripts/skynet.py` | historical automation path replaced by `tools/skynet_v2.py` |
| archived scratch Lean files | design archaeology, not current build surface |
| `lean/InfoGeometry/Unstable/` | quarantine area, not the canonical publication path |

## First Useful Commands

Build the main theorem surface:

```bash
lake build InfoGeometry.Canonical.All
```

Build the DAG/tooling surface:

```bash
lake build DAG semanticBlockExport semanticBlockServer
```

Refresh tracked frontier/docs artifacts from current local graph data:

```bash
python3 tools/update_repo_docs.py
```

Run the trusted heavy-module semantic export path:

```bash
python3 tools/semantic_block_export.py \
  lean/InfoGeometry/Canonical/GrandSynthesis.lean \
  reports/dag/GrandSynthesis.semantic-block.stdlib.json \
  --server-mode stdlib \
  --inject-rpc-import \
  --skip-wait-for-diagnostics \
  --timeout 900
```

Run frontier discovery from the KK seed:

```bash
python3 tools/skynet_v2.py \
  --input reports/dag/KasparovCycle.semantic-block.stdlib.json \
  --input reports/dag/AnalyticalIndex.semantic-block.stdlib.json \
  --input reports/dag/OperatorAlgebraBridge.semantic-block.stdlib.json \
  --input reports/dag/GrandSynthesis.semantic-block.stdlib.json \
  --seed KasparovCycle.analyticalIndex \
  --walk reverse \
  --top 12
```

## Current Verified Story

The current repository documentation and tooling support this verified bridge:

`InfoGeometry.KK.KasparovCycle.analyticalIndex`
-> `InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`
-> `InfoGeometry.Canonical.GrandSynthesis.*`

This is the main newcomer mental model for the current frontier.

## How To Use The Audit Note

The outsider audit at
[codebase-functionality-structure-audit-20260319.md](/home/goutev/LEAN4/info-geometry-lean/reports/codebase-functionality-structure-audit-20260319.md)
is useful as a second-pass architectural summary.

Use it after this document, not before it.

Reason:

- this file tells you where to start
- the audit note tells you what another reader independently reconstructed

## If You Are A Coding Agent

Start with:

1. this file
2. [README.md](/home/goutev/LEAN4/info-geometry-lean/README.md)
3. [lean/DAG/README.md](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md)
4. [skills/info-geometry-repo/SKILL.md](/home/goutev/LEAN4/info-geometry-lean/skills/info-geometry-repo/SKILL.md)

Then decide whether the task is:

- theorem-library work
- graph extraction
- frontier discovery
- documentation refresh
- historical archaeology in `archive/`
