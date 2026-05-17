# Tooling Overview

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current for this subsystem, but subordinate to repo-wide authority docs and code.
> See: [README.md](../README.md), [docs/README.md](../docs/README.md), [docs/CODEBASE_STATUS.md](../docs/CODEBASE_STATUS.md)

This directory contains the maintained script surface around the Lean codebase.

## Current Maintained Lanes

- `tools/infra/`
  build orchestration, DAG refresh/reporting, audits, packet workflows
- `tools/frontier/`
  proof-session and semantic/frontier helpers
- `tools/docs/`
  documentation refresh helpers
- `tools/observability/`
  static Lean graph overlay, wrapper dedup, auto-tagging, and audit reports
  - compatibility wrapper: `tools/observability/lean_graph_overlay.py`
- `tools/leantrail/`
  LeanTrail conformance, export, ingest, and path/failure tooling

There is also a real Python package under `src/igf/` that now owns a growing
part of the artifact pipeline and CLI surface.

## Live Entrypoints

Lake-managed commands from `lakefile.lean`:

- `lake script run changedVerify`
- `lake script run dagStatus`
- `lake script run dagRefresh`
- `lake script run dagReports`
- `lake script run dagDoctor`
- `lake script run dagAll`
- `lake script run leantrailConformance`
- `lake script run leantrailExport`
- `lake script run leantrailArangoIngest`
- `lake script run leantrailArangoPhysicsEval`
- `lake script run leantrailFailureHarvest`
- `lake script run leantrailPathLock`
- `lake script run leantrailHolePackets`

Python CLIs:

- `igf`
- `infogeometry`

## Wrapper Rule

Many top-level `tools/*.py` files are compatibility wrappers or convenience
entrypoints. When changing behavior, prefer editing the maintained module under
its owning subdirectory or under `src/igf/`.

## Start Here

- [infra/README.md](infra/README.md)
- [docs/README.md](docs/README.md)
- [../docs/OperatorQuickstart.md](../docs/OperatorQuickstart.md)
- [../docs/DAGTroubleshooting.md](../docs/DAGTroubleshooting.md)
- [../leantrail/README.md](../leantrail/README.md)
