# LeanTrail

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current for this subsystem, but subordinate to repo-wide authority docs and code.
> See: [README.md](../README.md), [docs/README.md](../docs/README.md), [docs/CODEBASE_STATUS.md](../docs/CODEBASE_STATUS.md)

LeanTrail is the repository’s graph-query and conformance layer built on top of
generated declaration/process artifacts.

It is a read model, not the theorem authority.

## Current Role

LeanTrail provides:

- graph snapshot building
- export to external carriers
- conformance checking between carriers
- Arango ingestion and analysis helpers
- failure/path-lock/hole-packet workflows

The maintained tools live under `tools/leantrail/`.

## Main Commands

```bash
lake script run leantrailConformance
lake script run leantrailExport
lake script run leantrailArangoIngest
lake script run leantrailArangoPhysicsEval
lake script run leantrailFailureHarvest
lake script run leantrailPathLock
lake script run leantrailHolePackets
```

Canonical snapshot output examples:

- `artifacts/leantrail/graph_snapshot.json`
- `artifacts/leantrail/conformance_report.json`
- `artifacts/leantrail/arango_ingest_report.json`

## Trust Rule

Use LeanTrail to navigate and compare artifact carriers. Use Lean source to
settle theorem truth.
