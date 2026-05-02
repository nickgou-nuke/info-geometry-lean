# Generated Artifacts Policy

> Status: `current authority`
> Audited: 2026-05-02
> Note: Maintained against the live code surface.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This repository separates source of truth from generated output.

## Source Of Truth

Treat these as canonical:

- `lean/`
- `src/igf/`
- `tools/`
- `tests/`
- `lakefile.lean`
- `pyproject.toml`
- the maintained entry docs listed in [README.md](README.md)

## Generated Or Snapshot Surfaces

Treat these as generated, reproducible, or point-in-time snapshots:

- `reports/`
- `artifacts/`
- `docs/auto/`
- generated run folders under `handover/` or other runtime trees

Common examples include:

- DAG indexes and overlays
- LeanTrail snapshots and conformance outputs
- Arango export or ingest payloads
- process-flow packets
- research/eval summaries
- frontier packets
- optimization run summaries

## Rule

If a generated file is important, regenerate it from code and tooling instead of
editing the prose snapshot by hand.

Use:

```bash
lake script run dagAll
igf build
igf run
igf validate
```

and the maintained script lanes under `tools/infra/`, `tools/frontier/`,
`tools/docs/`, and `tools/leantrail/`.
