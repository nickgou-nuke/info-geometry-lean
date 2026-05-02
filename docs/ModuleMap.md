# Module Map

> Status: `current authority`
> Audited: 2026-05-02
> Note: Maintained against the live code surface.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This is the short practical map of the current codebase.

## Primary Entry Surfaces

Lean:

- `lean/InfoGeometry.lean`
- `lean/InfoGeometry/All.lean`
- `lean/InfoGeometry/Audit.lean`
- `lean/InfoGeometry/Meta/`

Python:

- `src/igf/cli.py`
- `src/igf/pipeline/`
- `src/igf/graph/`
- `src/igf/artifacts/`
- `tools/infra/`
- `tools/frontier/`
- `tools/docs/`
- `tools/leantrail/`

## Major Lean Families Present

The current `lean/InfoGeometry/` tree includes major families such as:

- `Algebraic`
- `Arithmetic`
- `Automorphic`
- `Canonical`
- `Compatibility`
- `Convex`
- `Core`
- `ExponentialFamily`
- `Geometry`
- `GrandCanonical`
- `Interpretation`
- `Krein`
- `LLM`
- `Meta`
- `OperatorAlgebra`
- `Projective`
- `Quantum`
- `SuperMetriplectic`
- `Thermodynamics`
- `Topological`
- `Twistor`

The practical rule is simple:

- use `Audit.lean` and `Meta/` to understand architecture and policy
- use owner modules under `Canonical/`, `Arithmetic/`, `Projective/`, and
  related families for the actual theorem surface
- use umbrella files only after you know the owner path you care about

## Major Python Families Present

`src/igf/` currently exposes:

- `config`
  environment and configuration loading
- `artifacts`
  artifact I/O, manifests, normalization adapters
- `graph`
  Arango collections, clients, query running, indexes
- `pipeline`
  build, validate, ingest, verify, report, orchestration
- `policy`
  claim-scope policy support

## Current Operator Commands

Start with:

```bash
lake script run changedVerify
lake script run dagStatus
lake script run dagDoctor
```

For the Python package:

```bash
igf preflight
igf build
igf validate
igf run
```

## Read By Task

If you need architecture:

- `lean/InfoGeometry/Audit.lean`
- `lean/InfoGeometry/Meta/`
- [OperationalIntent.md](OperationalIntent.md)

If you need tooling:

- [../tools/README.md](../tools/README.md)
- [../tools/infra/README.md](../tools/infra/README.md)
- [LeanTrail.md](LeanTrail.md)

If you need onboarding:

- [../Installation.md](../Installation.md)
- [../NEWCOMER_PATH.md](../NEWCOMER_PATH.md)

If you need current status:

- [CODEBASE_STATUS.md](CODEBASE_STATUS.md)
