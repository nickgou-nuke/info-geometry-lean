# One Theory, Many Presentations

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current conceptual map, but subordinate to current code and status docs.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This repository should be read as one evolving theory presented through several
adjacent code surfaces.

## Current Meaning

The unifying idea is not that every file says the same thing in prose. It is
that related owner, translator, and audit surfaces can be checked against each
other in code.

## Active Structural Split

Today the theory is carried by:

- Lean theorem sources under `lean/`
- architecture and audit surfaces under `lean/InfoGeometry/Audit.lean` and
  `lean/InfoGeometry/Meta/`
- artifact and graph tooling under `src/igf/` and `tools/`

## Reading Rule

Read the theory through adjacent ownership:

- start from current owner files
- follow direct consumers
- use docs to orient yourself, not to override the code

## Current Stable Corridor

One of the cleanest current corridors remains:

- `PositiveMeasure`
- `Projective.Normalize`
- `PositiveRayCore`
- `RelativePotentialCore`
- `RelativePotentialCountBridge`
- `RelativeSurprisalOperatorLift`

For a practical map, use [ModuleMap.md](ModuleMap.md).
