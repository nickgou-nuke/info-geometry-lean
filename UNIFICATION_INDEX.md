# Unification Index

This file is a maintained explanation of what counts as unification in the current repository.

A surface counts as real unification only if it gives:
- two independently meaningful sides;
- an explicit bridge or identification;
- a proved transport, invariance, or equivalence theorem across that bridge.

## Current owner surfaces

Representative current bridge owners include:
- `RelativePotential*` modules for projective/density/log-potential unification;
- `KMSSinkhorn*` modules for KMS, scalar-potential, and weighted transport connections;
- `RicciMongeAmpere` and `CalabiYau*` modules for geometry-side identifications;
- `KasparovCycle`, `AnalyticalIndex`, `Rosetta`, and related KK/index modules for operator/index transport.

## What does not count

The following do not count as unification on their own:
- wrapper theorems;
- capstone conjunctions;
- pass-through re-exports;
- renamed packaging over a lower bridge.

## Live signals

For current structural pressure and fake-interface contraction, use:
- `tools/infra/generate_theorem_surface_index.py`
- `tools/infra/generate_semantic_quotient.py`
- `tools/infra/generate_projection_coloring.py`
