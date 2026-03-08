# Implementation Plan: Replace Legacy Axiom Facades

## Scope
- Remove legacy `Assumptions/Axioms/Degree` compatibility layers.
- Replace with canonical modules whose assumptions are explicit in theorem signatures.
- Keep the default build green under `lake build -R --wfail`.

## Audit Tool
- Script: `scripts/audit_surrogates.sh`
- Purpose: flag keywords such as `placeholder`, `surrogate`, `legacy`, `scaffold`, `tautology`.
- Usage:
  - `bash scripts/audit_surrogates.sh`

## Phases
1. Phase 1: Manifold Degree
  - Introduce canonical manifold-degree module in finite/discrete settings.
  - Remove old assumption-backed degree path from default surface.
2. Phase 2: Determinant/GL-SL Surface
  - Re-home determinant group interface to canonical namespace.
  - Eliminate remaining references to old determinant facade names.
3. Phase 3: Surrogate Hardening
  - Replace flagged placeholder theorems with explicit contracts or concrete proofs.
  - Keep interpretation docs separated from proved statements.
4. Phase 4: Publish Gate
  - Run full build + strict checks.
  - Produce a short registry of remaining non-constructive assumptions.

## Status
- Completed:
  - Removed `InfoGeometry.Assumptions*`, `InfoGeometry.Axioms`, and `InfoGeometry.Degree`.
  - Added:
    - `lean/InfoGeometry/Canonical/ManifoldDegreeCore.lean`
    - `lean/InfoGeometry/Canonical/ManifoldDegree.lean`
  - Wired canonical imports through `InfoGeometry.Canonical.All` and `InfoGeometry.Canonical.Geometry`.
- Next:
  - Phase 2 (Determinant/GL-SL surface).
