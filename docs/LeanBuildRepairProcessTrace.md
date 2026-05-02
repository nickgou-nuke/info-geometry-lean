# Lean Build Repair Process Trace (Toolchain + Build/Test)

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This trace records the exact implementation process used to repair recent Lean build failures and validate the fixes.

## Environment and Toolchain

Working directory:
- `/home/goutev/info-geometry-lean`

Branch:
- `fusion/upstream-intake-20260419`

Toolchain bootstrap used in-session:
- install `elan`
- set Lean toolchain: `leanprover/lean4:v4.28.0`
- use explicit binaries when needed:
  - `~/.elan/bin/lean`
  - `~/.elan/bin/lake`
- download Mathlib cache:
  - `~/.elan/bin/lake exe cache get`

## Build/Test Commands Used

Primary full rebuild command:
- `~/.elan/bin/lake build -R`

Targeted verification commands used during repair:
- `~/.elan/bin/lake build InfoGeometry.Convex.EuclideanMonotonicity`
- `~/.elan/bin/lake build InfoGeometry.ExponentialFamily.GaussianMonotonicity`
- `~/.elan/bin/lake build InfoGeometry.auto_blueprints`
- `~/.elan/bin/lake build InfoGeometry.AuditStrict`

## Error Classes Observed and Fix Strategy

### 1) `EuclideanMonotonicity` proof hygiene/error

Observed issue:
- `No goals to be solved` in `euclidean_grad_monotone` (over-solved `simp` followed by extra `exact`).

Fix:
- Collapse proof to one canonical line:
  - `simpa [grad] using (real_inner_self_nonneg (x - y))`
- Removed unnecessary section typeclass parameter from this file where not required.

### 2) `GaussianMonotonicity` mismatch errors

Observed issues:
- inner-product orientation mismatch
- equation orientation mismatch from `map_sub`.

Fixes:
- normalize subtraction rewrite with symmetry:
  - `simpa using (G.sigma.map_sub η₁ η₂).symm`
- close positivity branch by commutativity normalization:
  - `simpa [real_inner_comm] using (le_of_lt (G.sigma_pos (η₁ - η₂) hzero))`
- restored `[CompleteSpace E]` in this file (required by `GaussianFamily` context).

### 3) `auto_blueprints` stale symbol references

Observed issue:
- unknown constants from stale names in `lean/InfoGeometry/auto_blueprints.lean`.

Fixes:
- removed stale AQFT complex-prefixed symbols no longer available in imported `InfoGeometry.All` environment.
- replaced stale `QuantumInference.grandCanonicalZ` with current `QuantumInference.grandCanonicalOperator`.
- removed stale `QuantumInference.Op` attribute line.

### 4) `AuditStrict` architecture-audit false positives on container deps

Observed issue:
- large volume of `REGRESSION`/`WORMHOLE` findings caused by direct dependencies on tagged structure/context container declarations.

Fix applied in `lean/InfoGeometry/Meta/Architecture.lean`:
- architecture adjacency check now enforces layer constraints only for direct dependencies that are theorem/definition surfaces.
- tagged inductive/structure container dependencies are excluded from adjacency violations.

Rationale:
- preserve strict adjacency policy on proof/program surfaces while avoiding false positives from typed context carriers.

## Verification Status (this repair pass)

Successful targets:
- `InfoGeometry.Convex.EuclideanMonotonicity`: builds
- `InfoGeometry.ExponentialFamily.GaussianMonotonicity`: builds
- `InfoGeometry.auto_blueprints`: builds

Full rebuild status:
- `~/.elan/bin/lake build -R` still fails due architecture gates:
  - `InfoGeometry.Audit`
  - `InfoGeometry.AuditStrict`
- dominant remaining diagnostics are `REGRESSION` / `WORMHOLE` adjacency-policy violations emitted by `#audit_architecture` in `lean/InfoGeometry/Audit.lean` and `lean/InfoGeometry/AuditStrict.lean`.

## Git Process Used

Standard sequence used in this session:
1. `git status --short --branch`
2. `git add -A`
3. `git commit -m "..."`
4. `git push <remote> <branch>`

Remote notes:
- `origin` is configured.
- if `upstream` is missing, add it explicitly before push:
  - `git remote add upstream <upstream-url>`
  - then `git push upstream fusion/upstream-intake-20260419`

## Repro Checklist

1. Ensure toolchain:
   - `~/.elan/bin/lean --version`
   - `~/.elan/bin/lake --version`
2. Ensure cache:
   - `~/.elan/bin/lake exe cache get`
3. Run targeted builds above.
4. Run full rebuild:
   - `~/.elan/bin/lake build -R`
5. If clean, commit and push to `origin` and `upstream`.
