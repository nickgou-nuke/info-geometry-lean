# Roadmap

## Phase 1 — Library Scaffold (completed)
- Create domain folders and module files:
	- `InfoGeometry/{KL,Fenchel,Renyi,Cramer}.lean`
	- `Clifford/{Cl11,Supercharge,Grading}.lean`
	- `Projective/{Rays,ProjectiveMap}.lean`
	- `Prequantum/{Scaling,Bundle}.lean`
	- `Krein/{Metric,OrthogonalGroup}.lean`
- Add aggregate import hub: `InfoGeometry/Library.lean`.

## Phase 2 — Safe Extraction (next)
- Extract contiguous blocks from `InfoGeometry.lean` into the corresponding modules.
- Keep old symbol names and theorem statements unchanged during extraction.
- Keep `InfoGeometry.lean` as a compatibility facade importing extracted modules.

## Phase 3 — Mathlib Alignment
- Replace custom projective quotient with mathlib projectivization where possible.
- Prefer existing abstractions in:
	- `Mathlib/LinearAlgebra/Projectivization/*`
	- `Mathlib/Analysis/Convex/*`
	- `Mathlib/Algebra/CliffordAlgebra`
- Remove duplicate ad-hoc infrastructure once equivalent mathlib forms are in place.

## Migration Order
1. `InfoGeometry/{KL,Fenchel,Renyi,Cramer}.lean`
2. `Clifford/{Cl11,Grading,Supercharge}.lean`
3. `Projective/{Rays,ProjectiveMap}.lean`
4. `Prequantum/{Scaling,Bundle}.lean`
5. `Krein/{Metric,OrthogonalGroup}.lean`

## Build Policy
- Run `lake build` after each extracted module.
- Do not rewrite proofs and architecture in the same step.
- Refactor in mechanically checkable increments.
