# Literature Digest: Black Book Ch61 injection: spectral-weighted decomposition

> Status: `historical handover`
> Audited: 2026-05-02
> Note: Workflow history and packet memory, not current repository authority.
> See: [README.md](../../../README.md), [docs/README.md](../../../docs/README.md), [docs/CODEBASE_STATUS.md](../../../docs/CODEBASE_STATUS.md)

## Packet Metadata
- Packet ID: `EXT-20260414-BLACKBOOK-61-SPECTRAL-WEIGHTED`
- Lane: `accepted`
- Status: `accepted`
- Coverage: `distilled`
- Generated: `2026-04-14T11:22:00+00:00`

## Provenance
- Source type: `manual`
- Source ref: `docs/black_books/61_spectral‑weighted_decomposition.md`
- Source date: `2026-04-14T11:17:25+00:00`

## Topic
Black Book Chapter 61 spectral-weighted decomposition

## Research Questions
- How should CP-003/CP-002 theorem surfaces encode active-vs-kernel, elliptic-vs-hyperbolic, and gauge-vs-shape separation?

## Distilled Claim
Chapter 61 should land as a CP-003/CP-002-aligned surrogate decomposition surface: active-vs-kernel split, range/domain anomaly closure, and gauge-vs-shape bridge encoded through existing canonical owner symbols without introducing new ontology.

## Source Bibliography
- [S1] NOTE: Chapter 61 executive summary and decomposition template

## Claim-to-Source Traceability
Current claims are grounded in [S1].

## Repo Translation Targets
### Owner Files
- `lean/InfoGeometry/Canonical/SingularDecompositionSurrogate.lean`
- `lean/InfoGeometry/Canonical/GlobalChiralDecomposition.lean`
- `lean/InfoGeometry/Canonical/RelativeModularScaleShapeSplit.lean`
- `lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`

### Symbols
- `singular_decomposition_surrogate_package_of_commute`
- `singular_decomposition_surrogate_commutator_of_commute`
- `canonicalRelativeModularOperator_full_block_package_of_wedgeCalibrated`
- `global_active_apex_decomposition`
- `chiral_range_domain_decomposition`
- `singular_polar_surrogate_closure`
- `relativeModular_scaleShapeSplit_bridge_of_commute`

### Target Theorems
- `canonicalRelativeModularOperator_full_block_package_of_wedgeCalibrated`
- `singular_decomposition_surrogate_commutator_of_commute`

## Verification Surface
### Build Targets
- `InfoGeometry.Canonical.SingularDecompositionSurrogate`
- `InfoGeometry.Canonical.GlobalChiralDecomposition`
- `InfoGeometry.Canonical.RelativeModularScaleShapeSplit`

### Audit Targets
- `targeted-module-build-only`
- `no-full-chain-by-default`

## Reviewer Briefing Notes
- Confirm source quality and recency.
- Mark inferred statements explicitly before promotion to `translated`.
- Block canonical edits until owner/symbol mapping is concrete.
