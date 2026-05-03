# Literature Digest: Observer defect to modular source bridge

> Status: `historical handover`
> Audited: 2026-05-02
> Note: Workflow history and packet memory, not current repository authority.
> See: [README.md](../../../README.md), [docs/README.md](../../../docs/README.md), [docs/CODEBASE_STATUS.md](../../../docs/CODEBASE_STATUS.md)

## Packet Metadata
- Packet ID: `EXT-20260414-MODULAR-SOURCE-BRIDGE`
- Lane: `distilled`
- Status: `distilled`
- Coverage: `design_bridge_seeded`
- Generated: `2026-04-14T13:12:31+00:00`

## Provenance
- Source type: `web`
- Source ref: `chapter63+bridge`
- Source date: `2026-04-14T13:12:05+00:00`

## Topic
Observer defect residual as source-term candidate for modular dynamics

## Research Questions
- How to formalize sourced modular generator without overclaiming thermodynamics?
- Which bridge axioms preserve Drazin spectral cut under defect loading?
- What theorem ladder cleanly separates defect memory from modular-time transport?

## Distilled Claim
Defect-first ordering is required in current owner algebra: observer mismatch is first projected as a defect-supported residual; modular-time loading is introduced only through explicit bridge theorems that preserve spectral-cut compatibility.

## Source Bibliography
- [S1] PAPER: https://ems.press/journals/prims/articles/3152 (title: A Note on a Theorem of A. Connes on Radon-Nikodym Cocycles; date: 1984)
- [S2] PAPER: https://doi.org/10.1088/0264-9381/11/12/007 (title: The Thermal Time Hypothesis; date: 1994)
- [S3] PAPER: https://ems.press/journals/prims/articles/2800 (title: Relative Entropy of States of von Neumann Algebras; date: 1976)
- [S4] PAPER: https://www.sciencedirect.com/science/article/pii/S0022123624001083 (title: A short proof of Tomita's theorem; date: 2024)
- [S5] PAPER: https://www.osti.gov/biblio/4075342 (title: Duality condition and Lorentz group (Bisognano–Wichmann II); date: 1976)
- [S6] PAPER: https://cir.nii.ac.jp/crid/1364233271177587072 (title: On the equilibrium states in quantum statistical mechanics (HHW/KMS); date: 1967)
- [S7] PAPER: https://doi.org/10.1080/00029890.1958.11991949 (title: Pseudo-Inverses in Associative Rings and Semigroups; date: 1958)

## Claim-to-Source Traceability
Current claims are grounded in [S1], [S2], [S3], [S4], [S5], [S6], [S7].

## Repo Translation Targets
### Owner Files
- `lean/InfoGeometry/Canonical/DrazinSupercharge.lean`
- `lean/InfoGeometry/Canonical/SingularDecompositionSurrogate.lean`
- `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean`
- `lean/InfoGeometry/Canonical/RealTomitaCore.lean`

### Symbols
- `InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupported`
- `InfoGeometry.Canonical.SingularDecompositionSurrogate.drazin_singular_closure_packet`
- `InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData`

### Target Theorems
- `observerDefectResidual_isDefectSupported`
- `sourcedModularGenerator_respects_spectral_cut`
- `sourcedModularGenerator_bulk_invariant`
- `sourcedModularGenerator_boundary_excitation`

## Verification Surface
### Build Targets
- `InfoGeometry.Canonical.SingularDecompositionSurrogate`

### Audit Targets
- `reports/injections/slo_metrics.md`

## Reviewer Briefing Notes
- Confirm source quality and recency.
- Mark inferred statements explicitly before promotion to `translated`.
- Block canonical edits until owner/symbol mapping is concrete.
