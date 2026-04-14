# Literature Digest: Observer residual: defect-first then modular

## Packet Metadata
- Packet ID: `EXT-20260414-OBSERVER-DEFECT-FIRST`
- Lane: `distilled`
- Status: `distilled`
- Coverage: `seeded_with_literature`
- Generated: `2026-04-14T13:03:32+00:00`

## Provenance
- Source type: `web`
- Source ref: `blackbook61+literature`
- Source date: `2026-04-14T12:59:52+00:00`

## Topic
Observer orientation residuals: defect-first dissipation before modular-time loading

## Research Questions
- Is [O,G] best interpreted first as defect-supported residual?
- What owner-safe bridge is required from defect residual to modular generator?
- Which theorem family should formalize ObserverL5 without scalar entropy overreach?

## Distilled Claim
In the current Spire owner algebra, observer orientation mismatch should be modeled first as an operator-valued residual compressed in the Drazin defect lane (Q0*R*Q0), with modular-time coupling treated as a secondary bridge theorem.

## Source Bibliography
- [S1] PAPER: https://www.sciencedirect.com/science/article/pii/S0022123624001083 (title: A short proof of Tomita's theorem; date: 2024)
- [S2] PAPER: https://ems.press/journals/prims/articles/2800 (title: Relative Entropy of States of von Neumann Algebras; date: 1976)
- [S3] PAPER: https://www.osti.gov/biblio/4075342 (title: Duality condition and Lorentz group (Bisognano–Wichmann II); date: 1976)
- [S4] PAPER: https://www.osti.gov/biblio/4199488 (title: Duality condition for a Hermitian scalar field (Bisognano–Wichmann I); date: 1975)
- [S5] PAPER: https://cir.nii.ac.jp/crid/1364233271177587072 (title: On the equilibrium states in quantum statistical mechanics (HHW/KMS); date: 1967)
- [S6] PAPER: https://doi.org/10.1088/0264-9381/11/12/007 (title: The Thermal Time Hypothesis; date: 1994)
- [S7] PAPER: https://doi.org/10.1080/00029890.1958.11991949 (title: Pseudo-Inverses in Associative Rings and Semigroups; date: 1958)

## Claim-to-Source Traceability
Current claims are grounded in [S1], [S2], [S3], [S4], [S5], [S6], [S7].

## Repo Translation Targets
### Owner Files
- `lean/InfoGeometry/Canonical/DrazinSupercharge.lean`
- `lean/InfoGeometry/Canonical/SingularDecompositionSurrogate.lean`
- `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean`

### Symbols
- `InfoGeometry.Canonical.SingularDecompositionSurrogate.drazin_singular_closure_packet`
- `InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupported`
- `InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.exists_superHamiltonian_canonical_split`

### Target Theorems
- `observerDefectResidual_isDefectSupported`
- `observerDefectResidual_vanishes_when_slice_commutes_with_dilationGap`
- `observerDefectResidual_to_modular_source_bridge`

## Verification Surface
### Build Targets
- `InfoGeometry.Canonical.SingularDecompositionSurrogate`

### Audit Targets
- `reports/injections/slo_metrics.md`

## Reviewer Briefing Notes
- Confirm source quality and recency.
- Mark inferred statements explicitly before promotion to `translated`.
- Block canonical edits until owner/symbol mapping is concrete.
