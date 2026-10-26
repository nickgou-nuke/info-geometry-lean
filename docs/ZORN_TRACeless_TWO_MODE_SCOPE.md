# Zorn two-mode flow and Porter square completion — source contract

The 2026-10-25 pasted note proposes (i) a generic Zorn traceless Cayley–Hamilton polynomial flow, (ii) 7D Clifford polarization and Nambu three-cocycles, (iii) Porter Riccati completion, and (iv) a five-mode Cl(5,5) charge table.

## Owner search

The inspected current owners are:
- `lean/InfoGeometry/Algebra/ZornAlternativeLaws.lean`, which ALREADY defines `zornTracelessFlowGen`, `zornExpUpperNil`, `zornExpLowerNil`, `zornAssociator`, and `zornNambuDet`. It ALREADY establishes on-shell left/right alternatives and upper/lower Nambu three-cocycles.
- `lean/InfoGeometry/Canonical/AlbertCayleyDickson.lean`, which ALREADY provides Porter composition and Casimir discriminant identities.
- `lean/InfoGeometry/Physics/Cl55SpinorCartanFock.lean`, which ALREADY provides `sixChargeBL`, mode-occupation spectral decompositions and a concrete five-mode Fock owner.

## Correction of conflicting prose

The current Zorn owner proves `M(α,v,w)^2 = (α² + dot v w) • 1` (not `α² - dot v w`). Accordingly the new *polynomial multiplication* uses `κ = α² + dot v w`. Existing upper/lower Nambu associator equations have a **negative** determinant coefficient in the owner's convention; the pasted positive-sign statements must not be copied unaltered. The source's `norm` is its own quadratic definition, and no claim equating it with `c²-s²κ` is made here.

## New contributions

1. `Algebra/ZornTracelessTwoModeFlow.lean`: constructs `E(c,s)=c•1+s•M` on the existing Zorn carrier; proves its coordinate formula, the two-mode Cayley–Hamilton multiplication and a formal opposite-mode product.
2. `Canonical/PorterRiccatiSquareCompletion.lean`: derives square completion from the existing Porter Riccati evaluation owner theorem.

## Semantic boundary

These are finite ring identities, not an analytic exponential, Lie-group representation, physical Klein–Gordon equation, SU(2)/Pin group classification, or a g2 derivation representation. The existing Zorn alternatives prove a common-generator associator property relevant to operator actions; proving an action with inverses additionally requires the correct unit-norm carrier and its admissible parameter group.

The Cartan state-number table is already an owner concern. No duplicate `CartanSigns` coordinate surrogate is introduced.

## Verification

This is a GitHub API candidate only. The repository's Lean 4.34.1 toolchain and Lake build are **not installed in this execution environment**. The new source has **not been kernel checked** and cannot be labelled `sorry-free verified` merely from its text. A narrow locked build, axiom scan, semantic/vacuity audit, and broad pre-push verification are required before promotion. Pins, previous owners, and main were not modified.
