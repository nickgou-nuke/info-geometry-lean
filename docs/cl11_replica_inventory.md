# Split `Cl(1,1)` Replica Inventory

This note records the current exhaustive search allocation for the local split
`Cl(1,1)` packet across the repository.

It is narrower than a general keyword dump and stricter than a thematic survey.
Its purpose is to answer a practical refactor question:

**which files are actually parallel implementations or bridge surfaces for the
same packet, and which files merely consume the same vocabulary?**

Use this note together with:

- [BILINGUAL_SPINE_POLICY.md](BILINGUAL_SPINE_POLICY.md)
- [cl11_content_collision_map.md](cl11_content_collision_map.md)
- [cl11_rosetta_refactor_plan.md](cl11_rosetta_refactor_plan.md)

## Search Scope

The search was performed across full file content in:

- `lean/InfoGeometry/`
- `docs/`
- `scripts/quality/quarantine_manifest.txt`

using exact names plus synonymous terms for:

- `J`, `modular_j`, `modularConjugationJ`, `paritySupercharge`
- `ε`, `eps`, `spectral_epsilon`, `modularSignEpsilon`, `grading`, `chiral`
- `K`, `complex_i`, `modularComplexI`, `dilationOperator`, `cptSupercharge`
- `u_-`, `u_+`, `nullMinus`, `nullPlus`, `creation`, `annihilation`, `ladder`
- `P_-`, `P_+`, `projector`, `polarization`, `sector`
- `phaseFlip`, `equivariance`
- `BdG`, `DIII`, `particleHole`, `timeReversal`, `Kramers`
- `centralCharge`, `analyticalIndex`, `quasilatticeAnalyticalIndex`

## Allocation Rules

Files are assigned to one of these buckets:

- **Owner**: defines a natural presentation-level packet
- **Translator**: moves the packet into an adjacent lane
- **Coherence**: proves two live presentations coincide
- **Alternative**: intentional second implementation under policy
- **Raw duplicate**: unfinished or quarantined competing surface
- **Consumer / semantic neighbor**: uses the packet but does not own it

## High-Confidence Packet Surfaces

### Abstract owners

- `lean/InfoGeometry/Clifford/SplitQ11PhaseFlip.lean`
- `lean/InfoGeometry/Clifford/SplitQ11Projectors.lean`
- `lean/InfoGeometry/Clifford/SplitQ11Equivariance.lean`

Allocation:

- owner
- owner
- translator/coherence

### Doubled/Krein realization

- `lean/InfoGeometry/Krein/DoubledSpace.lean`
- `lean/InfoGeometry/Krein/Representation.lean`
- `lean/InfoGeometry/Quantum/RealSplitClifford.lean`

Allocation:

- owner
- translator/representation owner
- coherence/realization bridge

### Tensor/Bott recursive lane

- `lean/InfoGeometry/Canonical/BottPeriodicity.lean`
- `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean`
- `lean/InfoGeometry/Canonical/SplitCliffordHeadLift.lean`
- `lean/InfoGeometry/Canonical/SplitCliffordHeadPolarization.lean`
- `lean/InfoGeometry/Canonical/SplitCliffordHeadProjectors.lean`
- `lean/InfoGeometry/Canonical/SplitCliffordHeadPhaseFlip.lean`
- `lean/InfoGeometry/Canonical/SplitCliffordHeadEquivariance.lean`

Allocation:

- translator
- coherence/translator
- owner
- owner
- thin renaming surface
- translator
- coherence

### Projective lane

- `lean/InfoGeometry/Convex/ProjectiveRays.lean`
- `lean/InfoGeometry/Krein/State.lean`
- `lean/InfoGeometry/Projective/Dynamics.lean`
- `lean/InfoGeometry/Canonical/ProjectiveSplitQ11Realization.lean`
- `lean/InfoGeometry/Canonical/ProjectiveSectorDecomposition.lean`

Allocation:

- owner
- owner
- translator
- coherence, quarantined
- coherence, quarantined

### Operatorial supercharge/Fock lane

- `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean`
- `lean/InfoGeometry/Canonical/SuperchargeCARCCRBridge.lean`
- `lean/InfoGeometry/Canonical/SuperchargeRoleBridge.lean`
- `lean/InfoGeometry/Canonical/SuperchargeGapHessianBridge.lean`
- `lean/InfoGeometry/Canonical/ProjectorEquivariance.lean`
- `lean/InfoGeometry/Canonical/OperatorialCentralCharge.lean`
- `lean/InfoGeometry/Canonical/SuperchargeCentralChargeClosure.lean`
- `lean/InfoGeometry/Canonical/SuperchargeRoleMapAlt.lean`

Allocation:

- owner
- owner/coherence
- coherence
- closure owner
- coherence
- owner
- closure/coherence
- alternative, quarantined

### BdG / DIII lane

- `lean/InfoGeometry/Canonical/RealBdG.lean`
- `lean/InfoGeometry/Canonical/RealBdGSheetBridge.lean`
- `lean/InfoGeometry/Physics/DIIISymmetryAtom.lean`
- `lean/InfoGeometry/Canonical/RealBdGDIIIAtom.lean`

Allocation:

- owner
- translator
- raw duplicate, quarantined
- raw duplicate under stabilization, quarantined

## High-Value Semantic Neighbors

These are not first-line duplicates, but they are close enough that any refactor
should inspect them before moving names or deleting wrappers:

- `lean/InfoGeometry/Canonical/SplitCliffordHeadSuperBracket.lean`
- `lean/InfoGeometry/Canonical/TopologicalInvariantInvariance.lean`
- `lean/InfoGeometry/Canonical/DilatedGapEquivariance.lean`
- `lean/InfoGeometry/Canonical/BoundaryProjector.lean`
- `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean`
- `lean/InfoGeometry/KK/DiracFredholmIndex.lean`
- `lean/InfoGeometry/KK/QuasilatticeIndexInvariance.lean`
- `lean/InfoGeometry/Canonical/CentralChargeAnomaly.lean`
- `lean/InfoGeometry/Canonical/KreinDoubledAtom.lean`
- `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`

These are usually consumers, upstream carriers, or closure neighbors rather than
competing owners.

## Broad Semantic Cloud

The exhaustive synonym search also hits a wider cloud of files using the same
motifs:

- Majorana / Kitaev / spinor bridges
- conformal/projector/Drazin surfaces
- anomaly/equivariance files
- modular/twistor/phase-space bridges
- docs and black-book notes

These files should not be treated as duplicates automatically.
They are searched to prevent omission, not to justify flattening.

## Current Risk Points

The search surfaced these live refactor risks:

1. `RealBdGDIIIAtom.lean` is an unfinished duplicate and must stay out of the
   authoritative umbrella until it compiles.
2. `SuperchargeRoleMapAlt.lean` is a lawful alternative and must not be removed
   before all consumers route through the canonical bridge.
3. `ProjectiveSplitQ11Realization.lean` and `ProjectiveSectorDecomposition.lean`
   are real coherence files, not decorative wrappers; they should be stabilized
   before any projective deduplication.
4. `CentralChargeAnomaly.lean` uses overlapping vocabulary but is not yet the
   canonical owner of the central-charge lane.

## Refactor Use

When touching this packet:

1. read the owner lane first
2. read the alternative and coherence lane second
3. inspect the high-value semantic neighbors
4. migrate consumers through bridges
5. only then demote or remove anything

Short rule:

**search broadly, classify narrowly, refactor conservatively.**
