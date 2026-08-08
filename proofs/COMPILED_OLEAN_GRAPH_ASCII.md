# `~/auto` Compiled `.olean` Graph Layout

Scope: **only `/home/goutev/auto`**, centered on the compiled Lean theory in `~/auto/proofs`.

Source graph:

```text
~/auto/proofs/proof_graph.json
13110 compiled declarations
```

Main compiled capstone:

```lean
FiniteSpinePublicationCertificate.finite_spine_publication_certificate
```

## Top-level compiled graph

```text
~/auto
└── proofs/
    └── .lake/build/lib/lean/*.olean
        │
        ▼
┌─────────────────────────────────────────────────────────────────────┐
│ FiniteSpinePublicationCertificate.olean                             │
│                                                                     │
│ theorem finite_spine_publication_certificate                        │
│ deps: 113 compiled declarations                                     │
│ transitive closure: 415 declarations / 30 local modules             │
└──────────────────────────────┬──────────────────────────────────────┘
                               │
              ┌────────────────┴────────────────┐
              │                                 │
              ▼                                 ▼
┌────────────────────────────────────┐ ┌────────────────────────────────────┐
│ ThermodynamicNetworkSpine.olean    │ │ ColorParafermionCuntzBusSpine.olean│
│ closed_thermodynamic_network_spine │ │ closed_color_parafermion_...       │
│ deps: 44 decls                     │ │ deps: 78 decls                     │
│ used_by: 1                         │ │ used_by: 1                         │
└───────────────────┬────────────────┘ └───────────────────┬────────────────┘
                    │                                      │
                    ▼                                      ▼
        THERMAL / DIRAC / K / BKB              COLOR / SU(3) / CUNTZ BUS
```

## Thermodynamic spine inside `~/auto/proofs`

```text
ThermodynamicNetworkSpine.olean
│
├── ThermodynamicLorentzBoost.olean
│   ├── closed_thermodynamic_lorentz_boost_kernel
│   ├── equivariant_lorentz_boost_signature
│   └── K0EquivariantBoost
│
├── ThermodynamicTKKBridge.olean
│   └── formalChiralParityIndex_zero
│
├── ThermalBoostLorentzSuperalgebra.olean
│   ├── lorentzBoost_zero
│   ├── gamma_zero
│   ├── qOfRapidity_zero
│   └── safeDispersionFactor_zero
│
├── DiracCuntzCrystalDispersion.olean
│   ├── masslessDiracCuntzEnergySq_zero_rapidity
│   ├── bandSign conduction = 1
│   └── bandSign valence = -1
│
├── KTheoryChernConfinementSignature.olean
│   ├── cuntzK0Modulus
│   ├── fixedOrbitCountP6M
│   ├── blochFreeRank
│   ├── crossedProductK1Rank
│   ├── jonesIndexD6
│   └── chernParity_zero
│
├── NonAbelianBrillouinKleinBottle.olean
│   ├── bkbFold_involutive
│   ├── bkbLaneTransition_involutive
│   ├── bkbChernNumber
│   └── kleinParityInvariant
│
├── BuresInformationGeodesicFlow.olean
│   └── modularFlow_zero_time
│
├── CuntzP6MWallpaperBoundary.olean
│   └── sectorArity p3 = 3
│
└── TopologicalAndreevPump.olean
    └── ParafermionLane
```

Condensed arrows:

```text
ThermodynamicNetworkSpine
├─> ThermodynamicLorentzBoost
├─> ThermodynamicTKKBridge
├─> ThermalBoostLorentzSuperalgebra
├─> DiracCuntzCrystalDispersion
├─> KTheoryChernConfinementSignature
├─> NonAbelianBrillouinKleinBottle
├─> BuresInformationGeodesicFlow
├─> CuntzP6MWallpaperBoundary
└─> TopologicalAndreevPump
```

## Color / parafermion / Cuntz spine inside `~/auto/proofs`

```text
ColorParafermionCuntzBusSpine.olean
│
├── GellMannParafermionRealizationRoutesSynthesis.olean
│   └── gellmann_parafermion_realization_routes_synthesis
│
├── BogoliubovSU3ParafermionWeld.olean
│   ├── bogoliubov_su3_parafermion_synthesis
│   ├── frame_affine_gl1_gl2
│   └── bdgParafermionPlus4_sq
│
├── BogoliubovSU3ParafermionProofChain.olean
│   ├── bogoliubov_su3_parafermion_proof_chain
│   ├── su3_color_action_all_commutators
│   ├── theoremBackedColorParafermionBraidingSocket
│   ├── colorLieAction4
│   └── qBraid4
│
├── GellMannSU3.olean
│   ├── gl1 ... gl8
│   └── Gell-Mann commutator table
│
├── SupergradedCuntzBdG.olean
│   ├── Z2Parity
│   ├── affineSuperBracket
│   ├── qRapidity
│   └── hamiltonianAtom
│
├── AlgebraicCuntzQuotient.olean
│   ├── CuntzAlg
│   ├── S / T
│   ├── T_mul_S
│   └── partition_one
│
├── CantorBoundaryCuntzFamily.olean
│   ├── c4CuntzFamily
│   └── c4Realization
│
├── ParafermionIdentityRealization.olean
│   ├── idRealization
│   └── cuntzFamilyLift
│
├── GellMannParafermionSolder.olean
│   ├── realizedParafermionColorSpinor4
│   └── gellMannParafermionSolder
│
├── WeylSU3ColorSymmetry.olean
├── CuntzBoundarySolderRealization.olean
├── WeylSolderedParafermionSymmetry.olean
├── BogoliubovWeylChemicalPotential.olean
├── ColorCARStandardModel.olean
└── ChiralCausalCone.olean
```

Condensed arrows:

```text
ColorParafermionCuntzBusSpine
├─> GellMannParafermionRealizationRoutesSynthesis
├─> BogoliubovSU3ParafermionWeld
├─> BogoliubovSU3ParafermionProofChain
├─> GellMannSU3
├─> SupergradedCuntzBdG
├─> AlgebraicCuntzQuotient
├─> CantorBoundaryCuntzFamily
├─> ParafermionIdentityRealization
├─> GellMannParafermionSolder
├─> WeylSU3ColorSymmetry
├─> CuntzBoundarySolderRealization
├─> WeylSolderedParafermionSymmetry
├─> BogoliubovWeylChemicalPotential
├─> ColorCARStandardModel
└─> ChiralCausalCone
```

## Whole `~/auto` compiled proof spine

```text
FiniteSpinePublicationCertificate
│
├── ThermodynamicNetworkSpine
│   ├── ThermodynamicLorentzBoost
│   ├── ThermodynamicTKKBridge
│   ├── ThermalBoostLorentzSuperalgebra
│   ├── DiracCuntzCrystalDispersion
│   ├── KTheoryChernConfinementSignature
│   ├── NonAbelianBrillouinKleinBottle
│   ├── BuresInformationGeodesicFlow
│   ├── CuntzP6MWallpaperBoundary
│   └── TopologicalAndreevPump
│
└── ColorParafermionCuntzBusSpine
    ├── GellMannParafermionRealizationRoutesSynthesis
    ├── BogoliubovSU3ParafermionWeld
    ├── BogoliubovSU3ParafermionProofChain
    ├── BogoliubovWeylChemicalPotential
    ├── GellMannSU3
    ├── SupergradedCuntzBdG
    ├── AlgebraicCuntzQuotient
    ├── CantorBoundaryCuntzFamily
    ├── ParafermionIdentityRealization
    ├── GellMannParafermionSolder
    ├── CuntzBoundarySolderRealization
    ├── WeylSolderedParafermionSymmetry
    ├── WeylSU3ColorSymmetry
    ├── ColorCARStandardModel
    ├── ChiralCausalCone
    ├── ChiralTensorRecoupling
    ├── ChiralTLDescent
    └── BraidIdealDescent
```

## Compiled layer stack

```text
L0  Final compiled certificate
    └── FiniteSpinePublicationCertificate.olean

L1  Repair spines
    ├── ThermodynamicNetworkSpine.olean
    └── ColorParafermionCuntzBusSpine.olean

L2  Synthesis kernels
    ├── ThermodynamicLorentzBoost.olean
    ├── GellMannParafermionRealizationRoutesSynthesis.olean
    ├── BogoliubovSU3ParafermionWeld.olean
    └── BogoliubovSU3ParafermionProofChain.olean

L3  Finite algebra kernels
    ├── AlgebraicCuntzQuotient.olean
    ├── SupergradedCuntzBdG.olean
    ├── GellMannSU3.olean
    ├── CantorBoundaryCuntzFamily.olean
    ├── DiracCuntzCrystalDispersion.olean
    ├── KTheoryChernConfinementSignature.olean
    └── NonAbelianBrillouinKleinBottle.olean

L4  Support conductors
    ├── ChiralCausalCone.olean
    ├── ChiralTensorRecoupling.olean
    ├── ChiralTLDescent.olean
    ├── BraidIdealDescent.olean
    ├── ColorCARStandardModel.olean
    ├── BuresInformationGeodesicFlow.olean
    └── TopologicalAndreevPump.olean
```

## Boundary

```text
COMPILED IN ~/auto/proofs/.lake
  finite Lean kernels:
  algebra, matrices, Cuntz relations, parity, zero-rapidity facts,
  finite K/Chern bookkeeping, graph repair certificates.

NOT COMPILED AS LEAN THEOREMS
  analytic/physical/socket debts:
  KMS, C*-crossed products, continuum Berry/Pfaffian topology,
  physical metamaterial/Dirac/BKB realization, numerical Python audits.
```
