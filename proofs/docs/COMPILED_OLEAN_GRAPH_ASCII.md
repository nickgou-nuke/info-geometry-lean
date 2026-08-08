# Compiled `.olean` Theory Graph — ASCII Layout

Source: `proofs/proof_graph.json`, regenerated after successful `lake build`.

```text
Build:      lake build
Extractor:  lake env lean tools/ExtractGraph.lean
Graph:      13110 declarations
Capstone:   FiniteSpinePublicationCertificate.finite_spine_publication_certificate
```

This is the compiled Lean environment dependency graph, not a file-tree import sketch.
Arrows mean: **compiled declaration uses compiled declarations from the target module**.

## Top compiled capstone

```text
┌──────────────────────────────────────────────────────────────────────────────┐
│ FiniteSpinePublicationCertificate.olean                                      │
│                                                                              │
│ theorem finite_spine_publication_certificate                                 │
│ deps: 113 declaration deps                                                    │
│ transitive closure: 415 declarations / 30 local modules                       │
└───────────────────────────────┬──────────────────────────────────────────────┘
                                │
             ┌──────────────────┴──────────────────┐
             │                                     │
             ▼                                     ▼
┌──────────────────────────────────────┐ ┌──────────────────────────────────────┐
│ ThermodynamicNetworkSpine.olean      │ │ ColorParafermionCuntzBusSpine.olean │
│ theorem closed_thermodynamic_...     │ │ theorem closed_color_...            │
│ direct deps: 44 declarations         │ │ direct deps: 78 declarations        │
│ transitive: 100 decls / 10 modules   │ │ transitive: 314 decls / 19 modules │
└───────────────────┬──────────────────┘ └───────────────────┬──────────────────┘
                    │                                        │
                    │                                        │
                    ▼                                        ▼
          THERMAL / DIRAC / K-THEORY                 COLOR / SU(3) / CUNTZ
```

## Thermodynamic spine `.olean` subgraph

```text
ThermodynamicNetworkSpine.olean
│
├── ThermodynamicLorentzBoost.olean
│   ├── ThermalBoostLorentzSuperalgebra.olean
│   │   └── zero-rapidity Lorentz/q bookkeeping
│   ├── CuntzP6MWallpaperBoundary.olean
│   ├── KTheoryChernConfinementSignature.olean
│   ├── NonAbelianBrillouinKleinBottle.olean
│   └── DiracCuntzCrystalDispersion.olean
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
└── TopologicalAndreevPump.olean
    └── ParafermionLane carrier used by BKB lane transition
```

Condensed module arrows:

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

## Color / parafermion / Cuntz bus `.olean` subgraph

```text
ColorParafermionCuntzBusSpine.olean
│
├── GellMannParafermionRealizationRoutesSynthesis.olean
│   ├── route1_identity_spinor
│   ├── route2_universal_lift
│   ├── route3_cantor_cuntz_relations
│   ├── weyl_transport_on_route
│   └── gellmann_parafermion_realization_routes_synthesis
│
├── BogoliubovSU3ParafermionWeld.olean
│   ├── frame_affine_parameter
│   ├── frame_affine_gl1_gl2
│   ├── frame_affine_gl1_gl3
│   ├── frame_affine_gl3_gl8_commutes
│   ├── bdgParafermionPlus4_sq
│   └── bogoliubov_su3_parafermion_synthesis
│
├── BogoliubovSU3ParafermionProofChain.olean
│   ├── colorLieAction4
│   ├── colorLieAction4_commutator
│   ├── qBraid4
│   ├── frameBraid4_mu_shift
│   ├── bdgMajoranaPlusColorSpinor4
│   ├── su3_color_action_all_commutators
│   ├── bogoliubov_su3_parafermion_proof_chain
│   └── theoremBackedColorParafermionBraidingSocket
│
├── GellMannSU3.olean
│   ├── gl1 ... gl8
│   ├── gl1_comm_gl2
│   ├── gl1_comm_gl3
│   ├── gl2_comm_gl3
│   └── Cartan/root commutator table
│
├── SupergradedCuntzBdG.olean
│   ├── Z2Parity
│   ├── superBracket
│   ├── affineSuperBracket
│   ├── qRapidity
│   ├── unruhTemperature
│   └── hamiltonianAtom / BdG generators
│
├── AlgebraicCuntzQuotient.olean
│   ├── CuntzLetter
│   ├── CuntzAlg
│   ├── S / T generators
│   ├── T_mul_S
│   └── partition_one
│
├── CantorBoundaryCuntzFamily.olean
│   ├── C4Boundary
│   ├── C4Functions
│   ├── cuntzS / cuntzT
│   └── c4CuntzFamily / c4Realization
│
├── ParafermionIdentityRealization.olean
│   ├── idRealization
│   ├── CuntzFamilyOn
│   ├── cuntzFamilyLift
│   └── cuntzFamilyRealization
│
├── GellMannParafermionSolder.olean
│   ├── realizedParafermionColorSpinor4
│   ├── gellMannParafermionSolder
│   └── frameSolderedBraid
│
├── WeylSU3ColorSymmetry.olean
│   ├── swap12
│   ├── swap23
│   └── weylAct
│
├── CuntzBoundarySolderRealization.olean
├── WeylSolderedParafermionSymmetry.olean
├── BogoliubovWeylChemicalPotential.olean
├── ColorCARStandardModel.olean
└── ChiralCausalCone.olean
```

Condensed module arrows:

```text
ColorParafermionCuntzBusSpine
├─> GellMannParafermionRealizationRoutesSynthesis
│   ├─> CuntzBoundarySolderRealization
│   ├─> WeylSolderedParafermionSymmetry
│   ├─> BogoliubovSU3ParafermionWeld
│   ├─> BogoliubovSU3ParafermionProofChain
│   └─> CantorBoundaryCuntzFamily
│
├─> BogoliubovSU3ParafermionWeld
│   ├─> BogoliubovWeylChemicalPotential
│   ├─> GellMannSU3
│   ├─> ColorCARStandardModel
│   └─> SupergradedCuntzBdG
│
├─> BogoliubovSU3ParafermionProofChain
│   ├─> BogoliubovSU3ParafermionWeld
│   ├─> GellMannSU3
│   ├─> SupergradedCuntzBdG
│   └─> AlgebraicCuntzQuotient
│
├─> GellMannSU3
├─> SupergradedCuntzBdG
├─> AlgebraicCuntzQuotient
├─> CantorBoundaryCuntzFamily
├─> ParafermionIdentityRealization
├─> GellMannParafermionSolder
├─> WeylSU3ColorSymmetry
└─> ColorCARStandardModel
```

## Full capstone transitive module set

The compiled capstone reaches these local modules transitively:

```text
FiniteSpinePublicationCertificate
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

## Layered view

```text
L0  compiled certificate
    └── FiniteSpinePublicationCertificate

L1  graph-repair spines
    ├── ThermodynamicNetworkSpine
    └── ColorParafermionCuntzBusSpine

L2  synthesis/capstone kernels
    ├── ThermodynamicLorentzBoost
    ├── GellMannParafermionRealizationRoutesSynthesis
    ├── BogoliubovSU3ParafermionWeld
    └── BogoliubovSU3ParafermionProofChain

L3  finite algebraic kernels
    ├── AlgebraicCuntzQuotient
    ├── SupergradedCuntzBdG
    ├── GellMannSU3
    ├── CantorBoundaryCuntzFamily
    ├── ParafermionIdentityRealization
    ├── GellMannParafermionSolder
    ├── WeylSU3ColorSymmetry
    ├── ThermalBoostLorentzSuperalgebra
    ├── DiracCuntzCrystalDispersion
    ├── KTheoryChernConfinementSignature
    └── NonAbelianBrillouinKleinBottle

L4  support / older conductor kernels
    ├── ChiralCausalCone
    ├── ChiralTensorRecoupling
    ├── ChiralTLDescent
    ├── BraidIdealDescent
    ├── ColorCARStandardModel
    ├── BuresInformationGeodesicFlow
    ├── CuntzP6MWallpaperBoundary
    └── TopologicalAndreevPump
```

## Honesty boundary in the compiled graph

```text
COMPILED `.olean` THEOREMS
  finite algebraic/combinatorial/bookkeeping facts only
  ├── exact Cuntz quotient identities
  ├── exact SU(3) matrix commutators
  ├── exact BdG/Majorana lane equalities
  ├── zero-rapidity Lorentz/q identities
  ├── finite K/Chern parity bookkeeping
  └── explicit owner-debt hypotheses for analytic claims

NOT COMPILED AS THEOREMS
  analytic/physical/geometric realizations
  ├── KMS homotopy
  ├── crossed-product C*-K-theory
  ├── Berry/Pfaffian topology
  ├── continuum Dirac/BKB physics
  └── numerical/symbolic Python witness audits
```
