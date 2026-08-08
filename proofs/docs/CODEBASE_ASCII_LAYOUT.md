# Codebase ASCII Layout

```text
/home/goutev/auto
├── README.md / thesis.tex / chapters/
│   └── manuscript + narrative synthesis layer
│
├── docs/
│   ├── CODEBASE_ASCII_LAYOUT.md                 ← this map
│   ├── ARANGO_LEAN_MODULE_GRAPH_AQL.md
│   ├── REPOSITORY_THEOREM_GRAPH.md
│   └── release / architecture / audit notes
│
├── proofs/
│   ├── lakefile.toml                            ← Lean roots
│   ├── proof_graph.json                         ← extracted Lean env graph
│   ├── tools/
│   │   ├── ExtractGraph.lean                    ← env dependency extractor
│   │   └── lean_graph/
│   │       ├── DumpLeanGraph.lean               ← syntax dump
│   │       ├── join_syntax_env.py               ← syntax/env bridge
│   │       ├── import_arango.py                 ← Arango graph import
│   │       ├── aql_query.py                     ← AQL runner
│   │       └── out/                             ← AQL reports / graph audits
│   │
│   ├── FINITE PUBLICATION CAPSTONE
│   │   └── FiniteSpinePublicationCertificate.lean
│   │       ├── uses ThermodynamicNetworkSpine.closed_thermodynamic_network_spine
│   │       └── uses ColorParafermionCuntzBusSpine.closed_color_parafermion_cuntz_bus_spine
│   │
│   ├── THERMODYNAMIC / DIRAC / K-THEORY / BKB SPINE
│   │   ├── ThermodynamicNetworkSpine.lean
│   │   │   ├── ThermodynamicLorentzBoost.lean
│   │   │   ├── ThermodynamicTKKBridge.lean
│   │   │   ├── ThermalBoostLorentzSuperalgebra.lean
│   │   │   ├── DiracCuntzCrystalDispersion.lean
│   │   │   ├── KTheoryChernConfinementSignature.lean
│   │   │   └── NonAbelianBrillouinKleinBottle.lean
│   │   │
│   │   ├── analytic debts remain sockets:
│   │   │   KMS / crossed-product K-theory / Berry-Pfaffian / physical realization
│   │   │
│   │   └── external audit witness:
│   │       └── dirac_cuntz_crystal_dispersion.py
│   │           └── Jackson q-derivative audit; linear cone is q-trivial
│   │
│   ├── COLOR / PARAFERMION / CUNTZ BUS SPINE
│   │   ├── ColorParafermionCuntzBusSpine.lean
│   │   │   ├── GellMannParafermionRealizationRoutesSynthesis.lean
│   │   │   ├── BogoliubovSU3ParafermionWeld.lean
│   │   │   ├── BogoliubovSU3ParafermionProofChain.lean
│   │   │   ├── GellMannSU3.lean
│   │   │   ├── SupergradedCuntzBdG.lean
│   │   │   └── AlgebraicCuntzQuotient.lean
│   │   │
│   │   ├── route / realization layers
│   │   │   ├── GellMannParafermionSolder.lean
│   │   │   ├── ParafermionIdentityRealization.lean
│   │   │   ├── CantorBoundaryCuntzFamily.lean
│   │   │   ├── CuntzBoundarySolderRealization.lean
│   │   │   └── WeylSolderedParafermionSymmetry.lean
│   │   │
│   │   └── finite algebra only:
│   │       SU(3) commutators / Cuntz quotient / BdG lanes / q-clock bookkeeping
│   │
│   ├── O(5,5) / KLEIN / WALLPAPER / VACUUM CHAIN
│   │   ├── O55GradedGeneratorBasis.lean
│   │   ├── O55CartanPhononReduction.lean
│   │   ├── WallpaperO55FrozenSelectionBridge.lean
│   │   ├── TorusKleinO55Bridge.lean
│   │   ├── TwistedTorusVacuumMachine.lean
│   │   └── KasparovKreinKleinO55Kernel.lean
│   │
│   ├── EDGE / SCATTERING / PUMP / GEOMETRY CHAIN
│   │   ├── JackiwRebbiCantorEdgeStates.lean
│   │   ├── StimulatedScatteringAmplituhedron.lean
│   │   ├── TopologicalAndreevPump.lean
│   │   ├── BuresFisherAndreevGeodesicFlow.lean
│   │   └── PhaseConjugateVacuumMirror.lean
│   │
│   ├── METAMATERIAL / COSMOLOGY / SURFACE CHAIN
│   │   ├── MetamaterialQuasicrystalBloch.lean
│   │   ├── ConformalScaleRecurrence.lean
│   │   ├── CosmologicalSynthesis.lean
│   │   ├── SuperconductingHolographicResonator.lean
│   │   ├── TopologicalMetasurfaceSupercurrent.lean
│   │   └── CuntzP6MWallpaperBoundary.lean
│   │
│   ├── CHIRAL / BRAID / TKK / DE RHAM INFRASTRUCTURE
│   │   ├── ChiralCausalCone.lean
│   │   ├── ChiralTensorRecoupling.lean
│   │   ├── ChiralTLDescent.lean
│   │   ├── B3PresentedGroup.lean
│   │   ├── JonesBraidB3.lean
│   │   ├── TKKJordanPairSocket.lean
│   │   ├── ChemicalPotentialDeRhamG0Bridge.lean
│   │   ├── ModularRadonNikodymJacobianBridge.lean
│   │   └── NonIsoConf3DeRhamCooperad.lean
│   │
│   ├── PYTHON WITNESS / AUDIT SCRIPTS
│   │   ├── *_audit.py / *_witness.py / *_synthesis.py
│   │   └── external computations only, not Lean proof kernels
│   │
│   └── .lake/                                  ← Lean build artifacts / mathlib
│
├── external/
│   ├── repos/
│   │   ├── QuatIca/
│   │   ├── trainsum/
│   │   ├── all-you-need-is-spin/
│   │   └── Equivariant-Manifold-Flows/
│   └── papers/
│       └── literature digests / source papers
│
├── papers/
│   └── focused paper drafts + lemma chains
│
├── memory/
│   └── dated working notes
│
└── configs/local/                              ← local config; do not publish secrets
```

## Main proof-graph spine

```text
                         ┌─────────────────────────────────────────────┐
                         │ FiniteSpinePublicationCertificate           │
                         │ finite_spine_publication_certificate        │
                         └───────────────────┬─────────────────────────┘
                                             │
              ┌──────────────────────────────┴──────────────────────────────┐
              │                                                             │
              ▼                                                             ▼
┌─────────────────────────────────────────────┐        ┌─────────────────────────────────────────────┐
│ ThermodynamicNetworkSpine                   │        │ ColorParafermionCuntzBusSpine               │
│ closed_thermodynamic_network_spine          │        │ closed_color_parafermion_cuntz_bus_spine    │
└───────────────┬─────────────────────────────┘        └───────────────┬─────────────────────────────┘
                │                                                      │
     ┌──────────┼──────────┬──────────┬──────────┐          ┌──────────┼──────────┬──────────┬──────────┐
     ▼          ▼          ▼          ▼          ▼          ▼          ▼          ▼          ▼          ▼
 Thermo     TKK/grade   thermal     Dirac      K/BKB     routes      weld      proof     SU(3)      Cuntz
 Lorentz    parity      boost/q     Cuntz      finite    capstone    socket    chain     matrices   quotient
 boost                  zero facts  crystal    facts
```

## Theorem-honest boundary

```text
FINITE LEAN KERNELS
  prove algebraic / combinatorial / bookkeeping facts
  ├── Cuntz quotient relations
  ├── SU(3) matrix commutators
  ├── BdG/Majorana lane identities
  ├── zero-rapidity Lorentz/q facts
  ├── finite K-theory/Chern parity bookkeeping
  └── graph repair spines / certificates

SOCKET / WITNESS LAYERS
  record or audit claims not proved in Lean
  ├── analytic KMS and crossed-product K-theory
  ├── continuum Berry/Pfaffian topology
  ├── physical Dirac/BKB/metamaterial realizations
  ├── numerical or symbolic Python checks
  └── external repos as witnesses, not proof kernels
```
