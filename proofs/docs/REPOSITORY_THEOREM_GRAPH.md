# Repository map: what this Lean repository is about
This repository is a theorem-driven noncommutative geometry / mathematical-physics laboratory.  Its Lean files build finite, checkable algebraic kernels for chiral Clifford/CAR atoms, Cuntz/UHF operator boundaries, Weyl/phase-space cells, Bogoliubov/q-clock deformation, finite GNS/Krein/spectral regularization, q-super/root-of-unity truncation sockets, TKK/Jordan sockets, and information-geometric thermodynamic calibration.
The guiding theorem-honesty rule is: finite algebraic statements are proved in Lean; analytic/infinite/C⋆/KMS/Tomita/continuum claims are explicit sockets unless separately formalized.
## Generated graph artifacts
- Full local Lean import graph, Graphviz DOT: [`docs/LEAN_MODULE_GRAPH.dot`](LEAN_MODULE_GRAPH.dot)
- Rendered SVG graph: [`docs/LEAN_MODULE_GRAPH.svg`](LEAN_MODULE_GRAPH.svg)
- Machine-readable graph JSON: [`docs/lean_module_graph.json`](lean_module_graph.json)
Inventory: **457** `.lean` modules, **502** local import edges.
## High-level architecture

```text
Chiral / Clifford / CAR atom
  → Cuntz / UHF / finite operator boundary
  → finite GNS quotient, Krein adjoint, Cayley/DKT regularization
  → q-super parity/supertrace and finite root-of-unity truncation socket
  → Lorentz / Poincaré / Hestenes / TKK-Jordan sockets
  → braid / Yang-Baxter topology and SU(3) color lanes
  → information-geometric Dikin / Amari-Chentsov cubic torsion
  → analytic C⋆/KMS/Tomita/continuum sockets for future completion
```
## Category graph

| From | To | Local imports |
|---|---|---:|
| Core algebra / misc | Core algebra / misc | 42 |
| Tooling / graph extraction | Core algebra / misc | 24 |
| Clifford / chiral / spinors | Clifford / chiral / spinors | 22 |
| Arithmetic / zeta / primons | Arithmetic / zeta / primons | 21 |
| Core algebra / misc | Braids / YBE / topology | 18 |
| Tooling / graph extraction | Clifford / chiral / spinors | 16 |
| Tooling / graph extraction | Braids / YBE / topology | 16 |
| Tooling / graph extraction | Operator algebras / CAR-CCR-Cuntz | 16 |
| Operator algebras / CAR-CCR-Cuntz | Operator algebras / CAR-CCR-Cuntz | 14 |
| Braids / YBE / topology | Braids / YBE / topology | 13 |
| Core algebra / misc | Operator algebras / CAR-CCR-Cuntz | 13 |
| Operator algebras / CAR-CCR-Cuntz | Clifford / chiral / spinors | 12 |
| Geometry / holography / tilings | Geometry / holography / tilings | 11 |
| Core algebra / misc | Arithmetic / zeta / primons | 11 |
| Tooling / graph extraction | Arithmetic / zeta / primons | 11 |
| Geometry / holography / tilings | Core algebra / misc | 11 |
| Core algebra / misc | Geometry / holography / tilings | 10 |
| Core algebra / misc | Spacetime / phase / Bogoliubov | 10 |
| Braids / YBE / topology | Core algebra / misc | 9 |
| Clifford / chiral / spinors | Braids / YBE / topology | 9 |
| Tooling / graph extraction | Spacetime / phase / Bogoliubov | 9 |
| Tooling / graph extraction | Gauge / Standard Model color | 9 |
| Tooling / graph extraction | Geometry / holography / tilings | 9 |
| Gauge / Standard Model color | Gauge / Standard Model color | 8 |
| Braids / YBE / topology | Gauge / Standard Model color | 7 |
| Braids / YBE / topology | Clifford / chiral / spinors | 6 |
| Operator algebras / CAR-CCR-Cuntz | Spacetime / phase / Bogoliubov | 6 |
| Core algebra / misc | Clifford / chiral / spinors | 5 |
| Operator algebras / CAR-CCR-Cuntz | Core algebra / misc | 5 |
| Tooling / graph extraction | Information geometry / thermodynamics | 5 |
| Geometry / holography / tilings | Arithmetic / zeta / primons | 5 |
| Geometry / holography / tilings | Braids / YBE / topology | 5 |
| Spectral / index / anomaly | Spectral / index / anomaly | 4 |
| Gauge / Standard Model color | Clifford / chiral / spinors | 4 |
| Clifford / chiral / spinors | Operator algebras / CAR-CCR-Cuntz | 4 |
| Clifford / chiral / spinors | Gauge / Standard Model color | 4 |
| Gauge / Standard Model color | Operator algebras / CAR-CCR-Cuntz | 4 |
| Braids / YBE / topology | Operator algebras / CAR-CCR-Cuntz | 4 |
| Spacetime / phase / Bogoliubov | Spectral / index / anomaly | 4 |
| Spacetime / phase / Bogoliubov | Spacetime / phase / Bogoliubov | 4 |
| Arithmetic / zeta / primons | Operator algebras / CAR-CCR-Cuntz | 4 |
| Spacetime / phase / Bogoliubov | Operator algebras / CAR-CCR-Cuntz | 3 |
| Operator algebras / CAR-CCR-Cuntz | Arithmetic / zeta / primons | 3 |
| Clifford / chiral / spinors | Core algebra / misc | 3 |
| Braids / YBE / topology | Arithmetic / zeta / primons | 3 |
| Core algebra / misc | Information geometry / thermodynamics | 3 |
| Arithmetic / zeta / primons | Spacetime / phase / Bogoliubov | 3 |
| Geometry / holography / tilings | Clifford / chiral / spinors | 3 |
| Gauge / Standard Model color | Braids / YBE / topology | 3 |
| Spectral / index / anomaly | Arithmetic / zeta / primons | 3 |
| Spacetime / phase / Bogoliubov | Gauge / Standard Model color | 3 |
| Tooling / graph extraction | Tooling / graph extraction | 2 |
| Spacetime / phase / Bogoliubov | Core algebra / misc | 2 |
| Gauge / Standard Model color | Spacetime / phase / Bogoliubov | 2 |
| Geometry / holography / tilings | Operator algebras / CAR-CCR-Cuntz | 2 |
| Clifford / chiral / spinors | Spacetime / phase / Bogoliubov | 2 |
| Operator algebras / CAR-CCR-Cuntz | Spectral / index / anomaly | 2 |
| Information geometry / thermodynamics | Information geometry / thermodynamics | 2 |
| Arithmetic / zeta / primons | Spectral / index / anomaly | 2 |
| Geometry / holography / tilings | Gauge / Standard Model color | 2 |
| Core algebra / misc | Spectral / index / anomaly | 2 |
| Core algebra / misc | Gauge / Standard Model color | 2 |
| Arithmetic / zeta / primons | Core algebra / misc | 2 |
| Gauge / Standard Model color | Arithmetic / zeta / primons | 2 |
| Operator algebras / CAR-CCR-Cuntz | Geometry / holography / tilings | 1 |
| Operator algebras / CAR-CCR-Cuntz | Braids / YBE / topology | 1 |
| Information geometry / thermodynamics | Spacetime / phase / Bogoliubov | 1 |
| Information geometry / thermodynamics | Operator algebras / CAR-CCR-Cuntz | 1 |
| Operator algebras / CAR-CCR-Cuntz | Information geometry / thermodynamics | 1 |
| Information geometry / thermodynamics | Geometry / holography / tilings | 1 |
| Tooling / graph extraction | Spectral / index / anomaly | 1 |
| Braids / YBE / topology | Spacetime / phase / Bogoliubov | 1 |
| Geometry / holography / tilings | Information geometry / thermodynamics | 1 |
| Gauge / Standard Model color | Geometry / holography / tilings | 1 |
| Information geometry / thermodynamics | Arithmetic / zeta / primons | 1 |
| Geometry / holography / tilings | Spectral / index / anomaly | 1 |
| Geometry / holography / tilings | Spacetime / phase / Bogoliubov | 1 |
| Arithmetic / zeta / primons | Braids / YBE / topology | 1 |
| Arithmetic / zeta / primons | Clifford / chiral / spinors | 1 |
| Information geometry / thermodynamics | Core algebra / misc | 1 |

## Most central modules by imports

| Module | Imported by | Path |
|---|---:|---|
| `ChiralCausalCone` | 15 | `proofs/ChiralCausalCone.lean` |
| `CantorBoundaryCuntzFamily` | 11 | `proofs/CantorBoundaryCuntzFamily.lean` |
| `MajoranaPrimonSpectralBridge` | 8 | `proofs/MajoranaPrimonSpectralBridge.lean` |
| `AnomalousKMSFlow` | 7 | `proofs/AnomalousKMSFlow.lean` |
| `PrimonBosonFermionDuality` | 7 | `proofs/PrimonBosonFermionDuality.lean` |
| `JonesBraidB3` | 6 | `proofs/JonesBraidB3.lean` |
| `ChiralTensorRecoupling` | 6 | `proofs/ChiralTensorRecoupling.lean` |
| `TLChain` | 6 | `proofs/TLChain.lean` |
| `YangBaxterQSwap` | 6 | `proofs/YangBaxterQSwap.lean` |
| `BraidIdealDescent` | 6 | `proofs/BraidIdealDescent.lean` |
| `UHFInductiveColimit` | 6 | `proofs/UHFInductiveColimit.lean` |
| `SU3LoopBraidDuality` | 6 | `proofs/SU3LoopBraidDuality.lean` |
| `DeterminantSupergrading` | 6 | `proofs/DeterminantSupergrading.lean` |
| `GellMannParafermionSolder` | 6 | `proofs/GellMannParafermionSolder.lean` |
| `PrimonHilbertPolyaSeparation` | 6 | `proofs/PrimonHilbertPolyaSeparation.lean` |
| `Clifford55AnomalyOSP` | 5 | `proofs/Clifford55AnomalyOSP.lean` |
| `BogoliubovSU3ParafermionProofChain` | 5 | `proofs/BogoliubovSU3ParafermionProofChain.lean` |
| `BogoliubovWeylChemicalPotential` | 5 | `proofs/BogoliubovWeylChemicalPotential.lean` |
| `ProjectiveAffineConformalClosure55` | 5 | `proofs/ProjectiveAffineConformalClosure55.lean` |
| `SupergradedCuntzBdG` | 5 | `proofs/SupergradedCuntzBdG.lean` |
| `ChiralAffineBogoliubovWeld` | 5 | `proofs/ChiralAffineBogoliubovWeld.lean` |
| `HillWheelerUniversalProjection` | 5 | `proofs/HillWheelerUniversalProjection.lean` |
| `InformationGeometricCutoff` | 5 | `proofs/InformationGeometricCutoff.lean` |
| `NonIsoConf3QuadricD4PointCount` | 5 | `proofs/NonIsoConf3QuadricD4PointCount.lean` |
| `WeylSU3ColorSymmetry` | 5 | `proofs/WeylSU3ColorSymmetry.lean` |
| `B3PresentedGroup` | 4 | `proofs/B3PresentedGroup.lean` |
| `GellMannSU3` | 4 | `proofs/GellMannSU3.lean` |
| `TwistorParafermionBoundary` | 4 | `proofs/TwistorParafermionBoundary.lean` |
| `MobiusCantorTKKClosure` | 4 | `proofs/MobiusCantorTKKClosure.lean` |
| `JaynesLDDPGNSColimit` | 4 | `proofs/JaynesLDDPGNSColimit.lean` |
| `ContinuumAsColimitCounting` | 4 | `proofs/ContinuumAsColimitCounting.lean` |
| `PrimonCoarseGraining` | 4 | `proofs/PrimonCoarseGraining.lean` |
| `TrifactorGeometry` | 4 | `proofs/TrifactorGeometry.lean` |
| `BogoliubovBraidGraphWeld` | 4 | `proofs/BogoliubovBraidGraphWeld.lean` |
| `FierzIdentities` | 4 | `proofs/FierzIdentities.lean` |
| `NonIsoConf3OrlikSolomon` | 4 | `proofs/NonIsoConf3OrlikSolomon.lean` |
| `PenroseSpinIncidenceTessellation` | 4 | `proofs/PenroseSpinIncidenceTessellation.lean` |
| `GoutevTonevPrinciple` | 3 | `proofs/GoutevTonevPrinciple.lean` |
| `BraidCliffordIntegration` | 3 | `proofs/BraidCliffordIntegration.lean` |
| `ArtinMonodromyPin55` | 3 | `proofs/ArtinMonodromyPin55.lean` |

## Modules importing the most local modules

| Module | Local imports | Path |
|---|---:|---|
| `ExtractGraph` | 113 | `proofs/tools/ExtractGraph.lean` |
| `InfoGeometry` | 27 | `proofs/InfoGeometry.lean` |
| `BaxterAnchorManifest` | 11 | `proofs/BaxterAnchorManifest.lean` |
| `PenroseSpinTilingCapstone` | 7 | `proofs/PenroseSpinTilingCapstone.lean` |
| `ChiralB3PresentedBridge` | 6 | `proofs/ChiralB3PresentedBridge.lean` |
| `GellMannParafermionRealizationRoutesSynthesis` | 6 | `proofs/GellMannParafermionRealizationRoutesSynthesis.lean` |
| `HolographicDictionarySynthesis` | 6 | `proofs/_deprecated/removed_from_default_2026_06_15/HolographicDictionarySynthesis.lean` |
| `SU3LoopBraidDuality` | 6 | `proofs/SU3LoopBraidDuality.lean` |
| `GravitationalQuantumBraidDuality` | 5 | `proofs/GravitationalQuantumBraidDuality.lean` |
| `HolographicProxyQLimit` | 5 | `proofs/HolographicProxyQLimit.lean` |
| `PrimonFlavorCKM` | 5 | `proofs/PrimonFlavorCKM.lean` |
| `TopologicalColorCrystalFormal` | 5 | `proofs/TopologicalColorCrystalFormal.lean` |
| `UnifiedAnomalyArchitecture` | 5 | `proofs/UnifiedAnomalyArchitecture.lean` |
| `BogoliubovBraidGraphWeld` | 4 | `proofs/BogoliubovBraidGraphWeld.lean` |
| `CartanKleinBottleGeometry` | 4 | `proofs/CartanKleinBottleGeometry.lean` |
| `ChiralTLDescent` | 4 | `proofs/ChiralTLDescent.lean` |
| `ColorCARStandardModel` | 4 | `proofs/ColorCARStandardModel.lean` |
| `CuntzDeformedSuperPoincare` | 4 | `proofs/CuntzDeformedSuperPoincare.lean` |
| `DikinOnsagerCramerRaoOperator` | 4 | `proofs/DikinOnsagerCramerRaoOperator.lean` |
| `ExceptionalPointMonodromy` | 4 | `proofs/ExceptionalPointMonodromy.lean` |
| `HilbertPolyaBivariant` | 4 | `proofs/HilbertPolyaBivariant.lean` |
| `HolographicGaugeSymmetryUniqueness` | 4 | `proofs/HolographicGaugeSymmetryUniqueness.lean` |
| `IdealDescentProof` | 4 | `proofs/IdealDescentProof.lean` |
| `ItFromBitProjectiveHolographicSynthesis` | 4 | `proofs/ItFromBitProjectiveHolographicSynthesis.lean` |
| `KleinBottleKANCoordinates` | 4 | `proofs/KleinBottleKANCoordinates.lean` |
| `KreinCuntzShadow` | 4 | `proofs/KreinCuntzShadow.lean` |
| `LorentzChiralCuntzBridge` | 4 | `proofs/LorentzChiralCuntzBridge.lean` |
| `ModularEntropyPrimes` | 4 | `proofs/ModularEntropyPrimes.lean` |
| `NonIsoConf3ThreePointDeRhamCooperad` | 4 | `proofs/NonIsoConf3ThreePointDeRhamCooperad.lean` |
| `RunExtractor` | 4 | `proofs/RunExtractor.lean` |
| `S3ColorSpinorDecomposition` | 4 | `proofs/S3ColorSpinorDecomposition.lean` |
| `SU3LoopBraidCuntzBoundary` | 4 | `proofs/SU3LoopBraidCuntzBoundary.lean` |
| `SocketDischargeChain` | 4 | `proofs/SocketDischargeChain.lean` |
| `Z2NonAbelianBraiding` | 4 | `proofs/Z2NonAbelianBraiding.lean` |
| `BogoliubovSU3ParafermionWeld` | 3 | `proofs/BogoliubovSU3ParafermionWeld.lean` |
| `ChiralAffineBogoliubovWeld` | 3 | `proofs/ChiralAffineBogoliubovWeld.lean` |
| `ChiralCausalCone` | 3 | `proofs/ChiralCausalCone.lean` |
| `ChiralIsospinEOMSU2` | 3 | `proofs/ChiralIsospinEOMSU2.lean` |
| `ColorConfinementGNS` | 3 | `proofs/ColorConfinementGNS.lean` |
| `CuntzBoundarySolderRealization` | 3 | `proofs/CuntzBoundarySolderRealization.lean` |

## Recent finite spine additions

- `FiniteMatrixElementDuality` — `proofs/FiniteMatrixElementDuality.lean`
- `KreinCuntzShadow` — `proofs/KreinCuntzShadow.lean`
- `GNSQuotientFinite` — `proofs/GNSQuotientFinite.lean`
- `SpectralSquashCayleyDKT` — `proofs/SpectralSquashCayleyDKT.lean`
- `QSuperCuntzRegularization` — `proofs/QSuperCuntzRegularization.lean`
- `QSuperRegularizationRosetta` — `proofs/QSuperRegularizationRosetta.lean`
- `QRootOfUnityTruncation` — `proofs/QRootOfUnityTruncation.lean`
- `TKKJordanPairSocket` — `proofs/TKKJordanPairSocket.lean`
- `AmariChentsovFierzTorsion` — `proofs/AmariChentsovFierzTorsion.lean`

## Complete module inventory by theme

### Arithmetic / zeta / primons (43)

- `ArithmeticHamiltonianZeta` — `proofs/ArithmeticHamiltonianZeta.lean`; local imports: —
- `BiquaternionMobiusSquashing` — `proofs/BiquaternionMobiusSquashing.lean`; local imports: —
- `BosonicPrimonPartition` — `proofs/BosonicPrimonPartition.lean`; local imports: —
- `BostConnesDeformation` — `proofs/BostConnesDeformation.lean`; local imports: —
- `CayleyHilbertPolyaBraid` — `proofs/CayleyHilbertPolyaBraid.lean`; local imports: —
- `CuntzKriegerPrimon` — `proofs/CuntzKriegerPrimon.lean`; local imports: —
- `FermionicPrimonIndex` — `proofs/FermionicPrimonIndex.lean`; local imports: —
- `FermionicPrimonPartition` — `proofs/FermionicPrimonPartition.lean`; local imports: —
- `FiniteArithmeticUHFTrace` — `proofs/FiniteArithmeticUHFTrace.lean`; local imports: —
- `FiniteDirichletOccupation` — `proofs/FiniteDirichletOccupation.lean`; local imports: —
- `FiniteMobiusCoefficient` — `proofs/FiniteMobiusCoefficient.lean`; local imports: —
- `FinitePrimeFock` — `proofs/FinitePrimeFock.lean`; local imports: —
- `FixedLineRiemannKlein` — `proofs/FixedLineRiemannKlein.lean`; local imports: —
- `GeometricZeta` — `proofs/GeometricZeta.lean`; local imports: —
- `GrandCanonicalPrimon` — `proofs/GrandCanonicalPrimon.lean`; local imports: —
- `HilbertPolyaBivariant` — `proofs/HilbertPolyaBivariant.lean`; local imports: `ZetaCoordinateSymmetry`, `AnomalousKMSFlow`, `KasparovKreinCategory`, `UnifiedAnomalyArchitecture`
- `IJIRTRiemannDigest` — `proofs/IJIRTRiemannDigest.lean`; local imports: `MajoranaPrimonSpectralBridge`, `PrimonHilbertPolyaSeparation`
- `MajoranaPrimonSpectralBridge` — `proofs/MajoranaPrimonSpectralBridge.lean`; local imports: `SupergradedCuntzBdG`
- `MisraPrimeEntropyDigest` — `proofs/MisraPrimeEntropyDigest.lean`; local imports: `IJIRTRiemannDigest`
- `MobiusCantorTKKClosure` — `proofs/MobiusCantorTKKClosure.lean`; local imports: `CantorBoundaryCuntzFamily`, `ArtinMonodromyPin55`, `UHFInductiveColimit`
- `MobiusInversion` — `proofs/MobiusInversion.lean`; local imports: —
- `MobiusWittenIndex` — `proofs/MobiusWittenIndex.lean`; local imports: —
- `MobiusWittenKleinIndex` — `proofs/MobiusWittenKleinIndex.lean`; local imports: —
- `ModularEntropyPrimes` — `proofs/ModularEntropyPrimes.lean`; local imports: `PrimonBosonFermionDuality`, `PrimonCoarseGraining`, `MajoranaPrimonSpectralBridge`, `BosonicPrimonPartition`
- `PenroseArithmetic` — `proofs/PenroseArithmetic.lean`; local imports: —
- `primon_system` — `proofs/primon_system.lean`; local imports: —
- `PrimonBosonFermionDuality` — `proofs/PrimonBosonFermionDuality.lean`; local imports: `BosonicPrimonPartition`, `FermionicPrimonPartition`, `MajoranaPrimonSpectralBridge`
- `PrimonCoarseGrainedHilbertPolyaPotential` — `proofs/PrimonCoarseGrainedHilbertPolyaPotential.lean`; local imports: `PrimonHilbertPolyaSeparation`
- `PrimonCoarseGraining` — `proofs/PrimonCoarseGraining.lean`; local imports: `PrimonBosonFermionDuality`, `PrimonHilbertPolyaSeparation`, `UHFInductiveColimit`
- `PrimonCuntzTower` — `proofs/PrimonCuntzTower.lean`; local imports: `DiracColimit`, `KANFormalization`
- `PrimonFlavorCKM` — `proofs/PrimonFlavorCKM.lean`; local imports: `ChiralIsospinEOMSU2`, `PrimonCuntzTower`, `ContinuumAsColimitCounting`, `PrimonBosonFermionDuality`, `MajoranaPrimonSpectralBridge`
- `PrimonFockTraceBridge` — `proofs/PrimonFockTraceBridge.lean`; local imports: —
- `PrimonHilbertPolyaSeparation` — `proofs/PrimonHilbertPolyaSeparation.lean`; local imports: `PrimonFockTraceBridge`, `PrimonSuperThermodynamics`, `RiemannHypothesis`
- `PrimonSuperThermodynamics` — `proofs/PrimonSuperThermodynamics.lean`; local imports: —
- `PrimonZetaMobius` — `proofs/PrimonZetaMobius.lean`; local imports: —
- `ProjectiveKappaKleinMobius` — `proofs/ProjectiveKappaKleinMobius.lean`; local imports: —
- `RiemannHypothesis` — `proofs/RiemannHypothesis.lean`; local imports: —
- `RiemannHypothesisIJIRT172568` — `proofs/RiemannHypothesisIJIRT172568.lean`; local imports: —
- `RiemannKleinDuality` — `proofs/RiemannKleinDuality.lean`; local imports: —
- `SouriauHestenesMobiusPole` — `proofs/SouriauHestenesMobiusPole.lean`; local imports: —
- `zeta_zeros_moebius_klein` — `proofs/zeta_zeros_moebius_klein.lean`; local imports: —
- `ZetaCoordinateSymmetry` — `proofs/ZetaCoordinateSymmetry.lean`; local imports: —
- `ZetaSpectralBridge` — `proofs/ZetaSpectralBridge.lean`; local imports: `DiracColimit`, `PrimonCuntzTower`

### Braids / YBE / topology (46)

- `ArtinCentralizerMonodromy` — `proofs/ArtinCentralizerMonodromy.lean`; local imports: —
- `ArtinMonodromyPin55` — `proofs/ArtinMonodromyPin55.lean`; local imports: `BraidNegativeIdentityMonodromy`, `Clifford55AnomalyOSP`
- `BiquaternionLogarithmMonodromy` — `proofs/_deprecated/removed_from_default_2026_06_15/BiquaternionLogarithmMonodromy.lean`; local imports: —
- `BogoliubovBraidGraphWeld` — `proofs/BogoliubovBraidGraphWeld.lean`; local imports: `BogoliubovSU3ParafermionProofChain`, `B3RepresentationBridge`, `YangBaxterQSwap`, `BraidIdealDescent`
- `BraidCliffordIntegration` — `proofs/BraidCliffordIntegration.lean`; local imports: `FibonacciCliffordBridge`
- `BraidIdealDescent` — `proofs/BraidIdealDescent.lean`; local imports: —
- `BraidInductiveColimitComplement` — `proofs/BraidInductiveColimitComplement.lean`; local imports: —
- `BraidNegativeIdentityMonodromy` — `proofs/BraidNegativeIdentityMonodromy.lean`; local imports: —
- `ExceptionalBraidTopology` — `proofs/ExceptionalBraidTopology.lean`; local imports: —
- `ExceptionalNonorientableTopology` — `proofs/ExceptionalNonorientableTopology.lean`; local imports: —
- `ExceptionalPointMonodromy` — `proofs/ExceptionalPointMonodromy.lean`; local imports: `ExceptionalPointNullSector`, `DeterminantSupergrading`, `Z2NonAbelianBraiding`, `LieFlowCompilerBridge`
- `ExceptionalTopologicalBandStructures` — `proofs/ExceptionalTopologicalBandStructures.lean`; local imports: —
- `FibAnyonThm1` — `proofs/FibAnyonThm1.lean`; local imports: —
- `FibAnyonThm2` — `proofs/FibAnyonThm2.lean`; local imports: —
- `FibAnyonThm3` — `proofs/FibAnyonThm3.lean`; local imports: —
- `FibAnyonThm4` — `proofs/FibAnyonThm4.lean`; local imports: —
- `FibAnyonThm4_bridge` — `proofs/_deprecated/FibAnyonThm4_bridge.lean`; local imports: —
- `FibAnyonThm5` — `proofs/FibAnyonThm5.lean`; local imports: —
- `FibAnyonThm6_pentagon` — `proofs/FibAnyonThm6_pentagon.lean`; local imports: —
- `FibAnyonThm7_hexagon` — `proofs/FibAnyonThm7_hexagon.lean`; local imports: —
- `FibonacciGoldenBraiding` — `proofs/FibonacciGoldenBraiding.lean`; local imports: `Q8NuclearChirality`, `ModularEntropyPrimes`
- `GravitationalQuantumBraidDuality` — `proofs/GravitationalQuantumBraidDuality.lean`; local imports: `SU3LoopBraidDuality`, `BogoliubovWeylChemicalPotential`, `ChiralAffineBogoliubovWeld`, `WeylSU3ColorSymmetry`, `CantorBoundaryCuntzFamily`
- `GrothendieckGromovWittenYangBaxter` — `proofs/GrothendieckGromovWittenYangBaxter.lean`; local imports: `NonIsoConf3QuadricD4EPolynomial`
- `HexagonCocycle` — `proofs/HexagonCocycle.lean`; local imports: —
- `JonesBraidB3` — `proofs/JonesBraidB3.lean`; local imports: `TLChain`
- `ModularMonodromy` — `proofs/ModularMonodromy.lean`; local imports: —
- `NonOrientableBraid` — `proofs/_deprecated/removed_from_default_2026_06_15/NonOrientableBraid.lean`; local imports: —
- `PentagonPenroseWallpaperFractal` — `proofs/PentagonPenroseWallpaperFractal.lean`; local imports: —
- `ProjectiveCrystalTopology` — `proofs/_deprecated/removed_from_default_2026_06_15/ProjectiveCrystalTopology.lean`; local imports: —
- `SpectralYangBaxter` — `proofs/SpectralYangBaxter.lean`; local imports: —
- `SpinorMonodromySteppingStone` — `proofs/SpinorMonodromySteppingStone.lean`; local imports: —
- `SplitOctonionBraidSU3` — `proofs/SplitOctonionBraidSU3.lean`; local imports: —
- `SU3LoopBraidCuntzBoundary` — `proofs/SU3LoopBraidCuntzBoundary.lean`; local imports: `GellMannSU3`, `BogoliubovBraidGraphWeld`, `GellMannParafermionSolder`, `CantorBoundaryCuntzFamily`
- `SU3LoopBraidDuality` — `proofs/SU3LoopBraidDuality.lean`; local imports: `GellMannSU3`, `WeylSU3ColorSymmetry`, `CantorBoundaryCuntzFamily`, `JonesBraidB3`, `SupergradedCuntzBdG`, `BogoliubovBraidGraphWeld`
- `SUNLoopBraidCuntzBoundary` — `proofs/SUNLoopBraidCuntzBoundary.lean`; local imports: —
- `SUNQuantumBraidDuality` — `proofs/SUNQuantumBraidDuality.lean`; local imports: `GravitationalQuantumBraidDuality`
- `test_braid` — `proofs/test_braid.lean`; local imports: —
- `TestBraid` — `proofs/TestBraid.lean`; local imports: —
- `TLChain` — `proofs/TLChain.lean`; local imports: `ChiralCausalCone`
- `TopologicalColorCrystal` — `proofs/TopologicalColorCrystal.lean`; local imports: `SU3CorrelationExtraction`, `TripotentCliffordColimit`, `TopologicalColorCrystalFormal`
- `TopologicalColorCrystalFormal` — `proofs/TopologicalColorCrystalFormal.lean`; local imports: `SUNLoopBraidCuntzBoundary`, `SU3LoopBraidCuntzBoundary`, `HillWheelerUniversalProjection`, `FixedLineRiemannKlein`, `ProjectiveCrystalSymmetry`
- `WallpaperBulkAnyonProjection` — `proofs/WallpaperBulkAnyonProjection.lean`; local imports: —
- `WaveguideEPBraidSpec` — `proofs/WaveguideEPBraidSpec.lean`; local imports: —
- `YangBaxterQSwap` — `proofs/YangBaxterQSwap.lean`; local imports: —
- `YangBaxterQuotientDescent` — `proofs/YangBaxterQuotientDescent.lean`; local imports: —
- `Z2NonAbelianBraiding` — `proofs/Z2NonAbelianBraiding.lean`; local imports: `DeterminantSupergrading`, `TrifactorGeometry`, `LieFlowCompilerBridge`, `MobiusInversion`

### Clifford / chiral / spinors (37)

- `AmariChentsovFierzTorsion` — `proofs/AmariChentsovFierzTorsion.lean`; local imports: —
- `AtomicCliffordKAN` — `proofs/AtomicCliffordKAN.lean`; local imports: —
- `BiquaternionCliffordIso` — `proofs/BiquaternionCliffordIso.lean`; local imports: —
- `ChiralAffineBogoliubovWeld` — `proofs/ChiralAffineBogoliubovWeld.lean`; local imports: `SupergradedCuntzBdG`, `ChiralCausalCone`, `BogoliubovWeylChemicalPotential`
- `ChiralB3PresentedBridge` — `proofs/ChiralB3PresentedBridge.lean`; local imports: `ChiralTensorRecoupling`, `ChiralTensorMatrixBridge`, `TLChain`, `JonesBraidB3`, `YangBaxterQSwap`, `B3PresentedGroup`
- `ChiralCausalCone` — `proofs/ChiralCausalCone.lean`; local imports: `CPTAtom`, `SolderingSpinConnectionBogoliubov`, `SplitCliffordAlgebras`
- `ChiralCuntzInductive` — `proofs/ChiralCuntzInductive.lean`; local imports: `AlgebraicCuntzToeplitzInductive`
- `ChiralGUEWignerDyson` — `proofs/ChiralGUEWignerDyson.lean`; local imports: —
- `ChiralIsospinEOMSU2` — `proofs/ChiralIsospinEOMSU2.lean`; local imports: `ColorConfinementGNS`, `WeakIsospinSU2`, `ChiralAffineBogoliubovWeld`
- `ChiralPoincareSouriauBridge` — `proofs/ChiralPoincareSouriauBridge.lean`; local imports: —
- `ChiralScratch` — `proofs/_deprecated/removed_from_default_2026_06_15/ChiralScratch.lean`; local imports: —
- `ChiralTensorMatrixBridge` — `proofs/ChiralTensorMatrixBridge.lean`; local imports: `ChiralTensorRecoupling`, `TLChain`
- `ChiralTensorRecoupling` — `proofs/ChiralTensorRecoupling.lean`; local imports: `ChiralCausalCone`
- `ChiralTLDescent` — `proofs/ChiralTLDescent.lean`; local imports: `TLChain`, `ChiralTensorRecoupling`, `ChiralTensorMatrixBridge`, `BraidIdealDescent`
- `ChiralTwistedFibration` — `proofs/ChiralTwistedFibration.lean`; local imports: —
- `Cl11ChiralCARBridge` — `proofs/Cl11ChiralCARBridge.lean`; local imports: `ChiralCausalCone`
- `Clifford55AnomalyOSP` — `proofs/Clifford55AnomalyOSP.lean`; local imports: —
- `clifford_seed` — `proofs/clifford_seed.lean`; local imports: —
- `CliffordFiveFiveAnomaly` — `proofs/_deprecated/removed_from_default_2026_06_15/CliffordFiveFiveAnomaly.lean`; local imports: —
- `CliffordInductiveTripotent` — `proofs/_deprecated/removed_from_default_2026_06_15/CliffordInductiveTripotent.lean`; local imports: —
- `ColorCARStandardModel` — `proofs/ColorCARStandardModel.lean`; local imports: `ChiralCausalCone`, `ChiralTensorRecoupling`, `BraidIdealDescent`, `ChiralTLDescent`
- `ConcreteCliffordDiracTower` — `proofs/ConcreteCliffordDiracTower.lean`; local imports: —
- `CPTAtom` — `proofs/CPTAtom.lean`; local imports: —
- `FibonacciCliffordBridge` — `proofs/FibonacciCliffordBridge.lean`; local imports: —
- `FierzIdentities` — `proofs/FierzIdentities.lean`; local imports: `ChiralCausalCone`
- `FureyCharges` — `proofs/FureyCharges.lean`; local imports: `ColorCARStandardModel`
- `FureyZornFermionBridge` — `proofs/FureyZornFermionBridge.lean`; local imports: `ZornOPParavector`
- `LorentzChiralCuntzBridge` — `proofs/LorentzChiralCuntzBridge.lean`; local imports: `ChiralCausalCone`, `ChiralPoincareSouriauBridge`, `CuntzDeformedSuperPoincare`, `FierzIdentities`
- `LQGProblemsResolvedByChiralFramework` — `proofs/LQGProblemsResolvedByChiralFramework.lean`; local imports: —
- `OpticalAndreevSpinor` — `proofs/OpticalAndreevSpinor.lean`; local imports: —
- `PenroseSpinNetworkChiralIsomorphism` — `proofs/PenroseSpinNetworkChiralIsomorphism.lean`; local imports: —
- `Q8NuclearChirality` — `proofs/Q8NuclearChirality.lean`; local imports: `WeakIsospinSU2`, `ChiralCausalCone`, `ChiralAffineBogoliubovWeld`
- `S3ColorSpinorDecomposition` — `proofs/S3ColorSpinorDecomposition.lean`; local imports: `WeylSU3ColorSymmetry`, `GellMannParafermionSolder`, `BogoliubovBraidGraphWeld`, `SU3LoopBraidDuality`
- `SolovievQPNMChiralCuntz` — `proofs/SolovievQPNMChiralCuntz.lean`; local imports: —
- `SplitCliffordAlgebras` — `proofs/SplitCliffordAlgebras.lean`; local imports: —
- `TripotentCliffordColimit` — `proofs/TripotentCliffordColimit.lean`; local imports: —
- `ZornChiralBridge` — `proofs/ZornChiralBridge.lean`; local imports: `ZornParavectorNullspace`, `ChiralCausalCone`

### Core algebra / misc (136)

- `AffineDynkinGoutevTonev` — `proofs/AffineDynkinGoutevTonev.lean`; local imports: `iR`, `GoutevTonevPrinciple`
- `ArtinParityFlowWitness` — `proofs/ArtinParityFlowWitness.lean`; local imports: `BraidCliffordIntegration`
- `AssociativeCommutatorLie` — `proofs/AssociativeCommutatorLie.lean`; local imports: —
- `B3PresentedGroup` — `proofs/B3PresentedGroup.lean`; local imports: `JonesBraidB3`
- `B3RepresentationBridge` — `proofs/B3RepresentationBridge.lean`; local imports: `B3PresentedGroup`
- `BaxterAnchorManifest` — `proofs/BaxterAnchorManifest.lean`; local imports: `ChiralCausalCone`, `ChiralTensorRecoupling`, `TLChain`, `JonesBraidB3`, `YangBaxterQSwap`, `B3PresentedGroup`, `SpectralYangBaxter`, `FibAnyonThm4`, `HexagonCocycle`, `BraidNegativeIdentityMonodromy`, `ArtinMonodromyPin55`
- `BiquaternionExpClosure` — `proofs/BiquaternionExpClosure.lean`; local imports: —
- `BiquaternionKANnilpotent` — `proofs/BiquaternionKANnilpotent.lean`; local imports: —
- `BiquaternionLaplaceResolvent` — `proofs/_deprecated/removed_from_default_2026_06_15/BiquaternionLaplaceResolvent.lean`; local imports: —
- `BiquaternionLaplaceTripotent` — `proofs/BiquaternionLaplaceTripotent.lean`; local imports: —
- `BiquaternionNegativeRootsLog` — `proofs/BiquaternionNegativeRootsLog.lean`; local imports: —
- `BPSPositiveEnergyBound` — `proofs/BPSPositiveEnergyBound.lean`; local imports: —
- `bridge_full` — `proofs/bridge_full.lean`; local imports: —
- `CausalityCondensate` — `proofs/CausalityCondensate.lean`; local imports: —
- `CheckLimit` — `proofs/CheckLimit.lean`; local imports: —
- `CheckPUnitAdd` — `proofs/CheckPUnitAdd.lean`; local imports: —
- `ComplexTemperatureRH` — `proofs/ComplexTemperatureRH.lean`; local imports: —
- `ContinuumAsColimitCounting` — `proofs/ContinuumAsColimitCounting.lean`; local imports: `JaynesLDDPGNSColimit`
- `ConvexAlgebraicDuality` — `proofs/ConvexAlgebraicDuality.lean`; local imports: —
- `CPTConformantTriaxialHamiltonian` — `proofs/CPTConformantTriaxialHamiltonian.lean`; local imports: `MirrorNucleiIsospinGNS`, `Q8NuclearChirality`
- `CptFractalClosure` — `proofs/CptFractalClosure.lean`; local imports: —
- `CptTensorFractal` — `proofs/_deprecated/removed_from_default_2026_06_15/CptTensorFractal.lean`; local imports: —
- `CurryHowardLambekColimit` — `proofs/CurryHowardLambekColimit.lean`; local imports: `ContinuumAsColimitCounting`, `HillWheelerUniversalProjection`
- `CurryHowardLambekPhysics` — `proofs/CurryHowardLambekPhysics.lean`; local imports: `ContinuumAsColimitCounting`, `MobiusCantorTKKClosure`, `PrimonCoarseGraining`
- `DeterminantMoebiusFunctor` — `proofs/DeterminantMoebiusFunctor.lean`; local imports: `DeterminantSupergrading`, `TrifactorGeometry`, `MobiusInversion`
- `DeterminantSupergrading` — `proofs/DeterminantSupergrading.lean`; local imports: —
- `discrete_maxflow_mincut` — `proofs/discrete_maxflow_mincut.lean`; local imports: —
- `DupontHypersurfaceOSModel` — `proofs/DupontHypersurfaceOSModel.lean`; local imports: `NonIsoConf3QuadricD4PointCount`
- `EuclideanNilpotentObstruction` — `proofs/EuclideanNilpotentObstruction.lean`; local imports: `ChiralCausalCone`
- `ExceptionalPointCollapse` — `proofs/ExceptionalPointCollapse.lean`; local imports: —
- `ExceptionalPointNullSector` — `proofs/ExceptionalPointNullSector.lean`; local imports: —
- `FermiLevelGap` — `proofs/FermiLevelGap.lean`; local imports: —
- `FiniteMatrixElementDuality` — `proofs/FiniteMatrixElementDuality.lean`; local imports: —
- `FractalHamiltonian` — `proofs/FractalHamiltonian.lean`; local imports: —
- `GlideModularJ` — `proofs/GlideModularJ.lean`; local imports: —
- `GlideSuperchargeCasimir` — `proofs/GlideSuperchargeCasimir.lean`; local imports: —
- `GlideSymmetricInvariant` — `proofs/GlideSymmetricInvariant.lean`; local imports: —
- `goutev_principle` — `proofs/goutev_principle.lean`; local imports: —
- `GoutevTonevPrinciple` — `proofs/GoutevTonevPrinciple.lean`; local imports: `SouriauOperatorThermodynamics`, `InformationGeometricCutoff`
- `GrandCanonicalBerezinian` — `proofs/GrandCanonicalBerezinian.lean`; local imports: —
- `GrothendieckMotiveGWInvariant` — `proofs/GrothendieckMotiveGWInvariant.lean`; local imports: —
- `GT_FromText` — `proofs/GT_FromText.lean`; local imports: —
- `GUE2x2ExponentialFamily` — `proofs/GUE2x2ExponentialFamily.lean`; local imports: —
- `HillWheelerProjection` — `proofs/HillWheelerProjection.lean`; local imports: `MajoranaPrimonSpectralBridge`, `PrimonBosonFermionDuality`, `CantorBoundaryCuntzFamily`
- `HillWheelerUniversalProjection` — `proofs/HillWheelerUniversalProjection.lean`; local imports: `HillWheelerProjection`, `JaynesLDDPGNSColimit`, `ProjectiveAffineConformalClosure55`
- `HurwitzQuaternionSpectrum` — `proofs/HurwitzQuaternionSpectrum.lean`; local imports: `HurwitzTwistedSector`
- `HurwitzTwistedSector` — `proofs/HurwitzTwistedSector.lean`; local imports: `ZetaSpectralBridge`
- `IdealDescentProof` — `proofs/IdealDescentProof.lean`; local imports: `BraidIdealDescent`, `YangBaxterQuotientDescent`, `JonesBraidB3`, `YangBaxterQSwap`
- `InductiveAnalyticFlow` — `proofs/InductiveAnalyticFlow.lean`; local imports: `LieAlgebraColimit`
- `InfoGeometry` — `proofs/InfoGeometry.lean`; local imports: `SplitCliffordAlgebras`, `ProjectiveCuntzToeplitzCARCCR`, `ProjectivePenrosePGA`, `NoncommutativeTilingAlgebra`, `ConvexAlgebraicDuality`, `GoldenCCR`, `FractalHamiltonian`, `BlackHoleHolography`, `GoldenSpectralTriple`, `InformationGeometricCutoff`, `EinsteinThermodynamicBridge`, `UnifiedGaugeField`, `DiracKreinMetriplectic`, `SuperBerezinianKlein`, `GlideSymmetricInvariant`, `CubicJordanPeirceDecomposition`, `MinkowskiBiquaternion`, `DiracFourierMellin`, `PolynomialSymmetryOperators`, `BiquaternionKANnilpotent`, `CptFractalClosure`, `GravitySoldering`, `WallpaperIsometry`, `BraidIdealDescent`, `GohbergKreinIndex`, `ArtinCentralizerMonodromy`, `ArtinMonodromyPin55`
- `iR` — `proofs/iR.lean`; local imports: —
- `IwasawaAnalyticityLock` — `proofs/IwasawaAnalyticityLock.lean`; local imports: `KANFormalization`, `PrimonCuntzTower`
- `IwasawaKUnification` — `proofs/IwasawaKUnification.lean`; local imports: —
- `J_duality_chain` — `proofs/J_duality_chain.lean`; local imports: —
- `JaynesFinitePartitionColimit` — `proofs/JaynesFinitePartitionColimit.lean`; local imports: —
- `JaynesFiniteSetsColimitBridge` — `proofs/JaynesFiniteSetsColimitBridge.lean`; local imports: —
- `JaynesLeanColimitBridge` — `proofs/JaynesLeanColimitBridge.lean`; local imports: —
- `KANFormalization` — `proofs/KANFormalization.lean`; local imports: —
- `KANLogDetUnification` — `proofs/KANLogDetUnification.lean`; local imports: `KanCayley`, `DeterminantSupergrading`, `KreinDeterminantAnalyticity`
- `KANTraceSectorization` — `proofs/KANTraceSectorization.lean`; local imports: `KanCayley`, `TraceSeparationFlow`
- `LieAlgebraColimit` — `proofs/LieAlgebraColimit.lean`; local imports: —
- `LieFlowCompilerBridge` — `proofs/LieFlowCompilerBridge.lean`; local imports: `LieFlowMatching`, `TrifactorGeometry`, `DeterminantSupergrading`
- `LieFlowMatching` — `proofs/LieFlowMatching.lean`; local imports: —
- `LiuCollinsAffineInvariance` — `proofs/_deprecated/removed_from_default_2026_06_15/LiuCollinsAffineInvariance.lean`; local imports: —
- `LogDetSuperKahlerBarrier` — `proofs/LogDetSuperKahlerBarrier.lean`; local imports: —
- `master_equation` — `proofs/master_equation.lean`; local imports: —
- `Matrix2KANPauliChain` — `proofs/Matrix2KANPauliChain.lean`; local imports: —
- `MellinHeatKernelBridge` — `proofs/MellinHeatKernelBridge.lean`; local imports: `ZetaSpectralBridge`
- `MillenniumRosettaStone` — `proofs/MillenniumRosettaStone.lean`; local imports: `HolographicProxyQLimit`, `PrimonHilbertPolyaSeparation`
- `ModularAutomorphismGroup` — `proofs/ModularAutomorphismGroup.lean`; local imports: —
- `ModularGlideCPT` — `proofs/ModularGlideCPT.lean`; local imports: —
- `ModularItakuraBiquaternion` — `proofs/ModularItakuraBiquaternion.lean`; local imports: —
- `NilpotentItakuraSaito` — `proofs/NilpotentItakuraSaito.lean`; local imports: —
- `NonHermitianSMatrixDefect` — `proofs/NonHermitianSMatrixDefect.lean`; local imports: `ScatteringSMatrix`
- `NonIsoConf3DeRhamCooperad` — `proofs/NonIsoConf3DeRhamCooperad.lean`; local imports: `QuadraticConfiguration3`, `NonIsoConf3OrlikSolomon`
- `NonIsoConf3DupontGysinModel` — `proofs/NonIsoConf3DupontGysinModel.lean`; local imports: `DupontHypersurfaceOSModel`, `PenroseSpinIncidenceTessellation`
- `NonIsoConf3OrlikSolomon` — `proofs/NonIsoConf3OrlikSolomon.lean`; local imports: —
- `NonIsoConf3QuadricCompactification` — `proofs/NonIsoConf3QuadricCompactification.lean`; local imports: `DupontHypersurfaceOSModel`
- `NonIsoConf3QuadricD4EPolynomial` — `proofs/NonIsoConf3QuadricD4EPolynomial.lean`; local imports: `NonIsoConf3QuadricD4PointCount`
- `NonIsoConf3QuadricD4Model` — `proofs/NonIsoConf3QuadricD4Model.lean`; local imports: `NonIsoConf3OrlikSolomon`
- `NonIsoConf3QuadricD4PointCount` — `proofs/NonIsoConf3QuadricD4PointCount.lean`; local imports: `NonIsoConf3QuadricD4Model`
- `NonIsoConf3ThreePointDeRhamCooperad` — `proofs/NonIsoConf3ThreePointDeRhamCooperad.lean`; local imports: `QuadraticConfiguration3`, `NonIsoConf3OrlikSolomon`, `NonIsoConf3QuadricD4Model`, `NonIsoConf3QuadricD4PointCount`
- `OakuTakayamaDModuleDeRham` — `proofs/OakuTakayamaDModuleDeRham.lean`; local imports: —
- `OctonionMatrixEncodings` — `proofs/OctonionMatrixEncodings.lean`; local imports: —
- `OctonionMatrixObstruction` — `proofs/_deprecated/removed_from_default_2026_06_15/OctonionMatrixObstruction.lean`; local imports: —
- `PaperwallDiscreteSUSY` — `proofs/_deprecated/removed_from_default_2026_06_15/PaperwallDiscreteSUSY.lean`; local imports: —
- `PaperwallSUSY` — `proofs/_deprecated/removed_from_default_2026_06_15/PaperwallSUSY.lean`; local imports: —
- `ParafermionIdentityRealization` — `proofs/ParafermionIdentityRealization.lean`; local imports: `GellMannParafermionSolder`, `AlgebraicCuntzQuotient`, `UHFInductiveColimit`
- `PartitionPoleCriterion` — `proofs/PartitionPoleCriterion.lean`; local imports: —
- `PauliZornTrifactor` — `proofs/PauliZornTrifactor.lean`; local imports: —
- `PhotonicCMTTMM` — `proofs/PhotonicCMTTMM.lean`; local imports: `TwoPortScatteringCoefficients`
- `PhotonicHardwareLayout` — `proofs/PhotonicHardwareLayout.lean`; local imports: `TransferMatrixScattering`
- `PlatycosmKTheory` — `proofs/_deprecated/removed_from_default_2026_06_15/PlatycosmKTheory.lean`; local imports: —
- `PublishedThesisArchitecture` — `proofs/PublishedThesisArchitecture.lean`; local imports: —
- `QCDScaleExtraction` — `proofs/QCDScaleExtraction.lean`; local imports: `DikinOnsagerCramerRaoOperator`, `ColorConfinementGNS`
- `QuadraticConfiguration3` — `proofs/QuadraticConfiguration3.lean`; local imports: —
- `RelativisticBiquaternionKAN` — `proofs/RelativisticBiquaternionKAN.lean`; local imports: —
- `RGFixedPoint` — `proofs/_deprecated/removed_from_default_2026_06_15/RGFixedPoint.lean`; local imports: —
- `rigorous_proofs` — `proofs/rigorous_proofs.lean`; local imports: —
- `RP3Octupole` — `proofs/_deprecated/removed_from_default_2026_06_15/RP3Octupole.lean`; local imports: —
- `ScatteringSMatrix` — `proofs/ScatteringSMatrix.lean`; local imports: `BraidCliffordIntegration`
- `SiliconPhotonicChipCoefficients` — `proofs/SiliconPhotonicChipCoefficients.lean`; local imports: `NonHermitianSMatrixDefect`
- `SocketDischargeChain` — `proofs/SocketDischargeChain.lean`; local imports: `TwistorParafermionBoundary`, `PrimonBosonFermionDuality`, `PrimonCoarseGraining`, `CantorBoundaryCuntzFamily`
- `SolderingForms` — `proofs/SolderingForms.lean`; local imports: —
- `SolderingRoundTrip` — `proofs/SolderingRoundTrip.lean`; local imports: —
- `SplitOctonionNilpotent` — `proofs/_deprecated/removed_from_default_2026_06_15/SplitOctonionNilpotent.lean`; local imports: —
- `SuperchargeSquare` — `proofs/SuperchargeSquare.lean`; local imports: —
- `SuperPartitionBerezinian` — `proofs/SuperPartitionBerezinian.lean`; local imports: —
- `TemperleyLieb` — `proofs/_deprecated/TemperleyLieb.lean`; local imports: —
- `test` — `proofs/test.lean`; local imports: —
- `test_noncomm` — `proofs/test_noncomm.lean`; local imports: —
- `test_ring` — `proofs/test_ring.lean`; local imports: —
- `test_simp` — `proofs/test_simp.lean`; local imports: —
- `test_smul` — `proofs/test_smul.lean`; local imports: —
- `test_smul2` — `proofs/test_smul2.lean`; local imports: —
- `test_tl` — `proofs/_deprecated/test_tl.lean`; local imports: —
- `test_tl2` — `proofs/_deprecated/test_tl2.lean`; local imports: —
- `test_wrapper` — `proofs/test_wrapper.lean`; local imports: —
- `TestAF` — `proofs/TestAF.lean`; local imports: —
- `TestHex` — `proofs/_deprecated/TestHex.lean`; local imports: —
- `TestImport2` — `proofs/TestImport2.lean`; local imports: `tomita_kms_v4`
- `TestImportGP` — `proofs/TestImportGP.lean`; local imports: `goutev_principle`
- `TestImportKB` — `proofs/TestImportKB.lean`; local imports: `KleinBottle`
- `TestTL` — `proofs/TestTL.lean`; local imports: —
- `TetronParityLifetimeBridge` — `proofs/TetronParityLifetimeBridge.lean`; local imports: —
- `ThesisMaster` — `proofs/ThesisMaster.lean`; local imports: —
- `TraceSeparationFlow` — `proofs/TraceSeparationFlow.lean`; local imports: `KanCayley`
- `TransferMatrixScattering` — `proofs/TransferMatrixScattering.lean`; local imports: `Matrix2KANPauliChain`
- `TransformsAndScale` — `proofs/TransformsAndScale.lean`; local imports: —
- `TrifactorGeometry` — `proofs/TrifactorGeometry.lean`; local imports: —
- `TwoPortScatteringCoefficients` — `proofs/TwoPortScatteringCoefficients.lean`; local imports: `SiliconPhotonicChipCoefficients`
- `ZornAssociatorSplitOctonion` — `proofs/ZornAssociatorSplitOctonion.lean`; local imports: —
- `ZornOPParavector` — `proofs/ZornOPParavector.lean`; local imports: —
- `ZornParavectorNullspace` — `proofs/ZornParavectorNullspace.lean`; local imports: —
- `ZornScalingFlow` — `proofs/ZornScalingFlow.lean`; local imports: —
- `ZornScalingFlowOrdered` — `proofs/ZornScalingFlowOrdered.lean`; local imports: —

### Gauge / Standard Model color (16)

- `BogoliubovSU3ParafermionProofChain` — `proofs/BogoliubovSU3ParafermionProofChain.lean`; local imports: `BogoliubovSU3ParafermionWeld`
- `BogoliubovSU3ParafermionWeld` — `proofs/BogoliubovSU3ParafermionWeld.lean`; local imports: `BogoliubovWeylChemicalPotential`, `GellMannSU3`, `ColorCARStandardModel`
- `CayleySchreierGauge` — `proofs/_deprecated/removed_from_default_2026_06_15/CayleySchreierGauge.lean`; local imports: —
- `determinant_weyl_gauge` — `proofs/determinant_weyl_gauge.lean`; local imports: —
- `GellMannParafermionRealizationRoutesSynthesis` — `proofs/GellMannParafermionRealizationRoutesSynthesis.lean`; local imports: `CuntzBoundarySolderRealization`, `WeylSolderedParafermionSymmetry`, `BogoliubovSU3ParafermionWeld`, `BogoliubovSU3ParafermionProofChain`, `CantorBoundaryCuntzFamily`, `ChiralAffineBogoliubovWeld`
- `GellMannParafermionSolder` — `proofs/GellMannParafermionSolder.lean`; local imports: `BogoliubovSU3ParafermionProofChain`
- `GellMannSU3` — `proofs/GellMannSU3.lean`; local imports: —
- `HolographicGaugeSymmetryUniqueness` — `proofs/HolographicGaugeSymmetryUniqueness.lean`; local imports: `SU3LoopBraidCuntzBoundary`, `ItFromBitProjectiveHolographicSynthesis`, `Clifford55AnomalyOSP`, `YangBaxterQSwap`
- `HolographicGaugeSymmetryUniqueness20` — `proofs/HolographicGaugeSymmetryUniqueness20.lean`; local imports: `HolographicGaugeSymmetryUniqueness`
- `OctonionicStandardModel` — `proofs/_deprecated/removed_from_default_2026_06_15/OctonionicStandardModel.lean`; local imports: —
- `ProjectiveWallpaperGaugePSA` — `proofs/ProjectiveWallpaperGaugePSA.lean`; local imports: —
- `SU3CorrelationExtraction` — `proofs/SU3CorrelationExtraction.lean`; local imports: `HolographicGaugeSymmetryUniqueness`, `MajoranaPrimonSpectralBridge`, `PrimonBosonFermionDuality`
- `UnifiedGaugeField` — `proofs/UnifiedGaugeField.lean`; local imports: `EinsteinThermodynamicBridge`
- `WeakIsospinSU2` — `proofs/WeakIsospinSU2.lean`; local imports: `ChiralCausalCone`
- `WeylGaugeColimitWeld` — `proofs/WeylGaugeColimitWeld.lean`; local imports: `GaugeUHFLift`, `HestenesCuntzPhaseSpace`
- `WeylSU3ColorSymmetry` — `proofs/WeylSU3ColorSymmetry.lean`; local imports: `BogoliubovSU3ParafermionProofChain`, `SplitOctonionBraidSU3`

### Geometry / holography / tilings (54)

- `BlackHoleHolography` — `proofs/BlackHoleHolography.lean`; local imports: —
- `BrillouinKleinNilpotentAttractor` — `proofs/BrillouinKleinNilpotentAttractor.lean`; local imports: —
- `CompleteHolographicDictionary` — `proofs/CompleteHolographicDictionary.lean`; local imports: —
- `CP3CantorGeometricObstruction` — `proofs/CP3CantorGeometricObstruction.lean`; local imports: `TwistorParafermionBoundary`, `CantorBoundaryCuntzFamily`
- `Crystallographic` — `proofs/Crystallographic.lean`; local imports: —
- `ExceptionalKleinGlideEP` — `proofs/ExceptionalKleinGlideEP.lean`; local imports: —
- `FinalHolographicThesisSeal` — `proofs/_deprecated/removed_from_default_2026_06_15/FinalHolographicThesisSeal.lean`; local imports: —
- `FractalKleinSUSYFramework` — `proofs/FractalKleinSUSYFramework.lean`; local imports: —
- `GrandHolographicLoop` — `proofs/GrandHolographicLoop.lean`; local imports: —
- `GrandHolographicTheorem` — `proofs/GrandHolographicTheorem.lean`; local imports: —
- `HolographicDictionarySynthesis` — `proofs/_deprecated/removed_from_default_2026_06_15/HolographicDictionarySynthesis.lean`; local imports: `CliffordFiveFiveAnomaly`, `MobiusWittenIndex`, `KleinNilpotentThermo`, `RiemannKleinDuality`, `ZornParavectorNullspace`, `OctonionMatrixObstruction`
- `HolographicErlangenCompletion` — `proofs/_deprecated/removed_from_default_2026_06_15/HolographicErlangenCompletion.lean`; local imports: —
- `HolographicProxyQLimit` — `proofs/HolographicProxyQLimit.lean`; local imports: `TopologicalColorCrystal`, `GravitationalQuantumBraidDuality`, `SU3CorrelationExtraction`, `SU3LoopBraidDuality`, `ChiralAffineBogoliubovWeld`
- `HolographicScaleExtinctions` — `proofs/_deprecated/removed_from_default_2026_06_15/HolographicScaleExtinctions.lean`; local imports: —
- `ItFromBitProjectiveHolographicSynthesis` — `proofs/ItFromBitProjectiveHolographicSynthesis.lean`; local imports: `TwistorParafermionBoundary`, `ProjectiveAffineConformalClosure55`, `HillWheelerUniversalProjection`, `PrimonHilbertPolyaSeparation`
- `KleinBottle` — `proofs/KleinBottle.lean`; local imports: —
- `KleinBottleKANCoordinates` — `proofs/KleinBottleKANCoordinates.lean`; local imports: `DeterminantSupergrading`, `IwasawaKUnification`, `KleinBottleSymmetry`, `KleinFourAnomalyCancellation`
- `KleinBottleParafermionInvariant` — `proofs/KleinBottleParafermionInvariant.lean`; local imports: —
- `KleinBottleSymmetry` — `proofs/KleinBottleSymmetry.lean`; local imports: —
- `KleinErlangenGrothendieckBridge` — `proofs/KleinErlangenGrothendieckBridge.lean`; local imports: `PenroseSpinIncidenceTessellation`, `TKKJordanPairSocket`
- `KleinGeometrySupergraded` — `proofs/_deprecated/removed_from_default_2026_06_15/KleinGeometrySupergraded.lean`; local imports: —
- `KleinGrapheneTunneling` — `proofs/KleinGrapheneTunneling.lean`; local imports: —
- `KleinParafermionCohomology` — `proofs/KleinParafermionCohomology.lean`; local imports: —
- `ModularHolographicMetric` — `proofs/ModularHolographicMetric.lean`; local imports: —
- `MorandiWallpaperCohomology` — `proofs/MorandiWallpaperCohomology.lean`; local imports: —
- `MotivicHolographyGroebnerLFunction` — `proofs/MotivicHolographyGroebnerLFunction.lean`; local imports: `KleinErlangenGrothendieckBridge`
- `NoncommutativeTilingAlgebra` — `proofs/NoncommutativeTilingAlgebra.lean`; local imports: —
- `NonInvertiblePenroseCategoricalSymmetry` — `proofs/NonInvertiblePenroseCategoricalSymmetry.lean`; local imports: —
- `PaperwallHolographicSUSY` — `proofs/PaperwallHolographicSUSY.lean`; local imports: —
- `penrose_wallpaper_colimit` — `proofs/penrose_wallpaper_colimit.lean`; local imports: —
- `PenroseAF` — `proofs/PenroseAF.lean`; local imports: —
- `PenroseSpinIncidenceTessellation` — `proofs/PenroseSpinIncidenceTessellation.lean`; local imports: `PenroseSpinTilingConfig`, `NonIsoConf3QuadricD4PointCount`
- `PenroseSpinTilingCapstone` — `proofs/PenroseSpinTilingCapstone.lean`; local imports: `PenroseSpinTilingConfig`, `PenroseSpinIncidenceTessellation`, `NonIsoConf3QuadricD4PointCount`, `KleinErlangenGrothendieckBridge`, `NonIsoConf3DupontGysinModel`, `NonIsoConf3ThreePointDeRhamCooperad`, `NonIsoConf3DeRhamCooperad`
- `PenroseSpinTilingConfig` — `proofs/PenroseSpinTilingConfig.lean`; local imports: `GrothendieckGromovWittenYangBaxter`, `NonIsoConf3QuadricD4Model`
- `ProjectiveAffineConformalClosure55` — `proofs/ProjectiveAffineConformalClosure55.lean`; local imports: `Clifford55AnomalyOSP`, `RiemannHypothesis`
- `ProjectiveCrystalKappa` — `proofs/ProjectiveCrystalKappa.lean`; local imports: —
- `ProjectiveCrystalMackeyDecomposition` — `proofs/ProjectiveCrystalMackeyDecomposition.lean`; local imports: —
- `ProjectiveCrystalSymmetry` — `proofs/ProjectiveCrystalSymmetry.lean`; local imports: —
- `ProjectiveGlideSuperchargeUnification` — `proofs/ProjectiveGlideSuperchargeUnification.lean`; local imports: —
- `ProjectivePenrosePGA` — `proofs/ProjectivePenrosePGA.lean`; local imports: —
- `ProjectiveSymmetryAlgebra` — `proofs/_deprecated/removed_from_default_2026_06_15/ProjectiveSymmetryAlgebra.lean`; local imports: —
- `SuperBerezinianKlein` — `proofs/SuperBerezinianKlein.lean`; local imports: —
- `TitsBruhatBrillouinKlein` — `proofs/TitsBruhatBrillouinKlein.lean`; local imports: —
- `TripotentPenroseHolography` — `proofs/_deprecated/removed_from_default_2026_06_15/TripotentPenroseHolography.lean`; local imports: —
- `TwistedHeckeKleinBottle` — `proofs/_deprecated/removed_from_default_2026_06_15/TwistedHeckeKleinBottle.lean`; local imports: —
- `TwistorParafermionBoundary` — `proofs/TwistorParafermionBoundary.lean`; local imports: `CantorBoundaryCuntzFamily`, `GellMannParafermionSolder`, `ProjectiveAffineConformalClosure55`
- `UnorientedS3KleinTQFT` — `proofs/UnorientedS3KleinTQFT.lean`; local imports: `MobiusCantorTKKClosure`, `SU3LoopBraidDuality`
- `VerberckWallpaperFourier` — `proofs/VerberckWallpaperFourier.lean`; local imports: —
- `WallpaperClassification` — `proofs/_deprecated/removed_from_default_2026_06_15/WallpaperClassification.lean`; local imports: —
- `WallpaperCohomology` — `proofs/WallpaperCohomology.lean`; local imports: —
- `WallpaperFermionSuperconductingGap` — `proofs/WallpaperFermionSuperconductingGap.lean`; local imports: —
- `WallpaperIsometry` — `proofs/WallpaperIsometry.lean`; local imports: —
- `WallpaperMetamaterialDataset` — `proofs/WallpaperMetamaterialDataset.lean`; local imports: —
- `WallpaperSemidirectProduct` — `proofs/_deprecated/removed_from_default_2026_06_15/WallpaperSemidirectProduct.lean`; local imports: —

### Information geometry / thermodynamics (17)

- `CanonicalSouriauPauliThermodynamics` — `proofs/CanonicalSouriauPauliThermodynamics.lean`; local imports: —
- `CramerRaoFisher` — `proofs/CramerRaoFisher.lean`; local imports: —
- `DikinGoutevTonevBridge` — `proofs/DikinGoutevTonevBridge.lean`; local imports: `KreinMoorePenrose`, `InformationGeometricCutoff`, `SouriauOperatorThermodynamics`
- `EinsteinThermodynamicBridge` — `proofs/EinsteinThermodynamicBridge.lean`; local imports: `InformationGeometricCutoff`, `BlackHoleHolography`
- `InformationGeometricCutoff` — `proofs/InformationGeometricCutoff.lean`; local imports: —
- `InformationTheoreticPNT` — `proofs/InformationTheoreticPNT.lean`; local imports: `ModularEntropyPrimes`
- `KleinNilpotentThermo` — `proofs/_deprecated/removed_from_default_2026_06_15/KleinNilpotentThermo.lean`; local imports: —
- `krein_souriau` — `proofs/krein_souriau.lean`; local imports: —
- `krein_souriau_full` — `proofs/krein_souriau_full.lean`; local imports: —
- `RelativeModularStateDikin` — `proofs/RelativeModularStateDikin.lean`; local imports: `GoutevTonevPrinciple`
- `SouriauBiquaternionGaussian` — `proofs/SouriauBiquaternionGaussian.lean`; local imports: —
- `SouriauComplexTemperature` — `proofs/SouriauComplexTemperature.lean`; local imports: —
- `SouriauGaussian` — `proofs/_deprecated/removed_from_default_2026_06_15/SouriauGaussian.lean`; local imports: —
- `SouriauHestenesKrein` — `proofs/SouriauHestenesKrein.lean`; local imports: —
- `SouriauMoebiusCoupling` — `proofs/SouriauMoebiusCoupling.lean`; local imports: —
- `SouriauThermoColimit` — `proofs/SouriauThermoColimit.lean`; local imports: —
- `thermo_gauge_flow` — `proofs/thermo_gauge_flow.lean`; local imports: —

### Operator algebras / CAR-CCR-Cuntz (55)

- `AlgebraicCuntzQuotient` — `proofs/AlgebraicCuntzQuotient.lean`; local imports: —
- `AlgebraicCuntzToeplitzInductive` — `proofs/AlgebraicCuntzToeplitzInductive.lean`; local imports: —
- `BuresMetricClosedCartography` — `proofs/BuresMetricClosedCartography.lean`; local imports: —
- `CantorBoundaryCuntzFamily` — `proofs/CantorBoundaryCuntzFamily.lean`; local imports: `ParafermionIdentityRealization`, `UHFInductiveColimit`
- `CARCCRCantorFock` — `proofs/CARCCRCantorFock.lean`; local imports: —
- `CartanKleinBottleGeometry` — `proofs/CartanKleinBottleGeometry.lean`; local imports: `MobiusCantorTKKClosure`, `ProjectiveAffineConformalClosure55`, `Clifford55AnomalyOSP`, `MajoranaPrimonSpectralBridge`
- `CartanWeylBogoliubovGravity` — `proofs/CartanWeylBogoliubovGravity.lean`; local imports: —
- `CognitiveAccretionDiskSelfReferential` — `proofs/CognitiveAccretionDiskSelfReferential.lean`; local imports: —
- `ColorConfinementGNS` — `proofs/ColorConfinementGNS.lean`; local imports: `S3ColorSpinorDecomposition`, `JaynesLDDPGNSColimit`, `SU3LoopBraidDuality`
- `ComplexStarCuntzRedesign` — `proofs/ComplexStarCuntzRedesign.lean`; local imports: `CStarCuntzTensorQuotient`
- `CStarCuntzTensorQuotient` — `proofs/CStarCuntzTensorQuotient.lean`; local imports: `AlgebraicCuntzQuotient`
- `CuntzBoundarySolderRealization` — `proofs/CuntzBoundarySolderRealization.lean`; local imports: `ParafermionIdentityRealization`, `CantorBoundaryCuntzFamily`, `WeylSolderedParafermionSymmetry`
- `CuntzDeformedSuperPoincare` — `proofs/CuntzDeformedSuperPoincare.lean`; local imports: `SupergradedCuntzBdG`, `SuperPoincareOperatorCharges`, `LorentzBoostMinkowski`, `ChiralPoincareSouriauBridge`
- `CuntzK0TorsionRelation` — `proofs/CuntzK0TorsionRelation.lean`; local imports: —
- `CuntzKreinMinkowski` — `proofs/CuntzKreinMinkowski.lean`; local imports: —
- `CuntzKriegerFibonacciK` — `proofs/CuntzKriegerFibonacciK.lean`; local imports: —
- `CuntzKriegerKTheory` — `proofs/_deprecated/removed_from_default_2026_06_15/CuntzKriegerKTheory.lean`; local imports: —
- `CuntzKTheoryPairing` — `proofs/CuntzKTheoryPairing.lean`; local imports: `ConnesSpectralAction`, `AnomalousKMSFlow`
- `DikinOnsagerCramerRaoOperator` — `proofs/DikinOnsagerCramerRaoOperator.lean`; local imports: `PrimonFlavorCKM`, `DikinGoutevTonevBridge`, `SouriauOperatorThermodynamics`, `RescaledPhaseVolumeCanonical`
- `FiniteGNSConstruction` — `proofs/FiniteGNSConstruction.lean`; local imports: —
- `FiniteUHFBooleanTrace` — `proofs/FiniteUHFBooleanTrace.lean`; local imports: —
- `FockSpaceDerivation` — `proofs/FockSpaceDerivation.lean`; local imports: —
- `FockUHFBridge` — `proofs/FockUHFBridge.lean`; local imports: —
- `GaugeUHFLift` — `proofs/GaugeUHFLift.lean`; local imports: `UHFInductiveColimit`, `ChiralCausalCone`
- `GellMannCartan` — `proofs/GellMannCartan.lean`; local imports: —
- `GNSConstruction` — `proofs/GNSConstruction.lean`; local imports: —
- `GNSModularObservables` — `proofs/GNSModularObservables.lean`; local imports: `QCDScaleExtraction`, `FierzIdentities`, `ChiralCausalCone`
- `GNSQuotientFinite` — `proofs/GNSQuotientFinite.lean`; local imports: `FiniteGNSConstruction`
- `GoldenCCR` — `proofs/GoldenCCR.lean`; local imports: —
- `HestenesCuntzPhaseSpace` — `proofs/HestenesCuntzPhaseSpace.lean`; local imports: `HestenesCuntzSpacetimeAlgebra`
- `HestenesCuntzSpacetimeAlgebra` — `proofs/HestenesCuntzSpacetimeAlgebra.lean`; local imports: `LorentzChiralCuntzBridge`
- `inductive_colimit_uhf_group` — `proofs/inductive_colimit_uhf_group.lean`; local imports: —
- `JaynesLDDPGNSColimit` — `proofs/JaynesLDDPGNSColimit.lean`; local imports: `UHFInductiveColimit`, `RegularizationCayleyPipeline`
- `KreinCuntzShadow` — `proofs/KreinCuntzShadow.lean`; local imports: `SolovievQPNMChiralCuntz`, `FiniteMatrixElementDuality`, `FierzIdentities`, `Cl11ChiralCARBridge`
- `MirrorNucleiIsospinGNS` — `proofs/MirrorNucleiIsospinGNS.lean`; local imports: `Q8NuclearChirality`, `HillWheelerProjection`
- `NonHermitianKitaevCuntzChain` — `proofs/NonHermitianKitaevCuntzChain.lean`; local imports: —
- `PenroseCuntzKriegerHolography` — `proofs/PenroseCuntzKriegerHolography.lean`; local imports: —
- `PoissonGaussianGNSColimit` — `proofs/PoissonGaussianGNSColimit.lean`; local imports: —
- `PolynomialSymmetryOperators` — `proofs/PolynomialSymmetryOperators.lean`; local imports: —
- `ProjectiveCuntzToeplitzCARCCR` — `proofs/ProjectiveCuntzToeplitzCARCCR.lean`; local imports: —
- `QDeformedSuperCuntz` — `proofs/QDeformedSuperCuntz.lean`; local imports: —
- `QRootOfUnityTruncation` — `proofs/QRootOfUnityTruncation.lean`; local imports: —
- `QSuperCuntzRegularization` — `proofs/QSuperCuntzRegularization.lean`; local imports: `SpectralSquashCayleyDKT`
- `QSuperRegularizationRosetta` — `proofs/QSuperRegularizationRosetta.lean`; local imports: `QSuperCuntzRegularization`, `RegularizationCayleyPipeline`
- `SouriauOperatorThermodynamics` — `proofs/SouriauOperatorThermodynamics.lean`; local imports: —
- `SquashingOperator` — `proofs/SquashingOperator.lean`; local imports: —
- `SuperCuntzGrading` — `proofs/SuperCuntzGrading.lean`; local imports: `ChiralCuntzInductive`
- `SupergradedCuntzBdG` — `proofs/SupergradedCuntzBdG.lean`; local imports: `ComplexStarCuntzRedesign`
- `SuperPoincareOperatorCharges` — `proofs/SuperPoincareOperatorCharges.lean`; local imports: —
- `SymbolicFockLane` — `proofs/SymbolicFockLane.lean`; local imports: —
- `SymbolicLaneUHFBridge` — `proofs/SymbolicLaneUHFBridge.lean`; local imports: —
- `uhf_cantor_boundary` — `proofs/uhf_cantor_boundary.lean`; local imports: —
- `uhf_ladder` — `proofs/uhf_ladder.lean`; local imports: —
- `UHFInductiveColimit` — `proofs/UHFInductiveColimit.lean`; local imports: —
- `UnifiedKleinHolographicArchitecture` — `proofs/UnifiedKleinHolographicArchitecture.lean`; local imports: —

### Spacetime / phase / Bogoliubov (37)

- `BogoliubovFrameTransport` — `proofs/BogoliubovFrameTransport.lean`; local imports: `KANTraceSectorization`
- `BogoliubovWeylChemicalPotential` — `proofs/BogoliubovWeylChemicalPotential.lean`; local imports: `HestenesCuntzPhaseSpace`
- `CubicJordanPeirceDecomposition` — `proofs/CubicJordanPeirceDecomposition.lean`; local imports: —
- `DiracColimit` — `proofs/DiracColimit.lean`; local imports: —
- `DiracFourierMellin` — `proofs/DiracFourierMellin.lean`; local imports: —
- `DiracKreinMetriplectic` — `proofs/DiracKreinMetriplectic.lean`; local imports: —
- `DiracResolventZeroModeTripotent` — `proofs/DiracResolventZeroModeTripotent.lean`; local imports: —
- `DiracZeroModes` — `proofs/_deprecated/removed_from_default_2026_06_15/DiracZeroModes.lean`; local imports: —
- `EmergentSpacetimeAnsatz` — `proofs/EmergentSpacetimeAnsatz.lean`; local imports: —
- `FenchelSpacetime` — `proofs/FenchelSpacetime.lean`; local imports: —
- `GlideDiracSelectionRule` — `proofs/GlideDiracSelectionRule.lean`; local imports: —
- `GohbergKreinIndex` — `proofs/GohbergKreinIndex.lean`; local imports: —
- `GravitySoldering` — `proofs/GravitySoldering.lean`; local imports: `CartanWeylBogoliubovGravity`
- `JordanBlock2` — `proofs/JordanBlock2.lean`; local imports: —
- `KanCayley` — `proofs/KanCayley.lean`; local imports: —
- `KANFourierMellinDirac` — `proofs/KANFourierMellinDirac.lean`; local imports: —
- `KasparovKreinCategory` — `proofs/KasparovKreinCategory.lean`; local imports: `AnomalousKMSFlow`, `ConnesSpectralAction`, `CuntzKTheoryPairing`
- `KasparovKreinDoubling` — `proofs/_deprecated/removed_from_default_2026_06_15/KasparovKreinDoubling.lean`; local imports: —
- `KreinDeterminantAnalyticity` — `proofs/KreinDeterminantAnalyticity.lean`; local imports: —
- `KreinMoorePenrose` — `proofs/KreinMoorePenrose.lean`; local imports: —
- `KreinVacuumKMSBridge` — `proofs/KreinVacuumKMSBridge.lean`; local imports: `KreinVacuumPropagator`, `AnomalousKMSFlow`
- `KreinVacuumPropagator` — `proofs/KreinVacuumPropagator.lean`; local imports: `AnomalousKMSFlow`
- `LorentzBoostMinkowski` — `proofs/LorentzBoostMinkowski.lean`; local imports: —
- `MinkowskiBiquaternion` — `proofs/MinkowskiBiquaternion.lean`; local imports: —
- `PhaseTransition_SUSY` — `proofs/PhaseTransition_SUSY.lean`; local imports: —
- `RegularizationCayleyPipeline` — `proofs/RegularizationCayleyPipeline.lean`; local imports: —
- `RescaledPhaseVolumeCanonical` — `proofs/RescaledPhaseVolumeCanonical.lean`; local imports: `BogoliubovWeylChemicalPotential`, `InformationGeometricCutoff`, `AffineDynkinGoutevTonev`
- `SolderingSpinConnectionBogoliubov` — `proofs/SolderingSpinConnectionBogoliubov.lean`; local imports: —
- `SpacetimeGUEIsomorphism` — `proofs/SpacetimeGUEIsomorphism.lean`; local imports: —
- `SpacetimeIsSpin` — `proofs/SpacetimeIsSpin.lean`; local imports: —
- `SpectralSquashCayleyDKT` — `proofs/SpectralSquashCayleyDKT.lean`; local imports: —
- `SplitOctonionMinkowski` — `proofs/SplitOctonionMinkowski.lean`; local imports: —
- `TKKClosureErlangenGeometry` — `proofs/TKKClosureErlangenGeometry.lean`; local imports: —
- `TKKCompileSocket` — `proofs/TKKCompileSocket.lean`; local imports: —
- `TKKJordanPairSocket` — `proofs/TKKJordanPairSocket.lean`; local imports: `SpectralSquashCayleyDKT`
- `WeylColimitCanonicalLimit` — `proofs/WeylColimitCanonicalLimit.lean`; local imports: `WeylGaugeColimitWeld`, `RescaledPhaseVolumeCanonical`
- `WeylSolderedParafermionSymmetry` — `proofs/WeylSolderedParafermionSymmetry.lean`; local imports: `GellMannParafermionSolder`, `WeylSU3ColorSymmetry`

### Spectral / index / anomaly (11)

- `AnomalousKMSFlow` — `proofs/AnomalousKMSFlow.lean`; local imports: `tomita_kms_v4`
- `ConnesSpectralAction` — `proofs/ConnesSpectralAction.lean`; local imports: `AnomalousKMSFlow`
- `FiniteProjectorSpectralCalculus` — `proofs/FiniteProjectorSpectralCalculus.lean`; local imports: —
- `FredholmModularRegularization` — `proofs/FredholmModularRegularization.lean`; local imports: —
- `FredholmRegularization` — `proofs/FredholmRegularization.lean`; local imports: —
- `GoldenSpectralTriple` — `proofs/GoldenSpectralTriple.lean`; local imports: —
- `KleinFourAnomalyCancellation` — `proofs/KleinFourAnomalyCancellation.lean`; local imports: —
- `PenroseKMSSpectralDimension` — `proofs/PenroseKMSSpectralDimension.lean`; local imports: —
- `SpectralCPTKleinBottle` — `proofs/SpectralCPTKleinBottle.lean`; local imports: `MobiusCantorTKKClosure`, `TopologicalColorCrystalFormal`, `HillWheelerUniversalProjection`
- `tomita_kms_v4` — `proofs/tomita_kms_v4.lean`; local imports: —
- `UnifiedAnomalyArchitecture` — `proofs/UnifiedAnomalyArchitecture.lean`; local imports: `AnomalousKMSFlow`, `CuntzKTheoryPairing`, `ZetaCoordinateSymmetry`, `PrimonSuperThermodynamics`, `ConnesSpectralAction`

### Tooling / graph extraction (5)

- `ASTExtractor` — `proofs/ASTExtractor.lean`; local imports: `ExtractBraid`
- `DumpLeanGraph` — `proofs/tools/lean_graph/DumpLeanGraph.lean`; local imports: —
- `ExtractBraid` — `proofs/ExtractBraid.lean`; local imports: —
- `ExtractGraph` — `proofs/tools/ExtractGraph.lean`; local imports: `ChiralCausalCone`, `ChiralTensorRecoupling`, `TLChain`, `JonesBraidB3`, `YangBaxterQSwap`, `B3PresentedGroup`, `YangBaxterQuotientDescent`, `BraidIdealDescent`, `ChiralTensorMatrixBridge`, `ChiralTLDescent`, `ChiralB3PresentedBridge`, `AlgebraicCuntzQuotient`, `CStarCuntzTensorQuotient`, `ComplexStarCuntzRedesign`, `SupergradedCuntzBdG`, `HestenesCuntzSpacetimeAlgebra`, `HestenesCuntzPhaseSpace`, `BogoliubovWeylChemicalPotential`, `RelativeModularStateDikin`, `RescaledPhaseVolumeCanonical`, `GaugeUHFLift`, `WeylGaugeColimitWeld`, `WeylColimitCanonicalLimit`, `BogoliubovSU3ParafermionWeld`, `BogoliubovSU3ParafermionProofChain`, `WeylSU3ColorSymmetry`, `GellMannParafermionSolder`, `ParafermionIdentityRealization`, `CantorBoundaryCuntzFamily`, `WeylSolderedParafermionSymmetry`, `CuntzBoundarySolderRealization`, `GellMannParafermionRealizationRoutesSynthesis`, `BogoliubovBraidGraphWeld`, `SplitCliffordAlgebras`, `AtomicCliffordKAN`, `BiquaternionCliffordIso`, `BiquaternionExpClosure`, `BiquaternionKANnilpotent`, `BiquaternionLaplaceTripotent`, `TrifactorGeometry`, `TripotentCliffordColimit`, `ZornParavectorNullspace`, `ZornScalingFlow`, `SouriauMoebiusCoupling`, `SouriauBiquaternionGaussian`, `SouriauHestenesKrein`, `ExceptionalBraidTopology`, `ExceptionalPointCollapse`, `MobiusWittenIndex`, `OctonionMatrixEncodings`, `SplitOctonionBraidSU3`, `SplitOctonionMinkowski`, `Clifford55AnomalyOSP`, `MinkowskiBiquaternion`, `PolynomialSymmetryOperators`, `BraidCliffordIntegration`, `ColorCARStandardModel`, `FureyCharges`, `KreinMoorePenrose`, `GoutevTonevPrinciple`, `DikinGoutevTonevBridge`, `AffineDynkinGoutevTonev`, `GellMannCartan`, `GellMannSU3`, `WeakIsospinSU2`, `FierzIdentities`, `SpectralSquashCayleyDKT`, `QSuperCuntzRegularization`, `QRootOfUnityTruncation`, `QuadraticConfiguration3`, `NonIsoConf3OrlikSolomon`, `NonIsoConf3DeRhamCooperad`, `NonIsoConf3QuadricD4EPolynomial`, `GrothendieckGromovWittenYangBaxter`, `PenroseSpinTilingConfig`, `PenroseSpinIncidenceTessellation`, `KleinErlangenGrothendieckBridge`, `MotivicHolographyGroebnerLFunction`, `AmariChentsovFierzTorsion`, `TKKJordanPairSocket`, `GNSQuotientFinite`, `FiniteMatrixElementDuality`, `KreinCuntzShadow`, `EuclideanNilpotentObstruction`, `ZornChiralBridge`, `ArithmeticHamiltonianZeta`, `PrimonSuperThermodynamics`, `RiemannHypothesis`, `MajoranaPrimonSpectralBridge`, `PrimonHilbertPolyaSeparation`, `IJIRTRiemannDigest`, `MisraPrimeEntropyDigest`, `PrimonBosonFermionDuality`, `PrimonCoarseGraining`, `PrimonCoarseGrainedHilbertPolyaPotential`, `JaynesLDDPGNSColimit`, `JaynesLeanColimitBridge`, `ContinuumAsColimitCounting`, `CurryHowardLambekColimit`, `ProjectiveAffineConformalClosure55`, `TwistorParafermionBoundary`, `CP3CantorGeometricObstruction`, `HillWheelerProjection`, `HillWheelerUniversalProjection`, `SU3LoopBraidCuntzBoundary`, `SU3LoopBraidDuality`, `HolographicGaugeSymmetryUniqueness`, `GravitationalQuantumBraidDuality`, `SUNQuantumBraidDuality`, `TopologicalColorCrystalFormal`, `SolovievQPNMChiralCuntz`, `UnorientedS3KleinTQFT`, `SpectralCPTKleinBottle`
- `RunExtractor` — `proofs/RunExtractor.lean`; local imports: `ExtractBraid`, `FibAnyonThm7_hexagon`, `rigorous_proofs`, `KleinBottle`
