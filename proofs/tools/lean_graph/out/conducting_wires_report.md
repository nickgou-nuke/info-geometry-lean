# Lean Proof Graph Conducting Wires / Dangling Ends

Source: `proofs/proof_graph.json` after `lake build` + `lake env lean tools/ExtractGraph.lean`.

Interpretation of edge direction: `A -> B` means declaration `A` depends on declaration `B`.

- **Conducting wire declaration**: used by downstream declarations and also depends on upstream declarations; scored by `sqrt(used_by * depends_on)`.
- **Most-referenced atom**: high fan-in (`used_by`), often foundational current bus.
- **Dangling unused end**: zero incoming references in the extracted graph (`used_by = 0`) but nonzero dependencies; often capstone/socket theorem not yet wired downstream.
- **Foundational sink/root**: zero dependencies but high fan-in; base carrier/constant used throughout.

## Top declaration conductors

| score | used_by | deps | kind | declaration |
|---:|---:|---:|---|---|
| 26.65 | 142 | 5 | def | `AlgebraicCuntzQuotient.instSemiringCuntzAlg` |
| 25.50 | 130 | 5 | def | `AlgebraicCuntzQuotient.instAlgebraCuntzAlg` |
| 24.49 | 150 | 4 | def | `AlgebraicCuntzQuotient.CuntzAlg` |
| 22.80 | 52 | 10 | inductive | `TrainsumQuanticsTensorTrainsDigest.TrainSumFeature` |
| 22.80 | 52 | 10 | inductive | `QuaternionQuanticsBackendDigest.TrainSumFeature` |
| 21.91 | 48 | 10 | theorem | `ComplexStarCuntzRedesign.realCuntzStarModule` |
| 21.00 | 49 | 9 | inductive | `QuaternionQuanticsBackendDigest.QuatIcaFeature` |
| 20.49 | 70 | 6 | inductive | `NonIsoConf3DeRhamCooperad.OSAlphaBasis` |
| 19.90 | 44 | 9 | def | `AlgebraicCuntzQuotient.T` |
| 19.90 | 44 | 9 | def | `AlgebraicCuntzQuotient.S` |
| 19.75 | 78 | 5 | inductive | `TKKJordanPairSocket.TKKGrade` |
| 18.33 | 56 | 6 | inductive | `BraidedCocycleWilsonEntropy.OrientedEdge3` |
| 18.00 | 81 | 4 | inductive | `TopologicalAndreevPump.ParafermionLane` |
| 17.44 | 19 | 16 | def | `InfiniteLightConeConfColimit.arity3Stage` |
| 16.97 | 48 | 6 | def | `AlgebraicCuntzQuotient.instStarRing` |

## Most referenced foundational buses

| used_by | deps | kind | declaration |
|---:|---:|---|---|
| 279 | 0 | def | `ChiralCausalCone.M2C` |
| 171 | 1 | inductive | `TKKJordanPairSocket.FiveGradedLieAlgebra` |
| 160 | 1 | inductive | `ChemicalPotentialDeRhamG0Bridge.AbstractDeRhamComplex` |
| 150 | 4 | def | `AlgebraicCuntzQuotient.CuntzAlg` |
| 142 | 5 | def | `AlgebraicCuntzQuotient.instSemiringCuntzAlg` |
| 130 | 5 | def | `AlgebraicCuntzQuotient.instAlgebraCuntzAlg` |
| 120 | 1 | inductive | `BogoliubovWeylChemicalPotential.BogoliubovInertialFrame` |
| 106 | 2 | inductive | `SupergradedCuntzBdG.Z2Parity` |
| 94 | 2 | inductive | `AlgebraicCuntzQuotient.CuntzLetter` |
| 93 | 0 | def | `BogoliubovSU3ParafermionProofChain.ColorSpinor4` |
| 85 | 2 | inductive | `NonIsoConf3DeRhamCooperad.ModelChoice` |
| 81 | 4 | inductive | `TopologicalAndreevPump.ParafermionLane` |
| 81 | 0 | def | `SupergradedCuntzBdG.qRapidity` |
| 78 | 5 | inductive | `TKKJordanPairSocket.TKKGrade` |
| 75 | 1 | inductive | `CStarCuntzTensorQuotient.CStarCuntzFamily` |

## Top module conductors

| score | incoming | outgoing | decls | module |
|---:|---:|---:|---:|---|
| 155.19 | 108 | 223 | 232 | `SupergradedCuntzBdG` |
| 142.04 | 131 | 154 | 34 | `BogoliubovSU3ParafermionProofChain` |
| 111.74 | 227 | 55 | 189 | `NonIsoConf3DeRhamCooperad` |
| 95.58 | 45 | 203 | 68 | `ModularRadonNikodymJacobianBridge` |
| 94.36 | 212 | 42 | 26 | `BogoliubovWeylChemicalPotential` |
| 86.45 | 101 | 74 | 106 | `ChemicalPotentialDeRhamG0Bridge` |
| 83.71 | 49 | 143 | 26 | `ComplexStarCuntzRedesign` |
| 82.31 | 271 | 25 | 89 | `TKKJordanPairSocket` |
| 72.33 | 48 | 109 | 46 | `ChiralTensorRecoupling` |
| 61.48 | 45 | 84 | 32 | `ParafermionIdentityRealization` |
| 59.60 | 32 | 111 | 22 | `ChemicalPotentialTKKGradeZero` |
| 58.38 | 48 | 71 | 21 | `GellMannParafermionSolder` |
| 54.04 | 146 | 20 | 94 | `LightConeConf3DeRhamCooperad` |
| 52.99 | 36 | 78 | 35 | `ColorCARStandardModel` |
| 51.44 | 21 | 126 | 34 | `BogoliubovSU3ParafermionWeld` |

## Thick intermodule wires

| edges | from | to |
|---:|---|---|
| 174 | `SupergradedCuntzBdG` | `AlgebraicCuntzQuotient` |
| 112 | `ComplexStarCuntzRedesign` | `AlgebraicCuntzQuotient` |
| 109 | `ChiralTensorRecoupling` | `ChiralCausalCone` |
| 100 | `ModularRadonNikodymJacobianBridge` | `TKKJordanPairSocket` |
| 90 | `BogoliubovSU3ParafermionProofChain` | `GellMannSU3` |
| 78 | `ChemicalPotentialTKKGradeZero` | `TKKJordanPairSocket` |
| 69 | `ColorCARStandardModel` | `ChiralCausalCone` |
| 60 | `CStarCuntzTensorQuotient` | `AlgebraicCuntzQuotient` |
| 56 | `ModularRadonNikodymJacobianBridge` | `ChemicalPotentialDeRhamG0Bridge` |
| 55 | `NonIsoConf3DeRhamCooperad` | `QuadraticConfiguration3` |
| 53 | `LogCFTPotentialBranchChoice` | `NonIsoConf3DeRhamCooperad` |
| 49 | `ChemicalPotentialDeRhamG0Bridge` | `NonIsoConf3DeRhamCooperad` |
| 49 | `SupergradedCuntzBdG` | `ComplexStarCuntzRedesign` |
| 47 | `CooperadEnvironmentalRank32` | `LightConeConf3DeRhamCooperad` |
| 43 | `BogoliubovSU3ParafermionWeld` | `BogoliubovWeylChemicalPotential` |

## Highest-value dangling unused ends

These have `used_by = 0` in the extracted declaration graph and many dependencies. Many are intentional capstones/sockets; they are the best targets if we want to wire new synthesis nodes downstream.

| deps | kind | declaration |
|---:|---|---|
| 60 | theorem | `GellMannParafermionRealizationRoutesSynthesis.gellmann_parafermion_realization_routes_synthesis` |
| 58 | theorem | `ModularRadonNikodymJacobianBridge.de_rham_alpha_beta_forbidden_cone_clock_synthesis` |
| 56 | theorem | `PenroseQuadricTopologySynthesis.penrose_quadric_topological_compilation` |
| 56 | theorem | `ModularRadonNikodymJacobianBridge.modular_rn_jacobian_chemical_derham_tkk_synthesis` |
| 53 | theorem | `TopologicalColorCrystalFormal.topological_color_crystal_formal_synthesis` |
| 52 | theorem | `EntropicChiralDeRhamDictionary.entropic_chiral_deRham_dictionary_synthesis` |
| 49 | theorem | `CurryHowardLambekColimit.curry_howard_lambek_colimit_synthesis` |
| 49 | theorem | `ChemicalPotentialDeRhamG0Bridge.chemical_potential_derham_g0_synthesis` |
| 48 | theorem | `SuperconductingHolographicResonator.superconducting_holographic_resonator_synthesis` |
| 48 | theorem | `HolographicGaugeSymmetryUniqueness.holographic_gauge_symmetry_uniqueness_synthesis` |
| 46 | theorem | `ThermodynamicTKKBridge.thermodynamic_tkk_bridge_synthesis` |
| 45 | theorem | `BogoliubovSU3ParafermionWeld.bogoliubov_su3_parafermion_synthesis` |
| 43 | theorem | `TopologicalAndreevPump.topological_andreev_pump_synthesis` |
| 43 | theorem | `FinalSpectroscopicSynthesisAudit.final_spectroscopic_synthesis_audit` |
| 40 | theorem | `ConformalScaleRecurrence.conformal_scale_recurrence_synthesis` |
| 39 | theorem | `Mirror31PSLnQFlowToy.mirror31_ps_lnq_flow_toy_synthesis` |
| 39 | theorem | `CuntzBoundarySolderRealization.cuntz_boundary_solder_realization_synthesis` |
| 38 | theorem | `StimulatedScatteringAmplituhedron.stimulated_scattering_amplituhedron_synthesis` |
| 38 | theorem | `MetamaterialQuasicrystalBloch.metamaterial_quasicrystal_bloch_synthesis` |
| 37 | theorem | `TwistedTorusVacuumMachine.twisted_torus_vacuum_machine_synthesis` |
| 37 | theorem | `TopologicalMetasurfaceSupercurrent.topological_metasurface_supercurrent_synthesis` |
| 36 | theorem | `BuresFisherAndreevGeodesicFlow.bures_fisher_andreev_geodesic_flow_synthesis` |
| 34 | theorem | `Clifford55AnomalyOSP.clifford_55_anomaly_osp_synthesis` |
| 32 | theorem | `KasparovKreinKleinO55Kernel.kasparov_krein_klein_o55_kernel_synthesis` |
| 30 | theorem | `NonAbelianBrillouinKleinBottle.nonabelian_brillouin_klein_bottle_synthesis` |

## Module-level dangling outer tips

Modules with no incoming intermodule references but nonzero outgoing references.

| outgoing | decls | module |
|---:|---:|---|
| 160 | 12 | `GellMannParafermionRealizationRoutesSynthesis` |
| 95 | 91 | `EntropicChiralDeRhamDictionary` |
| 94 | 21 | `WeylColimitCanonicalLimit` |
| 80 | 22 | `ChiralB3PresentedBridge` |
| 70 | 62 | `PenroseQuadricTopologySynthesis` |
| 41 | 29 | `GravitationalQuantumBraidDuality` |
| 37 | 18 | `NonIsoConf3LogCFTLiteratureBridge` |
| 36 | 45 | `KreinCuntzShadow` |
| 33 | 41 | `SuperconductingHolographicResonator` |
| 29 | 17 | `EntropicChiralDeRhamFormalization` |
| 27 | 68 | `TopologicalColorCrystalFormal` |
| 27 | 31 | `FinalSpectroscopicSynthesisAudit` |
| 25 | 55 | `KasparovKreinKleinO55Kernel` |

## Module-level foundational sinks

Modules with incoming intermodule references but no outgoing intermodule references.

| incoming | decls | module |
|---:|---:|---|
| 444 | 63 | `AlgebraicCuntzQuotient` |
| 219 | 24 | `GellMannSU3` |
| 65 | 73 | `HestenesCuntzPhaseSpace` |
| 62 | 182 | `QuadraticConfiguration3` |
| 52 | 51 | `O55GradedGeneratorBasis` |
| 45 | 35 | `SpectralSquashCayleyDKT` |
| 42 | 29 | `BraidIdealDescent` |
| 34 | 134 | `JaynesLDDPGNSColimit` |
| 25 | 43 | `FiniteMatrixElementDuality` |
| 22 | 76 | `NonIsoConf3QuadricD4Model` |

## Immediate wiring opportunities

1. Add a closed synthesis/capstone theorem that references several current dangling capstones, without asserting new analytic content.
2. If the goal is graph conductivity, downstream modules should depend on existing capstones such as:
   - `ThermodynamicTKKBridge.thermodynamic_tkk_bridge_synthesis`
   - `SuperconductingHolographicResonator.superconducting_holographic_resonator_synthesis`
   - `NonAbelianBrillouinKleinBottle.nonabelian_brillouin_klein_bottle_synthesis`
   - `KasparovKreinKleinO55Kernel.kasparov_krein_klein_o55_kernel_synthesis`
3. Avoid creating new isolated capstones unless they are explicitly wired into the theorem spine.
