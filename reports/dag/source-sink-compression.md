# Source-Sink Compression Report

Model:
- atomic graph: declaration-to-declaration DAG under `artifacts/dag/full_graph.json`
- native structure: condensed SCC topology, dominator summaries, and canonical root witness paths under `artifacts/dag/structural-topology.json`
- incidence layer: source bundles -> sink theorems grouped by canonical atomic support paths and enriched with native component corridors
- bundle ids are content-stable hashes of sorted bundle members, not rank-based labels
- hydrated projection: module-level carriers enriched with source bundles, sink families, motifs, and compression potential

Flow orientation:
- this report reverses the declaration dependency arrows into generative flow: constructive sources -> downstream sinks

## Hotspot Modules
- `#1 InfoGeometry.Canonical.BulkBoundaryRegularizationBridge` score=306.399 mix=0/26/3
- `#2 InfoGeometry.Canonical.UnifiedSuperchargeAlgebra` score=268.505 mix=0/31/0
- `#3 InfoGeometry.Canonical.ConformalProjectorCore` score=260.609 mix=0/24/0
- `#4 InfoGeometry.Canonical.ModularSuperchargeClosure` score=241.159 mix=8/19/2
- `#5 InfoGeometry.Quantum.RealMajoranaCategory` score=184.676 mix=0/18/0
- `#6 InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge` score=167.706 mix=5/16/0
- `#7 InfoGeometry.Canonical.RealBdGDIIIAtom` score=144.608 mix=0/15/0
- `#8 InfoGeometry.Canonical.LogDetRadonNikodymMechanism` score=131.461 mix=0/15/0

## Canonical Sources
- `InfoGeometry.Krein.instL2Complete` score=103.767 reachable_sinks=15 closest_distance=1
- `InfoGeometry.Krein.DoubledSpace.ext` score=40.851 reachable_sinks=8 closest_distance=3
- `InfoGeometry.Krein.spectral_epsilon_involution` score=13.996 reachable_sinks=5 closest_distance=2
- `InfoGeometry.Krein.modular_j_involution` score=12.558 reachable_sinks=5 closest_distance=2
- `InfoGeometry.Krein.complex_i_sq` score=12.477 reachable_sinks=6 closest_distance=3
- `InfoGeometry.Quantum.RealSplitCl11Action.eps_sq_apply` score=11.964 reachable_sinks=5 closest_distance=7
- `InfoGeometry.Cartan.Pplus_add_Pminus_eq_id` score=11.538 reachable_sinks=5 closest_distance=7
- `InfoGeometry.Quantum.BulkBoundary.EndS` score=9.698 reachable_sinks=2 closest_distance=2
- `InfoGeometry.Krein.modular_j_spectral_epsilon_anticommute` score=9.675 reachable_sinks=4 closest_distance=2
- `InfoGeometry.Canonical.KKTCore.minusProjector_mul_plusProjector` score=9.622 reachable_sinks=5 closest_distance=6

## Selected Sinks
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch` category=`package_reprojection` hotspot_rank=1 flow_out_degree=0
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.moorePenroseLeftProjector_ne_one_of_hasZeroMode` category=`surrogate_or_vacuous` hotspot_rank=1 flow_out_degree=1
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.drazinProjection_ne_one_of_hasZeroMode` category=`surrogate_or_vacuous` hotspot_rank=1 flow_out_degree=1
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.moorePenroseRightProjector_ne_one_of_hasZeroMode` category=`surrogate_or_vacuous` hotspot_rank=1 flow_out_degree=1
- `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.unified_internal_split_with_operatorial_shadow` category=`package_reprojection` hotspot_rank=2 flow_out_degree=0
- `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.TopologicalCentralChargePackage.Zop_eq_analyticIndex` category=`package_reprojection` hotspot_rank=2 flow_out_degree=0
- `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace` category=`package_reprojection` hotspot_rank=2 flow_out_degree=0
- `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.instIsScalarTowerRealContinuousLinearMapIdDoubledSpace` category=`package_reprojection` hotspot_rank=2 flow_out_degree=0
- `InfoGeometry.Canonical.ModularSuperchargeClosure.cp003_singular_surrogate_commutator_closure` category=`surrogate_or_vacuous` hotspot_rank=4 flow_out_degree=0
- `InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalSeedFlowEqUnruhTarget_iff_superHamiltonian_eq_two_pi_modularSign` category=`package_reprojection` hotspot_rank=4 flow_out_degree=0
- `InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData_deltaLog` category=`package_reprojection` hotspot_rank=4 flow_out_degree=0
- `InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalSeedFlow_eq_internalUnruhFlowOfModularTime` category=`hypothesis_bridge` hotspot_rank=4 flow_out_degree=0

## Top Source Bundles

| Rank | Bundle | Sources | Sinks | Avg path | Compression | Motif |
| --- | --- | --- | ---: | ---: | ---: | --- |
| 1 | `bundle:e1ff0eb12e61` | `instL2Complete`, `doubledCarrier`, `complex_i_sq` | 2 | 7.000 | 28.000 | `instL2Complete -> doubledCarrier -> complex_i_sq -> complex_iSupercharge_hamiltonian -> modularCPTSupercharge_hamiltonian -> cptSuperchargeOp_sq -> canonicalDIIIProxy -> canonicalDIIIProxy_C_eq_modular_j` |
| 2 | `bundle:abbbb4a36d13` | `instL2Complete` | 12 | 1.000 | 25.000 | `instL2Complete -> unified_internal_split_with_operatorial_shadow` |
| 3 | `bundle:2cbafe241189` | `EndS`, `HasZeroMode` | 2 | 2.000 | 16.000 | `EndS -> HasZeroMode -> drazinProjection_ne_one_of_hasZeroMode` |
| 4 | `bundle:6081ce64e87a` | `instL2Complete`, `doubledCarrier`, `complex_i_sq` | 1 | 5.000 | 10.000 | `instL2Complete -> doubledCarrier -> complex_i_sq -> modularK_sq -> topologicalClassDIII_of_realBdGDatum -> canonicalDIIIProxy_topologicalClassDIII_of_realBdGDatum` |
| 5 | `bundle:f52e155db8bd` | `exists_zeroMode_of_hasZeroMode`, `exists_zeroMode_of_dim_mismatch` | 1 | 3.000 | 6.000 | `exists_zeroMode_of_hasZeroMode -> exists_zeroMode_of_dim_mismatch -> zeroModeRegularizationPackage_of_dim_mismatch -> exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch` |
| 6 | `bundle:343810c8cb03` | `exists_zeroMode_of_hasZeroMode` | 1 | 1.000 | 4.000 | `exists_zeroMode_of_hasZeroMode -> moorePenroseLeftProjector_ne_one_of_hasZeroMode` |
| 7 | `bundle:75b746d0432c` | `DoubledSpace` | 1 | 1.000 | 2.000 | `DoubledSpace -> instIsScalarTowerRealContinuousLinearMapIdDoubledSpace` |

## Repeated Path Motifs

| Rank | Motif signature | Paths | Avg path | Compression |
| --- | --- | ---: | ---: | ---: |
| 1 | `instL2Complete -> doubledCarrier -> complex_i_sq -> complex_iSupercharge_hamiltonian -> modularCPTSupercharge_hamiltonian -> cptSuperchargeOp_sq -> canonicalDIIIProxy -> canonicalDIIIProxy_C_eq_modular_j` | 1 | 7.000 | 14.000 |
| 2 | `instL2Complete -> doubledCarrier -> complex_i_sq -> complex_iSupercharge_hamiltonian -> modularCPTSupercharge_hamiltonian -> cptSuperchargeOp_sq -> canonicalDIIIProxy -> canonicalDIIIProxy_laws` | 1 | 7.000 | 14.000 |
| 3 | `instL2Complete -> doubledCarrier -> complex_i_sq -> modularK_sq -> topologicalClassDIII_of_realBdGDatum -> canonicalDIIIProxy_topologicalClassDIII_of_realBdGDatum` | 1 | 5.000 | 10.000 |
| 4 | `EndS -> HasZeroMode -> drazinProjection_ne_one_of_hasZeroMode` | 1 | 2.000 | 8.000 |
| 5 | `EndS -> HasZeroMode -> moorePenroseRightProjector_ne_one_of_hasZeroMode` | 1 | 2.000 | 8.000 |
| 6 | `exists_zeroMode_of_hasZeroMode -> exists_zeroMode_of_dim_mismatch -> zeroModeRegularizationPackage_of_dim_mismatch -> exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch` | 1 | 3.000 | 6.000 |
| 7 | `exists_zeroMode_of_hasZeroMode -> moorePenroseLeftProjector_ne_one_of_hasZeroMode` | 1 | 1.000 | 4.000 |
| 8 | `instL2Complete -> cp003_singular_surrogate_commutator_closure` | 1 | 1.000 | 4.000 |
| 9 | `DoubledSpace -> instIsScalarTowerRealContinuousLinearMapIdDoubledSpace` | 1 | 1.000 | 2.000 |
| 10 | `instL2Complete -> Zop_eq_analyticIndex` | 1 | 1.000 | 2.000 |
| 11 | `instL2Complete -> canonicalDIIIProxy_transport_root_parity_boundary_kkt_headSuperBracket_closure` | 1 | 1.000 | 2.000 |
| 12 | `instL2Complete -> canonicalSeedFlowEqUnruhTarget_iff_superHamiltonian_eq_two_pi_modularSign` | 1 | 1.000 | 2.000 |

## Hydrated Module Projection

| Rank | Module | Role | Paths | Compression | Dom pressure | Corridor reuse | Top root witness |
| --- | --- | --- | ---: | ---: | ---: | ---: | --- |
| 1 | `InfoGeometry.Krein.KreinSpace` | `constructive_source` | 15 | 63.000 | 0 | 26 | `InfoGeometry.Krein.instL2Complete` |
| 2 | `InfoGeometry.Canonical.RealBdGDIIIAtom` | `consumer_sink` | 4 | 40.000 | 1 | 15 | `InfoGeometry.Krein.InvolutiveSelfDualCarrier` |
| 3 | `InfoGeometry.Krein.DoubledSpace` | `constructive_source` | 4 | 40.000 | 0 | 15 | `InfoGeometry.Krein.DoubledSpace` |
| 4 | `InfoGeometry.Canonical.TomitaTakesaki` | `constructive_source` | 2 | 28.000 | 1 | 10 | `InfoGeometry.Krein.InvolutiveSelfDualCarrier` |
| 5 | `InfoGeometry.Krein.Superphysics` | `constructive_source` | 2 | 28.000 | 1 | 10 | `InfoGeometry.Krein.InvolutiveSelfDualCarrier` |
| 6 | `InfoGeometry.Canonical.SuperchargeCARCCRBridge` | `constructive_source` | 2 | 28.000 | 0 | 10 | `InfoGeometry.Krein.InvolutiveSelfDualCarrier` |
| 7 | `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge` | `consumer_sink` | 4 | 26.000 | 0 | 4 | `InfoGeometry.Canonical.Drazin.IsDrazinInverse` |
| 8 | `InfoGeometry.Quantum.BulkBoundary` | `constructive_source` | 4 | 26.000 | 0 | 4 | `InfoGeometry.Quantum.BulkBoundary.EndS` |
| 9 | `InfoGeometry.Canonical.DIIICommutatorInitialization` | `constructive_source` | 1 | 10.000 | 1 | 4 | `InfoGeometry.Krein.InvolutiveSelfDualCarrier` |
| 10 | `InfoGeometry.Canonical.RealBdG` | `constructive_source` | 1 | 10.000 | 0 | 4 | `InfoGeometry.Krein.InvolutiveSelfDualCarrier` |
| 11 | `InfoGeometry.Canonical.ModularSuperchargeClosure` | `consumer_sink` | 4 | 9.000 | 0 | 4 | `InfoGeometry.Canonical.InverseKernel` |
| 12 | `InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge` | `consumer_sink` | 4 | 8.000 | 0 | 4 | `InfoGeometry.Canonical.InverseKernel` |
| 13 | `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra` | `consumer_sink` | 4 | 8.000 | 0 | 4 | `InfoGeometry.Krein.KreinSpace` |

## Hydrated Edge Projection
- `InfoGeometry.Krein.KreinSpace -> InfoGeometry.Krein.DoubledSpace` paths=3 compression=38.000 packet=`instL2Complete -> doubledCarrier -> complex_i_sq -> modularK_sq -> topologicalClassDIII_of_realBdGDatum -> canonicalDIIIProxy_topologicalClassDIII_of_realBdGDatum`
- `InfoGeometry.Canonical.SuperchargeCARCCRBridge -> InfoGeometry.Canonical.RealBdGDIIIAtom` paths=2 compression=28.000 packet=`instL2Complete -> doubledCarrier -> complex_i_sq -> complex_iSupercharge_hamiltonian -> modularCPTSupercharge_hamiltonian -> cptSuperchargeOp_sq -> canonicalDIIIProxy -> canonicalDIIIProxy_C_eq_modular_j`
- `InfoGeometry.Canonical.TomitaTakesaki -> InfoGeometry.Canonical.SuperchargeCARCCRBridge` paths=2 compression=28.000 packet=`instL2Complete -> doubledCarrier -> complex_i_sq -> complex_iSupercharge_hamiltonian -> modularCPTSupercharge_hamiltonian -> cptSuperchargeOp_sq -> canonicalDIIIProxy -> canonicalDIIIProxy_C_eq_modular_j`
- `InfoGeometry.Krein.DoubledSpace -> InfoGeometry.Krein.Superphysics` paths=2 compression=28.000 packet=`instL2Complete -> doubledCarrier -> complex_i_sq -> complex_iSupercharge_hamiltonian -> modularCPTSupercharge_hamiltonian -> cptSuperchargeOp_sq -> canonicalDIIIProxy -> canonicalDIIIProxy_C_eq_modular_j`
- `InfoGeometry.Krein.Superphysics -> InfoGeometry.Canonical.TomitaTakesaki` paths=2 compression=28.000 packet=`instL2Complete -> doubledCarrier -> complex_i_sq -> complex_iSupercharge_hamiltonian -> modularCPTSupercharge_hamiltonian -> cptSuperchargeOp_sq -> canonicalDIIIProxy -> canonicalDIIIProxy_C_eq_modular_j`
- `InfoGeometry.Quantum.BulkBoundary -> InfoGeometry.Canonical.BulkBoundaryRegularizationBridge` paths=4 compression=26.000 packet=`exists_zeroMode_of_hasZeroMode -> exists_zeroMode_of_dim_mismatch -> zeroModeRegularizationPackage_of_dim_mismatch -> exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch`
- `InfoGeometry.Canonical.DIIICommutatorInitialization -> InfoGeometry.Canonical.RealBdGDIIIAtom` paths=1 compression=10.000 packet=`instL2Complete -> doubledCarrier -> complex_i_sq -> modularK_sq -> topologicalClassDIII_of_realBdGDatum -> canonicalDIIIProxy_topologicalClassDIII_of_realBdGDatum`
- `InfoGeometry.Canonical.RealBdG -> InfoGeometry.Canonical.DIIICommutatorInitialization` paths=1 compression=10.000 packet=`instL2Complete -> doubledCarrier -> complex_i_sq -> modularK_sq -> topologicalClassDIII_of_realBdGDatum -> canonicalDIIIProxy_topologicalClassDIII_of_realBdGDatum`
- `InfoGeometry.Krein.DoubledSpace -> InfoGeometry.Canonical.RealBdG` paths=1 compression=10.000 packet=`instL2Complete -> doubledCarrier -> complex_i_sq -> modularK_sq -> topologicalClassDIII_of_realBdGDatum -> canonicalDIIIProxy_topologicalClassDIII_of_realBdGDatum`
- `InfoGeometry.Krein.KreinSpace -> InfoGeometry.Canonical.ModularSuperchargeClosure` paths=4 compression=9.000 packet=`instL2Complete -> cp003_singular_surrogate_commutator_closure`
- `InfoGeometry.Krein.KreinSpace -> InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge` paths=4 compression=8.000 packet=`instL2Complete -> trunk_projectorObstruction_diagonal_blocks_and_holonomy_eq_projectorObstruction_nnnorm_of_flat`
- `InfoGeometry.Krein.KreinSpace -> InfoGeometry.Canonical.UnifiedSuperchargeAlgebra` paths=3 compression=6.000 packet=`instL2Complete -> unified_internal_split_with_operatorial_shadow`

