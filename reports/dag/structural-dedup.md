# Structural Dedup

This report separates true sink-surface dedup candidates from shadow transport relations so repeated packets are not confused with source-to-consumer reflections.

- structure: `/home/goutev/LEAN4/info-geometry-lean/artifacts/dag/structural-topology.json`
- bipartite artifact: `/home/goutev/LEAN4/info-geometry-lean/artifacts/dag/source-sink-bipartite.json`
- shadow threshold: `5.0`

## Summary
- sink surfaces: `20`
- hydrated carriers: `13`
- dedup families: `3`
- shadow relations: `6`
- reused assumption packets: `7`
- top dedup family score: `101.25`
- top shadow score: `10.0`

## Dedup Families
- `family:0c84ab173c89`: canonical `InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalSeedFlow_eq_internalUnruhFlowOfModularTime` | members `12` | score `101.25`
  - bundle: `bundle:abbbb4a36d13`
  - members: `InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalSeedFlowEqUnruhTarget_iff_superHamiltonian_eq_two_pi_modularSign, InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalSeedFlow_eq_internalUnruhFlowOfModularTime, InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData_deltaLog, InfoGeometry.Canonical.ModularSuperchargeClosure.cp003_singular_surrogate_commutator_closure, InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.leaf_projectorObstruction_diagonal_blocks_and_holonomy_eq_projectorObstruction_nnnorm_of_flat, InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.leaf_projectorObstruction_offDiagonal_vanish_and_holonomy_eq_projectorObstruction_nnnorm_of_flat, InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.trunk_projectorObstruction_diagonal_blocks_and_holonomy_eq_projectorObstruction_nnnorm_of_flat, InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.trunk_projectorObstruction_offDiagonal_vanish_and_holonomy_eq_projectorObstruction_nnnorm_of_flat, InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_transport_root_parity_boundary_kkt_headSuperBracket_closure, InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.TopologicalCentralChargePackage.Zop_eq_analyticIndex, InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace, InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.unified_internal_split_with_operatorial_shadow`
  - sink family: `InfoGeometry.Canonical.ModularSuperchargeClosure, InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge, InfoGeometry.Canonical.RealBdGDIIIAtom, InfoGeometry.Canonical.UnifiedSuperchargeAlgebra`
  - corridor reps: `InfoGeometry.Krein.instL2Complete`
  - motif: `instL2Complete -> unified_internal_split_with_operatorial_shadow`
- `family:e57f1e8a1b98`: canonical `InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_laws` | members `2` | score `11.4`
  - bundle: `bundle:e1ff0eb12e61`
  - members: `InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_C_eq_modular_j, InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_laws`
  - sink family: `InfoGeometry.Canonical.RealBdGDIIIAtom`
  - corridor reps: `InfoGeometry.Krein.instL2Complete, InfoGeometry.Krein.doubledCarrier, InfoGeometry.Krein.complex_i_sq, InfoGeometry.Krein.complex_iSupercharge_hamiltonian, InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge_hamiltonian, InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp_sq`
  - motif: `instL2Complete -> doubledCarrier -> complex_i_sq -> complex_iSupercharge_hamiltonian -> modularCPTSupercharge_hamiltonian -> cptSuperchargeOp_sq -> canonicalDIIIProxy -> canonicalDIIIProxy_C_eq_modular_j`
- `family:9fe2c8b6f993`: canonical `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.drazinProjection_ne_one_of_hasZeroMode` | members `2` | score `10.8`
  - bundle: `bundle:2cbafe241189`
  - members: `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.drazinProjection_ne_one_of_hasZeroMode, InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.moorePenroseRightProjector_ne_one_of_hasZeroMode`
  - sink family: `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge`
  - corridor reps: `InfoGeometry.Quantum.BulkBoundary.EndS, InfoGeometry.Quantum.BulkBoundary.HasZeroMode`
  - motif: `EndS -> HasZeroMode -> drazinProjection_ne_one_of_hasZeroMode`

## Shadow Relations
- `InfoGeometry.Quantum.BulkBoundary` -> `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge`: score `10.0` | packet `bundle:2cbafe241189`
  - roles: `constructive_source` -> `consumer_sink` | comp-j `0.0` | sink-j `1.0` | motif-j `1.0`
  - shared corridor reps: `InfoGeometry.Quantum.BulkBoundary.exists_zeroMode_of_hasZeroMode, InfoGeometry.Quantum.BulkBoundary.exists_zeroMode_of_dim_mismatch, InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.zeroModeRegularizationPackage_of_dim_mismatch, InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch`
  - why: `role mismatch constructive_source -> consumer_sink; same source bundle; same top corridor; aligned motif packet`
- `InfoGeometry.Canonical.SuperchargeCARCCRBridge` -> `InfoGeometry.Canonical.RealBdGDIIIAtom`: score `9.25` | packet `bundle:e1ff0eb12e61`
  - roles: `constructive_source` -> `consumer_sink` | comp-j `0.0` | sink-j `1.0` | motif-j `0.25`
  - shared corridor reps: `InfoGeometry.Krein.instL2Complete, InfoGeometry.Krein.doubledCarrier, InfoGeometry.Krein.complex_i_sq, InfoGeometry.Krein.complex_iSupercharge_hamiltonian, InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge_hamiltonian, InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp_sq`
  - why: `role mismatch constructive_source -> consumer_sink; same source bundle; same top corridor`
- `InfoGeometry.Canonical.TomitaTakesaki` -> `InfoGeometry.Canonical.RealBdGDIIIAtom`: score `9.25` | packet `bundle:e1ff0eb12e61`
  - roles: `constructive_source` -> `consumer_sink` | comp-j `0.0` | sink-j `1.0` | motif-j `0.25`
  - shared corridor reps: `InfoGeometry.Krein.instL2Complete, InfoGeometry.Krein.doubledCarrier, InfoGeometry.Krein.complex_i_sq, InfoGeometry.Krein.complex_iSupercharge_hamiltonian, InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge_hamiltonian, InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp_sq`
  - why: `role mismatch constructive_source -> consumer_sink; same source bundle; same top corridor`
- `InfoGeometry.Krein.Superphysics` -> `InfoGeometry.Canonical.RealBdGDIIIAtom`: score `9.25` | packet `bundle:e1ff0eb12e61`
  - roles: `constructive_source` -> `consumer_sink` | comp-j `0.0` | sink-j `1.0` | motif-j `0.25`
  - shared corridor reps: `InfoGeometry.Krein.instL2Complete, InfoGeometry.Krein.doubledCarrier, InfoGeometry.Krein.complex_i_sq, InfoGeometry.Krein.complex_iSupercharge_hamiltonian, InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge_hamiltonian, InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp_sq`
  - why: `role mismatch constructive_source -> consumer_sink; same source bundle; same top corridor`
- `InfoGeometry.Krein.DoubledSpace` -> `InfoGeometry.Canonical.RealBdGDIIIAtom`: score `8.5` | packet `bundle:e1ff0eb12e61`
  - roles: `constructive_source` -> `consumer_sink` | comp-j `0.0` | sink-j `0.5` | motif-j `0.5`
  - shared corridor reps: `InfoGeometry.Krein.instL2Complete, InfoGeometry.Krein.doubledCarrier, InfoGeometry.Krein.complex_i_sq, InfoGeometry.Krein.complex_iSupercharge_hamiltonian, InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge_hamiltonian, InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp_sq`
  - why: `role mismatch constructive_source -> consumer_sink; same source bundle; same top corridor; aligned motif packet`
- `InfoGeometry.Krein.KreinSpace` -> `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra`: score `5.5` | packet `bundle:abbbb4a36d13`
  - roles: `constructive_source` -> `consumer_sink` | comp-j `0.0` | sink-j `0.25` | motif-j `1.0`
  - shared corridor reps: `InfoGeometry.Krein.instL2Complete`
  - why: `role mismatch constructive_source -> consumer_sink; same source bundle; aligned motif packet`

## Assumption Packet Reuse
- `bundle:abbbb4a36d13`: reuse-score `64.25` | carriers `5` | sinks `12` | upstream `InfoGeometry.Krein.KreinSpace`
  - carrier modules: `InfoGeometry.Canonical.ModularSuperchargeClosure, InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge, InfoGeometry.Canonical.RealBdGDIIIAtom, InfoGeometry.Canonical.UnifiedSuperchargeAlgebra, InfoGeometry.Krein.KreinSpace`
  - motif: `instL2Complete -> unified_internal_split_with_operatorial_shadow`
- `bundle:e1ff0eb12e61`: reuse-score `35.4` | carriers `6` | sinks `2` | upstream `InfoGeometry.Krein.KreinSpace`
  - carrier modules: `InfoGeometry.Canonical.RealBdGDIIIAtom, InfoGeometry.Canonical.SuperchargeCARCCRBridge, InfoGeometry.Canonical.TomitaTakesaki, InfoGeometry.Krein.DoubledSpace, InfoGeometry.Krein.KreinSpace, InfoGeometry.Krein.Superphysics`
  - motif: `instL2Complete -> doubledCarrier -> complex_i_sq -> complex_iSupercharge_hamiltonian -> modularCPTSupercharge_hamiltonian -> cptSuperchargeOp_sq -> canonicalDIIIProxy -> canonicalDIIIProxy_C_eq_modular_j`
- `bundle:6081ce64e87a`: reuse-score `25.0` | carriers `5` | sinks `1` | upstream `InfoGeometry.Krein.KreinSpace`
  - carrier modules: `InfoGeometry.Canonical.DIIICommutatorInitialization, InfoGeometry.Canonical.RealBdG, InfoGeometry.Canonical.RealBdGDIIIAtom, InfoGeometry.Krein.DoubledSpace, InfoGeometry.Krein.KreinSpace`
  - motif: `instL2Complete -> doubledCarrier -> complex_i_sq -> modularK_sq -> topologicalClassDIII_of_realBdGDatum -> canonicalDIIIProxy_topologicalClassDIII_of_realBdGDatum`
- `bundle:2cbafe241189`: reuse-score `10.8` | carriers `2` | sinks `2` | upstream `InfoGeometry.Quantum.BulkBoundary`
  - carrier modules: `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge, InfoGeometry.Quantum.BulkBoundary`
  - motif: `EndS -> HasZeroMode -> drazinProjection_ne_one_of_hasZeroMode`
- `bundle:f52e155db8bd`: reuse-score `6.8` | carriers `2` | sinks `1` | upstream `InfoGeometry.Quantum.BulkBoundary`
  - carrier modules: `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge, InfoGeometry.Quantum.BulkBoundary`
  - motif: `exists_zeroMode_of_hasZeroMode -> exists_zeroMode_of_dim_mismatch -> zeroModeRegularizationPackage_of_dim_mismatch -> exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch`
- `bundle:343810c8cb03`: reuse-score `6.7` | carriers `2` | sinks `1` | upstream `InfoGeometry.Quantum.BulkBoundary`
  - carrier modules: `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge, InfoGeometry.Quantum.BulkBoundary`
  - motif: `exists_zeroMode_of_hasZeroMode -> moorePenroseLeftProjector_ne_one_of_hasZeroMode`
- `bundle:75b746d0432c`: reuse-score `6.6` | carriers `2` | sinks `1` | upstream `InfoGeometry.Krein.DoubledSpace`
  - carrier modules: `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra, InfoGeometry.Krein.DoubledSpace`
  - motif: `DoubledSpace -> instIsScalarTowerRealContinuousLinearMapIdDoubledSpace`
