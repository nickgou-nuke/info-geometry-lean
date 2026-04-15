# Structural Fibers

This report decomposes the native source-sink correspondence into packet-conditioned corridor strands so bulk entanglement can be separated from sink-surface pressure.

- structure: `/home/goutev/LEAN4/info-geometry-lean/artifacts/dag/structural-topology.json`
- bipartite artifact: `/home/goutev/LEAN4/info-geometry-lean/artifacts/dag/source-sink-bipartite.json`

## Summary
- native components: `17873`
- packet fibers: `7`
- source-sink fiber groups: `4`
- multi-packet source-sink groups: `2`
- sink-family entanglements: `4`
- multi-packet sink families: `2`
- packet kinds: `{'presentation_duplicate': 3, 'transport_projection': 1, 'single_strand': 3}`
- entanglement kinds: `{'transport_fibered': 2, 'presentation_heavy': 1, 'single_strand': 1}`
- top packet score: `79.25`
- top group score: `25.3`
- top entanglement score: `29.3`

## Packet Fibers
- `bundle:abbbb4a36d13`: kind `presentation_duplicate` | score `79.25` | source `InfoGeometry.Krein.KreinSpace` | sink `InfoGeometry.Canonical.ModularSuperchargeClosure, InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge, InfoGeometry.Canonical.RealBdGDIIIAtom, InfoGeometry.Canonical.UnifiedSuperchargeAlgebra`
  - canonical endpoint: `InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalSeedFlow_eq_internalUnruhFlowOfModularTime` | wrappers `11` | carriers `5` | roles `constructive_source, consumer_sink`
  - corridor: `InfoGeometry.Krein.instL2Complete`
- `bundle:e1ff0eb12e61`: kind `presentation_duplicate` | score `16.4` | source `InfoGeometry.Krein.KreinSpace` | sink `InfoGeometry.Canonical.RealBdGDIIIAtom`
  - canonical endpoint: `InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_laws` | wrappers `1` | carriers `6` | roles `constructive_source, consumer_sink`
  - corridor: `InfoGeometry.Krein.instL2Complete, InfoGeometry.Krein.doubledCarrier, InfoGeometry.Krein.complex_i_sq, InfoGeometry.Krein.complex_iSupercharge_hamiltonian, InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge_hamiltonian, InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp_sq`
  - strict dominators: `InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge_hamiltonian, InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp_sq`
- `bundle:2cbafe241189`: kind `presentation_duplicate` | score `7.8` | source `InfoGeometry.Quantum.BulkBoundary` | sink `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge`
  - canonical endpoint: `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.drazinProjection_ne_one_of_hasZeroMode` | wrappers `1` | carriers `2` | roles `constructive_source, consumer_sink`
  - corridor: `InfoGeometry.Quantum.BulkBoundary.EndS, InfoGeometry.Quantum.BulkBoundary.HasZeroMode`
- `bundle:6081ce64e87a`: kind `transport_projection` | score `7.0` | source `InfoGeometry.Krein.KreinSpace` | sink `InfoGeometry.Canonical.RealBdGDIIIAtom`
  - canonical endpoint: `InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_topologicalClassDIII_of_realBdGDatum` | wrappers `0` | carriers `5` | roles `constructive_source, consumer_sink`
  - corridor: `InfoGeometry.Krein.instL2Complete, InfoGeometry.Krein.doubledCarrier, InfoGeometry.Krein.complex_i_sq, InfoGeometry.Canonical.RealBdG.modularK_sq, InfoGeometry.Canonical.DIIICommutatorInitialization.topologicalClassDIII_of_realBdGDatum`
  - strict dominators: `InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_topologicalClassDIII_of_realBdGDatum, InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_commutator_packet_of_realBdGDatum`
- `bundle:f52e155db8bd`: kind `single_strand` | score `0.8` | source `InfoGeometry.Quantum.BulkBoundary` | sink `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge`
  - canonical endpoint: `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch` | wrappers `0` | carriers `2` | roles `constructive_source, consumer_sink`
  - corridor: `InfoGeometry.Quantum.BulkBoundary.exists_zeroMode_of_hasZeroMode, InfoGeometry.Quantum.BulkBoundary.exists_zeroMode_of_dim_mismatch`
  - strict dominators: `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.zeroModeRegularizationPackage_of_dim_mismatch`
- `bundle:343810c8cb03`: kind `single_strand` | score `0.7` | source `InfoGeometry.Quantum.BulkBoundary` | sink `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge`
  - canonical endpoint: `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.moorePenroseLeftProjector_ne_one_of_hasZeroMode` | wrappers `0` | carriers `2` | roles `constructive_source, consumer_sink`
  - corridor: `InfoGeometry.Quantum.BulkBoundary.exists_zeroMode_of_hasZeroMode`
- `bundle:75b746d0432c`: kind `single_strand` | score `0.6` | source `InfoGeometry.Krein.DoubledSpace` | sink `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra`
  - canonical endpoint: `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.instIsScalarTowerRealContinuousLinearMapIdDoubledSpace` | wrappers `0` | carriers `2` | roles `constructive_source, consumer_sink`
  - corridor: `InfoGeometry.Krein.DoubledSpace`

## Source-Sink Fiber Groups
- `InfoGeometry.Quantum.BulkBoundary` -> `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge`: class `multi_packet_mixed` | packets `3` | corridors `3` | score `25.3`
  - canonical endpoints: `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.drazinProjection_ne_one_of_hasZeroMode, InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch, InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.moorePenroseLeftProjector_ne_one_of_hasZeroMode` | wrappers `1` | sink surfaces `4`
  - branch points: `InfoGeometry.Quantum.BulkBoundary.EndS, InfoGeometry.Quantum.BulkBoundary.exists_zeroMode_of_hasZeroMode`
  - merge points: `InfoGeometry.Quantum.BulkBoundary.HasZeroMode, InfoGeometry.Quantum.BulkBoundary.exists_zeroMode_of_dim_mismatch, InfoGeometry.Quantum.BulkBoundary.exists_zeroMode_of_hasZeroMode`
- `InfoGeometry.Krein.KreinSpace` -> `InfoGeometry.Canonical.ModularSuperchargeClosure, InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge, InfoGeometry.Canonical.RealBdGDIIIAtom, InfoGeometry.Canonical.UnifiedSuperchargeAlgebra`: class `single_packet_presentation` | packets `1` | corridors `1` | score `23.25`
  - canonical endpoints: `InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalSeedFlow_eq_internalUnruhFlowOfModularTime` | wrappers `11` | sink surfaces `12`
  - shared source trunk: `InfoGeometry.Krein.instL2Complete`
  - shared sink trunk: `InfoGeometry.Krein.instL2Complete`
- `InfoGeometry.Krein.KreinSpace` -> `InfoGeometry.Canonical.RealBdGDIIIAtom`: class `multi_packet_mixed` | packets `2` | corridors `2` | score `14.9`
  - canonical endpoints: `InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_laws, InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_topologicalClassDIII_of_realBdGDatum` | wrappers `1` | sink surfaces `3`
  - shared source trunk: `InfoGeometry.Krein.instL2Complete, InfoGeometry.Krein.doubledCarrier, InfoGeometry.Krein.complex_i_sq`
  - branch points: `InfoGeometry.Krein.complex_iSupercharge_hamiltonian, InfoGeometry.Canonical.RealBdG.modularK_sq`
  - merge points: `InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp_sq, InfoGeometry.Canonical.DIIICommutatorInitialization.topologicalClassDIII_of_realBdGDatum`
- `InfoGeometry.Krein.DoubledSpace` -> `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra`: class `single_packet` | packets `1` | corridors `1` | score `0.1`
  - canonical endpoints: `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.instIsScalarTowerRealContinuousLinearMapIdDoubledSpace` | wrappers `0` | sink surfaces `1`
  - shared source trunk: `InfoGeometry.Krein.DoubledSpace`
  - shared sink trunk: `InfoGeometry.Krein.DoubledSpace`

## Sink-Family Entanglements
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge`: class `transport_fibered` | packets `3` | source modules `1` | corridors `3` | score `29.3`
  - canonical endpoints: `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.drazinProjection_ne_one_of_hasZeroMode, InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch, InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.moorePenroseLeftProjector_ne_one_of_hasZeroMode` | wrappers `1` | sink surfaces `4`
  - source modules: `InfoGeometry.Quantum.BulkBoundary`
  - branch points: `InfoGeometry.Quantum.BulkBoundary.EndS, InfoGeometry.Quantum.BulkBoundary.exists_zeroMode_of_hasZeroMode`
  - merge points: `InfoGeometry.Quantum.BulkBoundary.HasZeroMode, InfoGeometry.Quantum.BulkBoundary.exists_zeroMode_of_dim_mismatch, InfoGeometry.Quantum.BulkBoundary.exists_zeroMode_of_hasZeroMode`
- `InfoGeometry.Canonical.ModularSuperchargeClosure, InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge, InfoGeometry.Canonical.RealBdGDIIIAtom, InfoGeometry.Canonical.UnifiedSuperchargeAlgebra`: class `presentation_heavy` | packets `1` | source modules `1` | corridors `1` | score `23.25`
  - canonical endpoints: `InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalSeedFlow_eq_internalUnruhFlowOfModularTime` | wrappers `11` | sink surfaces `12`
  - source modules: `InfoGeometry.Krein.KreinSpace`
  - shared sink trunk: `InfoGeometry.Krein.instL2Complete`
- `InfoGeometry.Canonical.RealBdGDIIIAtom`: class `transport_fibered` | packets `2` | source modules `1` | corridors `2` | score `16.9`
  - canonical endpoints: `InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_laws, InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_topologicalClassDIII_of_realBdGDatum` | wrappers `1` | sink surfaces `3`
  - source modules: `InfoGeometry.Krein.KreinSpace`
  - branch points: `InfoGeometry.Krein.complex_iSupercharge_hamiltonian, InfoGeometry.Canonical.RealBdG.modularK_sq`
  - merge points: `InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp_sq, InfoGeometry.Canonical.DIIICommutatorInitialization.topologicalClassDIII_of_realBdGDatum`
- `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra`: class `single_strand` | packets `1` | source modules `1` | corridors `1` | score `0.1`
  - canonical endpoints: `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.instIsScalarTowerRealContinuousLinearMapIdDoubledSpace` | wrappers `0` | sink surfaces `1`
  - source modules: `InfoGeometry.Krein.DoubledSpace`
  - shared sink trunk: `InfoGeometry.Krein.DoubledSpace`
