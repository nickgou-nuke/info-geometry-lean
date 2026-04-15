# Structural anti-bleed diagnostic

- structure: `/home/goutev/LEAN4/info-geometry-lean/artifacts/dag/structural-topology.json`
- bipartite artifact: `/home/goutev/LEAN4/info-geometry-lean/artifacts/dag/source-sink-bipartite.json`
- model: native component support on the Lean-emitted condensation DAG
- criterion: pairwise partial-support bleed

## Anchor structure
- strictly safe: **6**
- anchored: **3**
- unanchored: **4**

## Pairwise bleed
- violating pairs: **3**
- leaking source carriers: **3**
- split target carriers: **2**

## Worst source carriers
- `InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge`: 1 leaking targets, total missing=2, total overlap=1
- `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra`: 1 leaking targets, total missing=2, total overlap=1
- `InfoGeometry.Canonical.RealBdGDIIIAtom`: 1 leaking targets, total missing=1, total overlap=4

## Worst target carriers
- `InfoGeometry.Krein.DoubledSpace`: 2 leaking sources, total missing=4, total overlap=2
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge`: 1 leaking sources, total missing=1, total overlap=4

## Anchor candidates
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge`: support=5, anchor=InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch
- `InfoGeometry.Quantum.BulkBoundary`: support=4, anchor=InfoGeometry.Quantum.BulkBoundary.exists_zeroMode_of_dim_mismatch
- `InfoGeometry.Krein.DoubledSpace`: support=3, anchor=InfoGeometry.Krein.complex_i_sq

## Worst violating pairs
- `InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge` -> `InfoGeometry.Krein.DoubledSpace`: overlap=1, missing=2
  - overlap components: InfoGeometry.Krein.DoubledSpace
  - missing components: InfoGeometry.Krein.complex_i_sq, InfoGeometry.Krein.doubledCarrier
- `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra` -> `InfoGeometry.Krein.DoubledSpace`: overlap=1, missing=2
  - overlap components: InfoGeometry.Krein.DoubledSpace
  - missing components: InfoGeometry.Krein.complex_i_sq, InfoGeometry.Krein.doubledCarrier
- `InfoGeometry.Canonical.RealBdGDIIIAtom` -> `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge`: overlap=4, missing=1
  - overlap components: InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.drazinProjection_ne_one_of_hasZeroMode, InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.moorePenroseLeftProjector_ne_one_of_hasZeroMode, InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.moorePenroseRightProjector_ne_one_of_hasZeroMode, InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.zeroModeRegularizationPackage_of_dim_mismatch
  - missing components: InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch
