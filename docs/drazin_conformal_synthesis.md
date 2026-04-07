# Drazin / Conformal / Anomaly Topic Map

This note maps the current singular-operator and conformal/anomaly corridor.

It is not a theorem certificate and it should not be read as a substitute for
the source.

## Current live packet

The current active packet is best read through:

- `lean/InfoGeometry/Canonical/KKTCore.lean`
- `lean/InfoGeometry/Canonical/EPDefectAlgebra.lean`
- `lean/InfoGeometry/Canonical/KKTGeneralizedInverseBridge.lean`
- `lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- `lean/InfoGeometry/Canonical/ChiralCartanCore.lean`
- `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`
- `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
- `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`
- `lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean`
- `lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean`

This is the current load-bearing corridor from generalized inverse data to
conformal and anomaly outputs.

## Reading of older singular files

Older singular / inverse files still matter, but they are no longer the
cleanest reading path for the active corridor by themselves.

The operative reading is now:

- KKT grading supplies the structural split;
- `EPDefectAlgebra` packages the defect operators;
- `KKTGeneralizedInverseBridge` places those defect objects in grade-zero;
- `ConformalProjectorCore`, `ChiralCartanCore`, and
  `ConformalAnomalySource` package the conformal/anomaly leaf;
- the corrected phase-space trunk now feeds this corridor through
  `PhaseSpaceConformalKKTBridge`.

## Current open gap

The remaining open step is not another scalar identity. It is:

- deriving the projector obstruction operator from trunk-compatible grading
  data, and
- only then routing Weyl holonomy through that theorem.

Until that exists, the conformal/Weyl weld is improved but not final.

## Use rule

Use this note as a map of the current packet only. Inspect the Lean files for
actual statements and exact ownership.
