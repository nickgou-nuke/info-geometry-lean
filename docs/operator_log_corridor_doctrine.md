# Operator-Log Corridor Doctrine

This note is a doctrine file for one specific future owner packet:
support-restricted operator logarithms and their scalar shadows.

It is not the main current roadmap of the repository.

The current repository already has live operator-level owners in other trunks:

- corrected phase-space generalized metric:
  - `lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean`
- KKT / inverse-kernel / conformal operator packet:
  - `lean/InfoGeometry/Canonical/KKTCore.lean`
  - `lean/InfoGeometry/Canonical/EPDefectAlgebra.lean`
  - `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`
- modular / Bogoliubov operator packet:
  - `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
  - `lean/InfoGeometry/Canonical/BogoliubovTransport.lean`

What remains missing is narrower:

- a native support-log owner for positive operators;
- a clean operator-to-scalar bridge for determinant and pseudo-determinant
  shadows.

The owner-level relative modular operator file is now present:

- `lean/InfoGeometry/Canonical/RelativeModularOperator.lean`

## Doctrine

For this corridor the direction remains:

`operator owner -> scalar shadow -> facade or lift`

The scalar object must never be treated as the source of truth for the operator
object.

## Current status by layer

### Owner layers already present elsewhere in the repo

These are live operator owners, but they are not support-log owners:

- `PhaseSpaceGeneralizedMetric` owns `g`, `B`, `S`, `P±`, and `ℋ` on `E × E*`
- `TomitaTakesaki` owns the doubled `J`, `ε`, and `Jε` packet
- `EPDefectAlgebra` owns Moore-Penrose / Drazin defect operators
- `ConformalAnomalySource` owns the projector-obstruction / anomaly operator
  surface

### Scalar corridors already present

- `lean/InfoGeometry/Canonical/DeterminantCore.lean`
- `lean/InfoGeometry/Canonical/Determinant.lean`
- `lean/InfoGeometry/Canonical/RelativePotentialScalarBridge.lean`
- `lean/InfoGeometry/Canonical/KMSSinkhornScalarPotential.lean`
- `lean/InfoGeometry/Volume/DeterminantBundle.lean`
- `lean/InfoGeometry/Volume/ConnesCocycle.lean`

These are real scalar corridors. They should not be read as if they already
provide the missing support-log owner layer.

### Facade or lift layers already present

- `lean/InfoGeometry/Canonical/OperatorialInformationLift.lean`
- `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean`
- `lean/InfoGeometry/Canonical/YangMillsContinuum.lean`

These may remain useful, but they are downstream packaging unless and until a
true owner layer is formalized beneath them.

## What is actually missing

The missing operator-log packet is now:

1. a support-restricted operator logarithm owner;
2. a bridge theorem relating it to determinant or pseudo-determinant scalar
   shadows in the finite setting.

Proposed files remain:

- `InfoGeometry.Canonical.SupportLog` (proposed)
- `InfoGeometry.Canonical.SupportLogScalarBridge` (proposed)
- `InfoGeometry.Canonical.PseudoDetCore` (proposed)

These should be built only after the current branch junction closures are done.

## Current repository priority

This doctrine is not the immediate next task.

The immediate closure burden remains:

1. derive the realized-projector to maintained tomita-projector identification;
2. attach the count/projective trunk to the corrected phase-space trunk at the polarized junction;
3. add one twisted end-to-end finite-dimensional example;
4. tighten the response matrix to the Weyl anomaly readout for grand-canonical models; and
5. formalize the spinor-modular identification theorem.

Only after those are closed should this support-log doctrine move back to the
front of the queue.

## Terminology discipline

- `operator owner` means the operator itself is defined and carries its own
  basic theorems.
- `scalar shadow` means a trace, determinant, pairing, or norm extracted from
  that operator.
- `facade lift` means a scalar object is repackaged as an operator coefficient
  or a downstream interface.

The doctrine here is only that these three layers must not be confused.
