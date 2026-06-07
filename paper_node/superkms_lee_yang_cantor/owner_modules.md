# Owner Modules

This packet is a publication-prep handoff.  The only proof authority is the
Lean source in the owner modules below plus the recorded Lake checks.

## Included Owner Surfaces

- `lean/InfoGeometry/Canonical/PrimeCantorThermoYangBaxterBridge.lean`
- `lean/InfoGeometry/Canonical/CayleyCriticalLineCircleBridge.lean`
- `lean/InfoGeometry/Canonical/PrimeLeeYangRHBridge.lean`
- `lean/InfoGeometry/Canonical/PrimeLeeYangFerromagneticChain.lean`
- `lean/InfoGeometry/Canonical/PrimeGasSuperKMSBridge.lean`
- `lean/InfoGeometry/Canonical/PrimeBinaryCantorSuperalgebraBridge.lean`
- `lean/InfoGeometry/Arithmetic/PrimeSuperalgebraReadback.lean`
- `lean/InfoGeometry/Analysis/L2CantorCommutation.lean`
- `lean/InfoGeometry/Canonical/BregmanDeformation.lean`
- `lean/InfoGeometry/Canonical/KMSInteriorPoint.lean`
- `lean/InfoGeometry/Canonical/KleinBottleSewing.lean`
- `lean/InfoGeometry/Canonical/ChiralAnomalyCantor.lean`
- `lean/InfoGeometry/Canonical/PrimeCl11ModularAtomCore.lean`
- `lean/InfoGeometry/Canonical/PrimeMajoranaWittenCharacter.lean`
- `lean/InfoGeometry/Canonical/HodgeDiracLaplacianBridge.lean`
- `lean/InfoGeometry/Categorical/FibonacciBraiding.lean`
- `lean/InfoGeometry/Canonical/YangBaxterProof.lean`

## Non-Owner Readout Or Debt Files

- `lean/InfoGeometry/Quantum/FibonacciFusionCategory.lean`
  - Finite matrix readout only.
  - Pentagon and hexagon coherence are closure debt.
- `lean/InfoGeometry/Canonical/PrimonFibBoundaryBridge.lean`
  - Closure-debt record only.
  - It does not own zeta, V4 parity, or boson/fermion splitting theorems.

## Category Discipline

`docs/CATEGORICAL_INFRASTRUCTURE_MAP.md` is binding for this packet:

- categorical Fibonacci content is owned by `Categorical/FibonacciBraiding.lean`;
- matrix Fibonacci code is an instance/readout;
- pentagon, hexagon, and `BraidedCategory` packaging remain open debt.
