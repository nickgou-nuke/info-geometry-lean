# Module Map

> Status: `current authority`
> Audited: 2026-05-02
> Note: Maintained against the live code surface.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This is the short practical map of the current codebase.

## Primary Entry Surfaces

Lean:

- `lean/InfoGeometry.lean`
- `lean/InfoGeometry/All.lean`
- `lean/InfoGeometry/Audit.lean`
- `lean/InfoGeometry/Meta/`

Python:

- `src/igf/cli.py`
- `src/igf/pipeline/`
- `src/igf/graph/`
- `src/igf/artifacts/`
- `tools/infra/`
- `tools/frontier/`
- `tools/docs/`
- `tools/leantrail/`

## Major Lean Families Present

The current `lean/InfoGeometry/` tree includes major families such as:

- `Algebraic`
- `Arithmetic`
- `Automorphic`
- `Canonical`
- `Compatibility`
- `Convex`
- `Core`
- `ExponentialFamily`
- `Geometry`
- `GrandCanonical`
- `Interpretation`
- `Krein`
- `LLM`
- `Meta`
- `OperatorAlgebra`
- `Projective`
- `Quantum`
- `SuperMetriplectic`
- `Thermodynamics`
- `Topological`
- `Twistor`

Selected bridge surfaces that connect these families:

- `lean/InfoGeometry/Canonical/MoebiusVirasoroBridge.lean`
- `lean/InfoGeometry/Canonical/PrimeExteriorSugawaraBridge.lean`
- `lean/InfoGeometry/Arithmetic/PrimeExteriorMobiusBridge.lean`
- `lean/InfoGeometry/GrandUnification/HodgeTrifactorBridge.lean`
- `lean/InfoGeometry/Krein/TomitaMatrixAtom.lean`
- `lean/InfoGeometry/Arithmetic/ZetaSymmetryAdaptedDefinitions.lean`
- `lean/InfoGeometry/Arithmetic/WittenParityIndex.lean`
- `lean/InfoGeometry/Canonical/UHFInductiveColimitBoundary.lean`
- `lean/InfoGeometry/Canonical/CuntzCantorBoundaryShift.lean`
- `lean/InfoGeometry/Canonical/CantorBoundaryCuntzShift.lean`
- `lean/InfoGeometry/Canonical/BostConnesSuperalgebra.lean`
- `lean/InfoGeometry/Canonical/EvansHarmonicTrap.lean`
- `lean/InfoGeometry/Canonical/DeformedIdeleAction.lean`
- `lean/InfoGeometry/Canonical/DeformedIdeleDysonBridge.lean`
- `lean/InfoGeometry/Canonical/FinitePhenomenologyReadout.lean`
- `lean/InfoGeometry/Algebra/NonCommutativeIsometry.lean`
- `lean/InfoGeometry/Arithmetic/SpectorPrimonGasBridge.lean`
- `lean/InfoGeometry/Arithmetic/CastroThetaScalingBridge.lean`
- `lean/InfoGeometry/Canonical/HaugManiYinYangBridge.lean`
- `lean/InfoGeometry/Canonical/BiquaternionTorsionBridge.lean`
- `lean/InfoGeometry/Clifford/GullDoranPseudoscalarBridge.lean`
- `lean/InfoGeometry/Arithmetic/KudinoorWittenIndexBridge.lean`

For the 2026-06-10 finite index-theorem milestone, see
[noncommutative-index-theorem-milestone.md](noncommutative-index-theorem-milestone.md).
For the centered zeta coordinate API, see
[centered-zeta-coordinate-api.md](centered-zeta-coordinate-api.md).
For the finite Cuntz-Cantor shift API, see
[cuntz-cantor-boundary-shift-api.md](cuntz-cantor-boundary-shift-api.md).
For the finite Cuntz/Weyl UHF bridge API, see
[cuntz-weyl-uhf-bridge-api.md](cuntz-weyl-uhf-bridge-api.md).
For the finite Bost-Connes/Witten supertrace API, see
[bost-connes-superalgebra-api.md](bost-connes-superalgebra-api.md).
For the finite Evans harmonic-trap lattice API, see
[evans-harmonic-trap-api.md](evans-harmonic-trap-api.md).
For the finite deformed-idele/Cuntz commutator API, see
[deformed-idele-action-api.md](deformed-idele-action-api.md).
For the finite Spector primon-gas arithmetic API, see
[spector-primon-gas-bridge-api.md](spector-primon-gas-bridge-api.md).
For the finite Castro theta/scaling API, see
[castro-theta-scaling-bridge-api.md](castro-theta-scaling-bridge-api.md).
For the finite Haug-Mani real doubled bridge API, see
[haug-mani-yin-yang-bridge-api.md](haug-mani-yin-yang-bridge-api.md).
For the finite quaternion condensate API, see
[quaternion-condensate-api.md](quaternion-condensate-api.md).
For the finite quaternion embedding API, see
[quaternion-embedding-api.md](quaternion-embedding-api.md).
For the finite split-octonion/Zorn trace API, see
[octonion-condensate-api.md](octonion-condensate-api.md).
For the finite biquaternion `SU(2)` commutator API, see
[biquaternion-su2-api.md](biquaternion-su2-api.md).
For the finite Weyl / crystal surface API, see
[weyl-crystal-surface-api.md](weyl-crystal-surface-api.md).
For the finite Berry / Klein / Bott bridge API, see
[klein-berry-boundary-bott-api.md](klein-berry-boundary-bott-api.md).
For the external braid / Fibonacci precedent map, see
[external-braid-fibonacci-map.md](external-braid-fibonacci-map.md).
For the finite inverse-zeta / Weyl / Witten master-key API, see
[inverse-zeta-weyl-master-key-api.md](inverse-zeta-weyl-master-key-api.md).
For the Katz-Sarnak density/symmetry index, see
[katz-sarnak-density-index.md](katz-sarnak-density-index.md).
For the finite Gull-Doran-Lasenby pseudoscalar bridge API, see
[gull-doran-pseudoscalar-bridge-api.md](gull-doran-pseudoscalar-bridge-api.md).
For the finite emergent-gravity action-variation API, see
[emergent-gravity-action-variation-api.md](emergent-gravity-action-variation-api.md).
For the additive-combinatorics bounds API, see
[additive-combinatorics-bounds-api.md](additive-combinatorics-bounds-api.md).
For the finite Kudinoor supersymmetry/Witten-index bridge API, see
[kudinoor-witten-index-bridge-api.md](kudinoor-witten-index-bridge-api.md).
For the unified finite matrix witness index, see
[finite-matrix-witness-index.md](finite-matrix-witness-index.md).
For the finite phenomenology readout dictionary, see
[finite-phenomenology-readout-api.md](finite-phenomenology-readout-api.md).

The practical rule is simple:

- use `Audit.lean` and `Meta/` to understand architecture and policy
- use owner modules under `Canonical/`, `Arithmetic/`, `Projective/`, and
  related families for the actual theorem surface
- use umbrella files only after you know the owner path you care about

## Major Python Families Present

`src/igf/` currently exposes:

- `config`
  environment and configuration loading
- `artifacts`
  artifact I/O, manifests, normalization adapters
- `graph`
  Arango collections, clients, query running, indexes
- `pipeline`
  build, validate, ingest, verify, report, orchestration
- `policy`
  claim-scope policy support

## Current Operator Commands

Start with:

```bash
lake script run changedVerify
lake script run dagStatus
lake script run dagDoctor
```

For the Python package:

```bash
igf preflight
igf build
igf validate
igf run
```

## Read By Task

If you need architecture:

- `lean/InfoGeometry/Audit.lean`
- `lean/InfoGeometry/Meta/`
- [OperationalIntent.md](OperationalIntent.md)

If you need tooling:

- [../tools/README.md](../tools/README.md)
- [../tools/infra/README.md](../tools/infra/README.md)
- [LeanTrail.md](LeanTrail.md)

If you need onboarding:

- [../Installation.md](../Installation.md)
- [../NEWCOMER_PATH.md](../NEWCOMER_PATH.md)

If you need current status:

- [CODEBASE_STATUS.md](CODEBASE_STATUS.md)
