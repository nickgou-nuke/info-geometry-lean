# Representation Depth Index

Status: `provisional-manual-index`

Intent: depth-indexed bicategory of presentation layers, atomic translators, and coherence files for the stable information-geometry spine.

## Layers
- `L0` Count: raw relative counts, relative volume data, positive-measure representatives.
- `L1` ProjectiveGauge: positive rays, gauge sections, relative log-potentials, normalization/projectivization layer.
- `L2` Operator: diagonal operator lift, partition/log-partition calculus, scalar modular Hamiltonian as operator syntax.
- `L3` KreinClifford: split/Krein quadratic geometry, polarized sheets, Dirac/metric compatibility on the doubled carrier.
- `L4` Transport: Bogoliubov transport, Hestenes-frame changes, transported spectral and transported thermal generators.
- `L5` ThermoAttention: Gibbs states, Sinkhorn balance, softmax/attention phenomenology.

## Tracked Files
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean` | `translator` | `0→1` | Counts to projective/gauge layer via countRay, mass normalization, and relative modular-potential formulas.
- `lean/InfoGeometry/Canonical/PositiveRayCore.lean` | `owner` | `1→1` | Owner of the positive-ray/gauge-section presentation.
- `lean/InfoGeometry/Canonical/RelativePotentialCore.lean` | `owner` | `1→1` | Owner of relative density, relative log-density, and relative modular potential on rays.
- `lean/InfoGeometry/Canonical/RelativePotentialDiscreteBridge.lean` | `translator` | `1→1` | Discrete/projective realization within the projective-gauge layer.
- `lean/InfoGeometry/Canonical/RelativePotentialScalarBridge.lean` | `translator` | `1→1` | Singleton scalar realization of the projective-gauge layer.
- `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean` | `translator` | `1→2` | First quantization of relative potentials and surprisal observables into diagonal operators.
- `lean/InfoGeometry/Canonical/InformationPartitionCore.lean` | `owner` | `2→2` | Owner of partition/log-partition syntax and derivative lemmas for modular generators.
- `lean/InfoGeometry/Canonical/DiagonalMetricModularBridge.lean` | `coherence` | `2→3` | Diagonal coherence cell between scalar/operator modular Hamiltonian form and the spectral metric operator.
- `lean/InfoGeometry/Krein/SplitQuadratic.lean` | `owner` | `3→3` | Owner of the global signed split/Krein quadratic calibration.
- `lean/InfoGeometry/Krein/SplitQuadraticSheets.lean` | `owner` | `3→3` | Owner of sheet restriction and sign recovery on the split/Krein carrier.
- `lean/InfoGeometry/Krein/PolarizedSector.lean` | `owner` | `3→3` | Owner of the positive/negative sector maps and projected sign laws.
- `lean/InfoGeometry/Canonical/KreinDiracPolarizationBridge.lean` | `translator` | `2→3` | Operator/spectral structures transported onto the doubled Krein-Clifford carrier.
- `lean/InfoGeometry/Canonical/KreinDiracSpectralLift.lean` | `translator` | `3→4` | Transported Dirac generator and partition calculus on the Bogoliubov-moved carrier.
- `lean/InfoGeometry/Canonical/BogoliubovPolarizationBridge.lean` | `translator` | `3→4` | Primitive Bogoliubov/polarization transport step.
- `lean/InfoGeometry/Canonical/KreinDiracWeightFunctionalLift.lean` | `coherence` | `3→4` | Transport-layer coherence between transported Dirac, transported thermal generators, and their weight-functional/log-partition presentations.
- `lean/InfoGeometry/Canonical/SplitCliffordThermalBridge.lean` | `translator` | `3→4` | Transport-local grand-canonical deformation and partition/log-partition calculus on the doubled transported carrier; not yet the Gibbs/attention surface.
- `lean/InfoGeometry/Canonical/AttentionPolarizedSplit.lean` | `translator` | `4→5` | Positive-sheet transported score to softmax attention semantics.
- `lean/InfoGeometry/Canonical/AttentionPolarizedGibbsBridge.lean` | `coherence` | `5→5` | Coherence between polarized attention weights/heads and finite Gibbs weights/expectations.
- `lean/InfoGeometry/Canonical/AttentionPolarizedSinkhornBridge.lean` | `coherence` | `5→5` | Coherence between the polarized Gibbs matrix and Sinkhorn/bistochastic structure.
- `lean/InfoGeometry/Convex/LogSumExp.lean` | `owner` | `5→5` | Scalar gauge/softmax owner on the thermodynamic-attention surface.

## Rules
- atomic translator: A translator should satisfy target_depth <= source_depth + 1.
- coherence cell: A coherence file may mention multiple adjacent layers but should define no new skip-level ontology.
- capstone exception: A capstone may consume multiple depths only if it introduces no new primitive translators.

## Review Surface
- `lean/InfoGeometry/Canonical/ChiralTorsionRelativeVolume.lean` | Still imports quarantined BeliefDynamics; likely a facade or missing primitive translator.
- `lean/InfoGeometry/Canonical/ConformalAlgebra.lean` | Depends on structural primitives currently owned by quarantined ChiralCliffordBridge.
- `lean/InfoGeometry/Canonical/CountEmergentFlow.lean` | Still imports quarantined HolographicEmergence; likely a higher-level facade rather than an adjacent-depth translator.
