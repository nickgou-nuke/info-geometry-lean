# Replacement Frontier

This report ranks declarations by replacement feasibility, not by proof triviality.
It integrates DAG consumer classes, representation depth, vacuity signals, and artifact freshness checks.

## Artifact Trust

- schema version: `3`
- timestamp: `2026-04-15T17:36:52.538858+00:00`
- olean hash: `003dcbc996b53b2d90186e433bb89afda0bd941f1feaf75e8e30057b3b74fc2e`

## Summary

- candidate declarations: `3758`
- modules with replacement pressure: `551`
- class counts: `{'wrapper_surface': 88, 'bridge_surface_promoted': 3, 'dead_public_theorem': 3294, 'package_reprojection_surface': 232, 'hypothesis_bridge_surface': 45, 'surrogate_surface': 77, 'internal_staging_only': 17, 'live_wrapper_surface': 2}`
- depth counts: `{'untracked': 3756, 'transport': 1, 'operator': 1}`
- vacuity counts: `{'V1/public-wrapper-inflation': 92, 'V2/dead-public-theorem': 3376, 'V4/bridge-infrastructure-promoted': 5, 'V0/syntactic-vacuity': 84}`

## Top Modules

| File | Score | Candidates | Substantive-free | Depths | Classes | Vacuity |
| --- | ---: | ---: | ---: | --- | --- | --- |
| `lean/InfoGeometry/Canonical/BerryConnection.lean` | 427 | 41 | 41 | `{}` | `{'dead_public_theorem': 37, 'package_reprojection_surface': 4}` | `{'V2/dead-public-theorem': 37}` |
| `lean/InfoGeometry/Krein/HilbertBridge.lean` | 384 | 32 | 32 | `{}` | `{'dead_public_theorem': 32}` | `{'V2/dead-public-theorem': 32}` |
| `lean/InfoGeometry/MaxEnt/Jaynes.lean` | 378 | 32 | 32 | `{}` | `{'dead_public_theorem': 27, 'package_reprojection_surface': 5}` | `{'V2/dead-public-theorem': 27}` |
| `lean/InfoGeometry/Quantum/RealMajorana.lean` | 372 | 31 | 31 | `{}` | `{'dead_public_theorem': 31}` | `{'V2/dead-public-theorem': 31}` |
| `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean` | 369 | 31 | 31 | `{}` | `{'package_reprojection_surface': 4, 'dead_public_theorem': 27}` | `{'V2/dead-public-theorem': 27}` |
| `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean` | 362 | 36 | 36 | `{}` | `{'dead_public_theorem': 22, 'surrogate_surface': 2, 'package_reprojection_surface': 8, 'hypothesis_bridge_surface': 4}` | `{'V2/dead-public-theorem': 22}` |
| `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean` | 354 | 31 | 31 | `{}` | `{'dead_public_theorem': 31}` | `{'V2/dead-public-theorem': 31}` |
| `lean/InfoGeometry/Canonical/UnifiedSuperchargeAlgebra.lean` | 353 | 30 | 30 | `{}` | `{'dead_public_theorem': 17, 'package_reprojection_surface': 12, 'wrapper_surface': 1}` | `{'V2/dead-public-theorem': 18, 'V1/public-wrapper-inflation': 1}` |
| `lean/InfoGeometry/Core/SymmetricLieSpaces.lean` | 336 | 28 | 28 | `{}` | `{'dead_public_theorem': 28}` | `{'V2/dead-public-theorem': 28}` |
| `lean/InfoGeometry/Core/SymmetricLie.lean` | 310 | 26 | 26 | `{}` | `{'surrogate_surface': 9, 'package_reprojection_surface': 4, 'dead_public_theorem': 11, 'hypothesis_bridge_surface': 2}` | `{'V2/dead-public-theorem': 11}` |
| `lean/InfoGeometry/Quantum/HestenesKahler.lean` | 304 | 31 | 31 | `{}` | `{'dead_public_theorem': 31}` | `{'V2/dead-public-theorem': 31}` |
| `lean/InfoGeometry/Canonical/TransportLieDerivative.lean` | 302 | 28 | 28 | `{}` | `{'internal_staging_only': 2, 'dead_public_theorem': 26}` | `{'V0/syntactic-vacuity': 2, 'V2/dead-public-theorem': 26}` |
| `lean/InfoGeometry/Canonical/SinkhornFoundation.lean` | 300 | 25 | 25 | `{}` | `{'dead_public_theorem': 25}` | `{'V2/dead-public-theorem': 25}` |
| `lean/InfoGeometry/Thermal/FiniteMatrix.lean` | 298 | 25 | 25 | `{}` | `{'dead_public_theorem': 25}` | `{'V2/dead-public-theorem': 25}` |
| `lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean` | 285 | 30 | 30 | `{}` | `{'wrapper_surface': 1, 'dead_public_theorem': 18, 'hypothesis_bridge_surface': 4, 'package_reprojection_surface': 7}` | `{'V1/public-wrapper-inflation': 1, 'V2/dead-public-theorem': 19}` |
| `lean/InfoGeometry/Quantum/ModularAnomaly.lean` | 284 | 24 | 24 | `{}` | `{'dead_public_theorem': 23, 'wrapper_surface': 1}` | `{'V2/dead-public-theorem': 24, 'V1/public-wrapper-inflation': 1}` |
| `lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean` | 281 | 22 | 22 | `{}` | `{'dead_public_theorem': 16, 'package_reprojection_surface': 6}` | `{'V2/dead-public-theorem': 16}` |
| `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean` | 275 | 23 | 23 | `{}` | `{'dead_public_theorem': 20, 'package_reprojection_surface': 3}` | `{'V2/dead-public-theorem': 20}` |
| `lean/InfoGeometry/Canonical/NavierStokesBridge.lean` | 267 | 23 | 23 | `{}` | `{'dead_public_theorem': 20, 'package_reprojection_surface': 2, 'surrogate_surface': 1}` | `{'V2/dead-public-theorem': 20}` |
| `lean/InfoGeometry/Geometry/DualFlat.lean` | 267 | 21 | 21 | `{}` | `{'dead_public_theorem': 17, 'wrapper_surface': 1, 'package_reprojection_surface': 3}` | `{'V2/dead-public-theorem': 18, 'V1/public-wrapper-inflation': 1}` |
| `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean` | 266 | 26 | 26 | `{}` | `{'dead_public_theorem': 25, 'wrapper_surface': 1}` | `{'V2/dead-public-theorem': 26, 'V1/public-wrapper-inflation': 1}` |
| `lean/InfoGeometry/Canonical/RestrictedSheetContinuous.lean` | 264 | 24 | 24 | `{}` | `{'dead_public_theorem': 24}` | `{'V2/dead-public-theorem': 24}` |
| `lean/InfoGeometry/Canonical/ConformalProjectorCore.lean` | 262 | 23 | 23 | `{}` | `{'package_reprojection_surface': 7, 'dead_public_theorem': 16}` | `{'V2/dead-public-theorem': 16}` |
| `lean/InfoGeometry/Canonical/GenerativeInferenceCore.lean` | 257 | 22 | 22 | `{}` | `{'package_reprojection_surface': 11, 'dead_public_theorem': 11}` | `{'V2/dead-public-theorem': 11}` |
| `lean/InfoGeometry/Canonical/IBUpdate.lean` | 256 | 23 | 23 | `{}` | `{'dead_public_theorem': 20, 'package_reprojection_surface': 2, 'hypothesis_bridge_surface': 1}` | `{'V2/dead-public-theorem': 20}` |

## Top Declarations

### `InfoGeometry.Canonical.HyperbolicRotor.rotor_lane_head_null_car`
- file: `lean/InfoGeometry/Canonical/HyperbolicRotor.lean:99`
- kind/category/class/depth: `theorem` / `package_reprojection` / `wrapper_surface` / `None`
- score: `22`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.SplitCliffordHeadSuperBracket.head_null_car_algebra']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`
- signals: `['context:packaging']`

### `InfoGeometry.Canonical.exists_moorePenroseInverse_endomorphism_of_isUnit`
- file: `lean/InfoGeometry/Canonical/Singular.lean:216`
- kind/category/class/depth: `theorem` / `surrogate_or_vacuous` / `wrapper_surface` / `None`
- score: `22`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`
- signals: `['context:surrogate']`

### `InfoGeometry.Canonical.SplitCliffordTensorBridge.doubledHeadAtom_supergradedLiePackage_root`
- file: `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:78`
- kind/category/class/depth: `theorem` / `package_reprojection` / `wrapper_surface` / `None`
- score: `22`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`
- signals: `['context:packaging']`

### `InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis_eq_dilationOperator`
- file: `lean/InfoGeometry/Canonical/DensityWeightIntertwinerBridge.lean:143`
- kind/category/class/depth: `theorem` / `likely_constructive` / `bridge_surface_promoted` / `None`
- score: `20`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `1`
- external support targets: `1` total -> `['InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_dilationOperator']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V4/bridge-infrastructure-promoted']`
- significance tags: `['proof-infrastructure', 'wrapper-candidate']`

### `InfoGeometry.LLM.KMSSoftmaxBridge.kmsLogPartition_eq_logSumExpRouter`
- file: `lean/InfoGeometry/LLM/KMSSoftmaxBridge.lean:76`
- kind/category/class/depth: `theorem` / `likely_constructive` / `bridge_surface_promoted` / `None`
- score: `20`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `1`
- external support targets: `1` total -> `['InfoGeometry.LLM.RouterFreeEnergyBridge.routerMassieu_eq_logSumExpRouter']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V4/bridge-infrastructure-promoted']`
- significance tags: `['proof-infrastructure', 'wrapper-candidate']`

### `InfoGeometry.measurable_potential_p`
- file: `lean/InfoGeometry/Basic.lean:76`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovClosedForms.JBoost_eq_cosh_add_sinh_modular_j`
- file: `lean/InfoGeometry/Canonical/BogoliubovClosedForms.lean:183`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovClosedForms.epsilonBoost_eq_cosh_add_sinh_spectral_epsilon`
- file: `lean/InfoGeometry/Canonical/BogoliubovClosedForms.lean:197`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovClosedForms.KRotation_eq_cos_add_sin_complex_i`
- file: `lean/InfoGeometry/Canonical/BogoliubovClosedForms.lean:211`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovClosedForms.spectral_epsilon_comp_epsilonBoost`
- file: `lean/InfoGeometry/Canonical/BogoliubovClosedForms.lean:335`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovClosedForms.spectral_epsilon_comp_JBoost`
- file: `lean/InfoGeometry/Canonical/BogoliubovClosedForms.lean:353`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovClosedForms.spectral_epsilon_comp_KRotation`
- file: `lean/InfoGeometry/Canonical/BogoliubovClosedForms.lean:371`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovProjectorFlux.JBoost_comp_spectralPlusProj_modular_j`
- file: `lean/InfoGeometry/Canonical/BogoliubovProjectorFlux.lean:88`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovProjectorFlux.JBoost_comp_spectralMinusProj_modular_j`
- file: `lean/InfoGeometry/Canonical/BogoliubovProjectorFlux.lean:107`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovProjectorFlux.KRotation_comp_spectralPlusProj_complex_i`
- file: `lean/InfoGeometry/Canonical/BogoliubovProjectorFlux.lean:126`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovProjectorFlux.KRotation_comp_spectralMinusProj_complex_i`
- file: `lean/InfoGeometry/Canonical/BogoliubovProjectorFlux.lean:145`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovProjectorFlux.plusProjectorFlux_JBoost_modular_j`
- file: `lean/InfoGeometry/Canonical/BogoliubovProjectorFlux.lean:244`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovProjectorFlux.minusProjectorFlux_JBoost_modular_j`
- file: `lean/InfoGeometry/Canonical/BogoliubovProjectorFlux.lean:266`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovProjectorFlux.plusProjectorFlux_KRotation_complex_i`
- file: `lean/InfoGeometry/Canonical/BogoliubovProjectorFlux.lean:288`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovProjectorFlux.minusProjectorFlux_KRotation_complex_i`
- file: `lean/InfoGeometry/Canonical/BogoliubovProjectorFlux.lean:310`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovProjectorTransport.spectral_epsilon_comp_spectralPlusProj`
- file: `lean/InfoGeometry/Canonical/BogoliubovProjectorTransport.lean:36`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovProjectorTransport.spectral_epsilon_comp_spectralMinusProj`
- file: `lean/InfoGeometry/Canonical/BogoliubovProjectorTransport.lean:51`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovProjectorTransport.spectralPlusProj_comp_spectral_epsilon`
- file: `lean/InfoGeometry/Canonical/BogoliubovProjectorTransport.lean:65`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.BogoliubovProjectorTransport.spectralMinusProj_comp_spectral_epsilon`
- file: `lean/InfoGeometry/Canonical/BogoliubovProjectorTransport.lean:80`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.CliffordBridge.splitQuadratic_eq_gaugeQuadratic`
- file: `lean/InfoGeometry/Canonical/CliffordBridge.lean:14`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.CliffordBridge.splitBilinear_eq_gaugeBilinear`
- file: `lean/InfoGeometry/Canonical/CliffordBridge.lean:26`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.HeadTrialityCore.splitDoubled128_dimension`
- file: `lean/InfoGeometry/Canonical/HeadTrialityCore.lean:127`
- kind/category/class/depth: `theorem` / `package_reprojection` / `dead_public_theorem` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V0/syntactic-vacuity', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'rfl-like']`
- signals: `['context:packaging']`

### `InfoGeometry.Canonical.IBFinitePythagorean.finiteWeightedKL_bind_marginal_decomposition_fullSupport`
- file: `lean/InfoGeometry/Canonical/IBFinitePythagorean.lean:757`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.MajoranaKreinCartanSplit.projectiveDynamics_tomitaAtomSeed_J_comp_eps`
- file: `lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean:63`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.ProjectiveDynamics.J_comp_epsilon']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.MajoranaKreinCartanSplit.projectiveDynamics_tomitaAtomSeed_commute`
- file: `lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean:71`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.ProjectiveDynamics.J_epsilon_commute']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.ModularOrientationContract.canonical_phaseAxis_eq_modular_j_comp_spectral_epsilon`
- file: `lean/InfoGeometry/Canonical/ModularOrientationContract.lean:54`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.OperatorDictionary.phaseAxisK_eq_modular_j_comp_spectral_epsilon']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.ModularOrientationContract.orientationFlip_swaps_vacuum_polarizations_plus`
- file: `lean/InfoGeometry/Canonical/ModularOrientationContract.lean:123`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Krein.Prelude.vacuumChoice_switch_swaps_polarizations_plus']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.ModularOrientationContract.orientationFlip_swaps_vacuum_polarizations_minus`
- file: `lean/InfoGeometry/Canonical/ModularOrientationContract.lean:134`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Krein.Prelude.vacuumChoice_switch_swaps_polarizations_minus']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.ModularVolumeDeformationBridge.scalar_modularPotential_is_neg_log`
- file: `lean/InfoGeometry/Canonical/ModularVolumeDeformationBridge.lean:92`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential_eq_neg_log']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.OnsagerCasimirJ.complex_i_comp_modularConjugationJ`
- file: `lean/InfoGeometry/Canonical/OnsagerCasimirJ.lean:60`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.OperatorAlgebraBridge.modular_atom_is_cl11_root`
- file: `lean/InfoGeometry/Canonical/OperatorAlgebraModularAtom.lean:28`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Krein.modular_j_spectral_epsilon_is_cl11']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.OperatorDictionary.modular_j_comp_spectral_epsilon_eq_neg_spectral_epsilon_comp_modular_j`
- file: `lean/InfoGeometry/Canonical/OperatorDictionary.lean:83`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Krein.modular_j_spectral_epsilon_anticommute']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator`
- file: `lean/InfoGeometry/Canonical/PhaseSpaceCausalFlowBridge.lean:45`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge.toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge.toDoubledCopyRho_comp_phasePlusProjector_eq_KKT_plusProjector`
- file: `lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean:43`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.KKTGeneralizedMetricBridge.toDoubledCopyRho_comp_phasePlusProjector_eq_canonical_plusProjector']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge.toDoubledCopyRho_comp_phaseMinusProjector_eq_KKT_minusProjector`
- file: `lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean:52`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.KKTGeneralizedMetricBridge.toDoubledCopyRho_comp_phaseMinusProjector_eq_canonical_minusProjector']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator`
- file: `lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean:42`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge.toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_concreteCAR`
- file: `lean/InfoGeometry/Canonical/RealBdGDIIIAtom.lean:260`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.SuperchargeCARCCRBridge.concrete_car_minus_plus']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.SplitCliffordHeadProjectors.headEpsProjectorTensor_sum`
- file: `lean/InfoGeometry/Canonical/SplitCliffordHeadProjectors.lean:40`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.SplitCliffordHeadPolarization.headMinusSectorTensor_add_headPlusSectorTensor']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.SplitCliffordHeadProjectors.headEpsMinusProjectorTensor_mul_headEpsPlusProjectorTensor`
- file: `lean/InfoGeometry/Canonical/SplitCliffordHeadProjectors.lean:45`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.SplitCliffordHeadPolarization.headMinusSectorTensor_mul_headPlusSectorTensor']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.SplitCliffordHeadProjectors.headEpsPlusProjectorTensor_mul_headEpsMinusProjectorTensor`
- file: `lean/InfoGeometry/Canonical/SplitCliffordHeadProjectors.lean:50`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.SplitCliffordHeadPolarization.headPlusSectorTensor_mul_headMinusSectorTensor']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.SplitCliffordHeadProjectors.headEpsMinusProjectorTensor_idempotent`
- file: `lean/InfoGeometry/Canonical/SplitCliffordHeadProjectors.lean:55`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.SplitCliffordHeadPolarization.headMinusSectorTensor_idempotent']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.SplitCliffordHeadProjectors.headEpsPlusProjectorTensor_idempotent`
- file: `lean/InfoGeometry/Canonical/SplitCliffordHeadProjectors.lean:60`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.SplitCliffordHeadPolarization.headPlusSectorTensor_idempotent']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.SplitCliffordHeadProjectors.headEpsTensor_mul_headEpsMinusProjectorTensor`
- file: `lean/InfoGeometry/Canonical/SplitCliffordHeadProjectors.lean:65`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.SplitCliffordHeadPolarization.headEpsTensor_mul_headMinusSectorTensor']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.SplitCliffordHeadProjectors.headEpsMinusProjectorTensor_mul_headEpsTensor`
- file: `lean/InfoGeometry/Canonical/SplitCliffordHeadProjectors.lean:69`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.SplitCliffordHeadPolarization.headMinusSectorTensor_mul_headEpsTensor']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.SplitCliffordHeadProjectors.headEpsTensor_mul_headEpsPlusProjectorTensor`
- file: `lean/InfoGeometry/Canonical/SplitCliffordHeadProjectors.lean:73`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.SplitCliffordHeadPolarization.headEpsTensor_mul_headPlusSectorTensor']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.SplitCliffordHeadProjectors.headEpsPlusProjectorTensor_mul_headEpsTensor`
- file: `lean/InfoGeometry/Canonical/SplitCliffordHeadProjectors.lean:77`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.SplitCliffordHeadPolarization.headPlusSectorTensor_mul_headEpsTensor']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.TomitaTakesaki.modularFlow_reversal`
- file: `lean/InfoGeometry/Canonical/TomitaTakesaki.lean:544`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.TransportedSuperchargePackage.transported_primitive_anticommutator_zero`
- file: `lean/InfoGeometry/Canonical/UnifiedSuperchargeAlgebra.lean:219`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.SuperchargeTransportBridge.parity_modular_anticommutator_eq_zero']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.VortexAnomalyLink.canonicalSourceBoundarySupercharge_projectedNilpotent`
- file: `lean/InfoGeometry/Canonical/VortexAnomalyLink.lean:179`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.VortexAnomalyLink.canonicalSinkBoundarySupercharge_projectedNilpotent`
- file: `lean/InfoGeometry/Canonical/VortexAnomalyLink.lean:186`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.WedgeBoostModularBridge.modularTime_roundtrip`
- file: `lean/InfoGeometry/Canonical/WedgeBoostModularBridge.lean:66`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.RealTomitaCore.modularTimeOfWedgeBoost_wedgeBoostParameter']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Canonical.Determinant.capstone_logAbsVolume_add_from_zeta`
- file: `lean/InfoGeometry/Canonical/ZetaDeterminant.lean:181`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Clifford.ClNNSpecialization.gamma_rankOne_headNullMinus_sq`
- file: `lean/InfoGeometry/Clifford/ClNNSpecialization.lean:99`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Clifford.ClNN.gammaHeadNullMinus_sq']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Clifford.ClNNSpecialization.gamma_rankOne_headNullPlus_sq`
- file: `lean/InfoGeometry/Clifford/ClNNSpecialization.lean:103`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Clifford.ClNN.gammaHeadNullPlus_sq']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.CliffordTower.Q11_apply`
- file: `lean/InfoGeometry/Clifford/Tower.lean:18`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Clifford.splitQ11_apply']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.ConvexDuality.bregman_nonneg_of_convex`
- file: `lean/InfoGeometry/Convex/Duality.lean:81`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.ConvexDuality.KL_param_nonneg_of_convex`
- file: `lean/InfoGeometry/Convex/Duality.lean:99`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.cramerRateOn_singleton`
- file: `lean/InfoGeometry/Cramer.lean:75`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Convex.OneD.bregmanDiv_three_point`
- file: `lean/InfoGeometry/Fenchel.lean:24`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.bregmanThreePoint']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Geometry.convex_iff_eGeodesicConvex`
- file: `lean/InfoGeometry/Geometry/DualFlat.lean:113`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Geometry.krein_hessian_sq`
- file: `lean/InfoGeometry/Geometry/KreinAsHessian.lean:39`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Krein.spectral_epsilon_involution']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Geometry.krein_form_self_to_doubled_real`
- file: `lean/InfoGeometry/Geometry/KreinAsHessian.lean:105`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Krein.SplitCliffordNN.gamma_head_null_car`
- file: `lean/InfoGeometry/Krein/SplitCliffordNN.lean:45`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Clifford.ClNN.gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.LLM.AllTopThermodynamicRouter.allTop_entropy_eq_beta_internal_plus_massieu`
- file: `lean/InfoGeometry/LLM/AllTopThermodynamicRouter.lean:69`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.LLM.RouterFreeEnergyBridge.routerEntropy_eq_beta_internal_plus_massieu']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.LLM.AllTopThermodynamicRouter.allTop_beta_mul_freeEnergy_eq_neg_massieu`
- file: `lean/InfoGeometry/LLM/AllTopThermodynamicRouter.lean:79`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.LLM.RouterFreeEnergyBridge.beta_mul_routerFreeEnergy_eq_neg_routerMassieu']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.LLM.HypothesisScaffold70.h70_krein_energy_surface`
- file: `lean/InfoGeometry/LLM/HypothesisScaffold70.lean:53`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.LLM.KreinAttentionEnergy.kreinInteractionEnergy_eq_neg_splitB11']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.LLM.RouterFreeEnergyBridge.routerScaledPotentialGap_eq_scaledBregman`
- file: `lean/InfoGeometry/LLM/RouterFreeEnergyBridge.lean:159`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.LLM.ScalarThermoBridge.switchMatrix_mem_rowStochastic_bridge`
- file: `lean/InfoGeometry/LLM/ScalarThermoBridge.lean:114`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Canonical.MoE.switchMatrix_mem_rowStochastic']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Math.Convexity.kl_convexity_finite`
- file: `lean/InfoGeometry/Math/Convexity.lean:43`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Measure.RadonNikodymNormalForms.rnDeriv_singleton_eq_mass_ratio`
- file: `lean/InfoGeometry/Measure/RadonNikodymNormalForms.lean:76`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Measure.DiscreteRN.rnDeriv_eq_div_of_singleton']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Measure.RadonNikodymNormalForms.rnDeriv_pmf_eq_pointwise_ratio`
- file: `lean/InfoGeometry/Measure/RadonNikodymNormalForms.lean:87`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Measure.DiscreteRN.rnDeriv_pmf_eq_div']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Projective.logSumInequality`
- file: `lean/InfoGeometry/Projective/LogSumIneq.lean:12`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Projective.logSum_inequality']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Quantum.GeometricQuantumTensor.complex_i_star_eq_neg`
- file: `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean:1341`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Quantum.ModularAnomaly.Lattice.invariant_parity_index`
- file: `lean/InfoGeometry/Quantum/ModularAnomaly.lean:960`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

### `InfoGeometry.Quantum.canonicalSuperchargeMultiplet.parity_hamiltonian_eq_id`
- file: `lean/InfoGeometry/Quantum/SuperchargeMultiplet.lean:153`
- kind/category/class/depth: `theorem` / `likely_constructive` / `wrapper_surface` / `None`
- score: `18`
- substantive consumers: `0`
- facade consumers: `0`
- local consumers: `0`
- external support targets: `1` total -> `['InfoGeometry.Quantum.canonicalSplitTrialityKernel.paritySupercharge_hamiltonian_eq_id']`
- vacuity codes: `['V1/public-wrapper-inflation', 'V2/dead-public-theorem']`
- significance tags: `['dead-candidate', 'wrapper-candidate']`

