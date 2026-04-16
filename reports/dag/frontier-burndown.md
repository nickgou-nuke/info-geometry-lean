# Frontier Burn-Down Order

Scope:
- source set: top frontier hotspot modules selected from the theorem-surface frontier graph
- hotspot selector: module strength (`in_weight + out_weight`) on the frontier module graph
- burn-down selector: weighted replaceable surface mass biased toward downstream support pressure

Formula:
- `replaceable_surface_mass = 4 * surrogate_or_vacuous + 2 * package_reprojection + 1 * hypothesis_bridge`
- `support_pressure = 2 * in_weight + out_weight`
- `burn_down_score = replaceable_surface_mass * log1p(support_pressure)`

## Order

| Rank | Module | Score | Dominant Pressure | Mix (H/P/S) | Strength | Action |
| --- | --- | ---: | --- | ---: | ---: | --- |
| 1 | `InfoGeometry.Core.SymmetricLie` | 770.871 | surrogate_or_vacuous | 2/8/40 | 50 | replace surrogates, then collapse package layer |
| 2 | `InfoGeometry.Meta.ProofShape` | 446.649 | surrogate_or_vacuous | 0/15/20 | 38 | replace surrogates, then collapse package layer |
| 3 | `InfoGeometry.Meta.Admission` | 373.561 | surrogate_or_vacuous | 0/0/23 | 38 | direct constructive replacement |
| 4 | `InfoGeometry.Canonical.DrazinInfiniteCore` | 327.134 | surrogate_or_vacuous | 1/14/12 | 44 | replace surrogates, then collapse package layer |
| 5 | `InfoGeometry.Meta.RegionPolicy` | 323.412 | surrogate_or_vacuous | 0/0/21 | 31 | direct constructive replacement |
| 6 | `InfoGeometry.Canonical.TypeIIIContinuousCoreReal` | 308.012 | surrogate_or_vacuous | 0/12/14 | 32 | replace surrogates, then collapse package layer |
| 7 | `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge` | 306.399 | package_reprojection | 0/26/3 | 75 | replace surrogates, then collapse package layer |
| 8 | `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra` | 268.505 | package_reprojection | 0/31/0 | 52 | collapse package layer |
| 9 | `InfoGeometry.Canonical.SingularBoundaryCorrection` | 264.137 | package_reprojection | 0/32/0 | 38 | collapse package layer |
| 10 | `InfoGeometry.Canonical.ConformalProjectorCore` | 260.609 | package_reprojection | 0/24/0 | 134 | collapse package layer |
| 11 | `InfoGeometry.Canonical.ModularSuperchargeClosure` | 241.159 | package_reprojection | 8/19/2 | 54 | replace surrogates, then collapse package layer |
| 12 | `InfoGeometry.Canonical.SpectralInference` | 192.659 | package_reprojection | 1/24/0 | 30 | construct witnesses behind packaged hypotheses |
| 13 | `InfoGeometry.Quantum.RealMajoranaCategory` | 184.676 | package_reprojection | 0/18/0 | 106 | collapse package layer |
| 14 | `InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge` | 167.706 | package_reprojection | 5/16/0 | 81 | construct witnesses behind packaged hypotheses |
| 15 | `InfoGeometry.Canonical.GenerativeInferenceCore` | 149.409 | package_reprojection | 0/19/0 | 34 | collapse package layer |
| 16 | `InfoGeometry.Canonical.RealBdGDIIIAtom` | 144.608 | package_reprojection | 0/15/0 | 79 | collapse package layer |
| 17 | `InfoGeometry.Canonical.HeadTrialityCore` | 134.342 | package_reprojection | 0/17/0 | 34 | collapse package layer |
| 18 | `InfoGeometry.Canonical.LogDetRadonNikodymMechanism` | 131.461 | package_reprojection | 0/15/0 | 53 | collapse package layer |
| 19 | `InfoGeometry.Physics.DIIISymmetryAtom` | 108.131 | package_reprojection | 0/13/0 | 49 | collapse package layer |
| 20 | `InfoGeometry.Canonical.WeylTransportChiralBridge` | 66.790 | package_reprojection | 0/8/0 | 36 | collapse package layer |

