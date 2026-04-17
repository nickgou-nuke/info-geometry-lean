# Functorial Invariance Audit

- Status: **PASS**
- Root declarations: `1385`
- Root declarations with canopy consumers: `130`
- Root declarations with rep-depth tags: `1`
- Untagged root declarations: `1384`
- Untagged root declarations with canopy consumers: `129`
- Isomorphism corridors (equiv/iso/simplex/projective): `8`
- Simplex/projective corridors: `4`

Tag coverage is informational only; PASS/FAIL is decided by
Core→canopy functorial connectivity and corridor checks, not by tag density.

## Root File Coverage

| File | Root Decls | Reaching Canopy |
|---|---:|---:|
| `lean/InfoGeometry/Core/SymmetricLie.lean` | 158 | 0 |
| `lean/InfoGeometry/Geometry/DualFlat.lean` | 132 | 21 |
| `lean/InfoGeometry/MaxEnt/Jaynes.lean` | 120 | 0 |
| `lean/InfoGeometry/Core/Involution.lean` | 95 | 0 |
| `lean/InfoGeometry/MaxEnt/JaynesInfoStatMech.lean` | 83 | 5 |
| `lean/InfoGeometry/Core/SymmetricLieGeneric.lean` | 81 | 6 |
| `lean/InfoGeometry/MaxEnt/Finite.lean` | 79 | 25 |
| `lean/InfoGeometry/Core/UnifiedGeometry.lean` | 76 | 5 |
| `lean/InfoGeometry/Convex/HessianGeometry.lean` | 70 | 18 |
| `lean/InfoGeometry/Convex/Legendre.lean` | 61 | 3 |
| `lean/InfoGeometry/MaxEnt/Core.lean` | 48 | 0 |
| `lean/InfoGeometry/Core/SymmetricLieSpaces.lean` | 44 | 0 |
| `lean/InfoGeometry/Core/GrandCanonical.lean` | 42 | 0 |
| `lean/InfoGeometry/MaxEnt/JaynesRNMaxEnt.lean` | 37 | 13 |
| `lean/InfoGeometry/Convex/SelfDualCone.lean` | 33 | 0 |
| `lean/InfoGeometry/Core/SymmetricSpaces.lean` | 31 | 0 |
| `lean/InfoGeometry/Geometry/LegendreDuality.lean` | 28 | 5 |
| `lean/InfoGeometry/Geometry/KreinAsHessian.lean` | 25 | 0 |
| `lean/InfoGeometry/Convex/Euclidean.lean` | 24 | 11 |
| `lean/InfoGeometry/Core/Jordan.lean` | 12 | 0 |
| `lean/InfoGeometry/Convex/FenchelConjugate.lean` | 11 | 0 |
| `lean/InfoGeometry/Convex/LogSumExp.lean` | 11 | 8 |
| `lean/InfoGeometry/Convex/Duality.lean` | 11 | 2 |
| `lean/InfoGeometry/Core/Entropy.lean` | 11 | 0 |
| `lean/InfoGeometry/MaxEnt/DualBridge.lean` | 11 | 0 |
| `lean/InfoGeometry/Convex/ProjectiveRays.lean` | 10 | 4 |
| `lean/InfoGeometry/MaxEnt/Optimality.lean` | 10 | 0 |
| `lean/InfoGeometry/Convex/RadonHelly.lean` | 9 | 0 |
| `lean/InfoGeometry/MaxEnt/IProjection.lean` | 7 | 3 |
| `lean/InfoGeometry/Convex/Bregman.lean` | 6 | 1 |

## Corridor Samples

| Root Decl | Canopy Decl | Depth | Root File | Canopy File |
|---|---|---:|---|---|
| `InfoGeometry.Convex.BregmanDivergence.mk` | `InfoGeometry.Canonical.BregmanTriality.softmaxBregmanAttention` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/BregmanTriality.lean` |
| `InfoGeometry.Convex.Euclidean.scaledHessianGeometry` | `InfoGeometry.Canonical.DiagonalMetricModularBridge.countDiagonalHessianGeometry` | 1 | `lean/InfoGeometry/Convex/Euclidean.lean` | `lean/InfoGeometry/Canonical/DiagonalMetricModularBridge.lean` |
| `InfoGeometry.Convex.Euclidean.scaledHessianGeometry_metricOp_eq_smul_id` | `InfoGeometry.Canonical.DiagonalMetricModularBridge.countDiagonalHessianGeometryOfRelativeCountDensitySumBound_metricOp_eq_countModularHamiltonian` | 1 | `lean/InfoGeometry/Convex/Euclidean.lean` | `lean/InfoGeometry/Canonical/DiagonalMetricModularBridge.lean` |
| `InfoGeometry.Convex.HessianGeometry` | `InfoGeometry.Canonical.BeliefDynamics.exponentialTilt` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/BeliefDynamics.lean` |
| `InfoGeometry.Convex.HessianGeometry.divergence` | `InfoGeometry.Canonical.BeliefDynamics.radonNikodymOp` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/BeliefDynamics.lean` |
| `InfoGeometry.Convex.HessianGeometry.divergence_nonneg` | `InfoGeometry.Canonical.SpectralInference.bayesianAction_nonneg` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/SpectralInference.lean` |
| `InfoGeometry.Convex.HessianGeometry.dualMap` | `InfoGeometry.Canonical.BeliefDynamics.exponentialTilt` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/BeliefDynamics.lean` |
| `InfoGeometry.Convex.HessianGeometry.grad` | `InfoGeometry.Canonical.RGFlow.dualDeriv_constantFlow` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/RGFlow.lean` |
| `InfoGeometry.Convex.HessianGeometry.metric` | `InfoGeometry.Canonical.CalabiYauBridge.isRicciFlat_of_unitRelativeVolume` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/CalabiYauMetricRicci.lean` |
| `InfoGeometry.Convex.HessianGeometry.metricOp` | `InfoGeometry.Canonical.BeliefDynamics.quantumGeometryOp` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/BeliefDynamics.lean` |
| `InfoGeometry.Convex.HessianGeometry.metricOp_isSymmetric` | `InfoGeometry.Canonical.DiracMetricCompatibility.ofMetric` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/DiracMetricCompatibility.lean` |
| `InfoGeometry.Convex.HessianGeometry.metric_quadratic_nonneg` | `InfoGeometry.Canonical.DiracMetricCompatibility.ofMetric` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/DiracMetricCompatibility.lean` |
| `InfoGeometry.Convex.HessianGeometry.potential` | `InfoGeometry.Canonical.AnomalyInflow.AnomalyInflowClosure` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/AnomalyInflow.lean` |
| `InfoGeometry.Convex.LegendrePotential` | `InfoGeometry.Thermo.KL_param_eq_bregman_energy` | 1 | `lean/InfoGeometry/Convex/Legendre.lean` | `lean/InfoGeometry/Thermo/FromBregman.lean` |
| `InfoGeometry.Convex.LegendrePotential.bregman` | `InfoGeometry.Thermo.KL_param_eq_bregman_energy` | 1 | `lean/InfoGeometry/Convex/Legendre.lean` | `lean/InfoGeometry/Thermo/FromBregman.lean` |
| `InfoGeometry.Convex.LegendrePotential.f` | `InfoGeometry.Thermo.KL_param_eq_bregman_energy` | 1 | `lean/InfoGeometry/Convex/Legendre.lean` | `lean/InfoGeometry/Thermo/FromBregman.lean` |
| `InfoGeometry.Convex.LogSumExp.RN` | `InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights_eq_euclideanAttentionWeights_of_constantKeyNorm` | 1 | `lean/InfoGeometry/Convex/LogSumExp.lean` | `lean/InfoGeometry/Canonical/AttentionPolarizedSplit.lean` |
| `InfoGeometry.Convex.LogSumExp.softmax` | `InfoGeometry.Canonical.Attention.gibbsWeight_polarizedPlusParams_eq_polarizedPlusAttentionWeights` | 1 | `lean/InfoGeometry/Convex/LogSumExp.lean` | `lean/InfoGeometry/Canonical/AttentionPolarizedGibbsBridge.lean` |
| `InfoGeometry.Convex.LogSumExp.softmax_add_uniformShift` | `InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights_eq_euclideanAttentionWeights_of_constantKeyNorm` | 1 | `lean/InfoGeometry/Convex/LogSumExp.lean` | `lean/InfoGeometry/Canonical/AttentionPolarizedSplit.lean` |
| `InfoGeometry.Convex.LogSumExp.sumExp` | `InfoGeometry.Canonical.Attention.gibbsWeight_polarizedPlusParams_eq_polarizedPlusAttentionWeights` | 1 | `lean/InfoGeometry/Convex/LogSumExp.lean` | `lean/InfoGeometry/Canonical/AttentionPolarizedGibbsBridge.lean` |
| `InfoGeometry.Convex.LogSumExp.sum_softmax_eq_one` | `InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights_sum_one` | 1 | `lean/InfoGeometry/Convex/LogSumExp.lean` | `lean/InfoGeometry/Canonical/AttentionPolarizedSplit.lean` |
| `InfoGeometry.Convex.LogSumExp.uniformShift` | `InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights_eq_euclideanAttentionWeights_of_constantKeyNorm` | 1 | `lean/InfoGeometry/Convex/LogSumExp.lean` | `lean/InfoGeometry/Canonical/AttentionPolarizedSplit.lean` |
| `InfoGeometry.Convex.NonzeroDoubledState` | `InfoGeometry.Canonical.ChiralTorsionBridge.UnnormalizedProjectiveState` | 1 | `lean/InfoGeometry/Convex/ProjectiveRays.lean` | `lean/InfoGeometry/Canonical/ChiralTorsionTwistor.lean` |
| `InfoGeometry.Convex.ProjectiveState` | `InfoGeometry.Canonical.ProjectiveAlgebraComparison.epsilon_is_mathlib_involute` | 1 | `lean/InfoGeometry/Convex/ProjectiveRays.lean` | `lean/InfoGeometry/Canonical/ProjectiveAlgebraComparison.lean` |
| `InfoGeometry.Convex.bregmanTriadicCore` | `InfoGeometry.Canonical.BregmanTriality.softmaxBregmanAttention` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/BregmanTriality.lean` |
| `InfoGeometry.Convex.projectivize` | `InfoGeometry.Canonical.ProjectiveSplitQ11Realization.strictProjectivize` | 1 | `lean/InfoGeometry/Convex/ProjectiveRays.lean` | `lean/InfoGeometry/Canonical/ProjectiveSplitQ11Realization.lean` |
| `InfoGeometry.Convex.projectivize_smul` | `InfoGeometry.Canonical.ProjectiveSplitQ11Realization.strict_projectivize_eq_of_same_ray` | 1 | `lean/InfoGeometry/Convex/ProjectiveRays.lean` | `lean/InfoGeometry/Canonical/ProjectiveSplitQ11Realization.lean` |
| `InfoGeometry.ConvexDuality.KL_param` | `InfoGeometry.Thermo.KL_param_eq_bregman_energy` | 1 | `lean/InfoGeometry/Convex/Duality.lean` | `lean/InfoGeometry/Thermo/FromBregman.lean` |
| `InfoGeometry.Core.Generic.SymmetricLieAlgebra` | `InfoGeometry.Canonical.NoetherInference.P_minus_conjugate_eq_of_theta_commutes` | 1 | `lean/InfoGeometry/Core/SymmetricLieGeneric.lean` | `lean/InfoGeometry/Canonical/NoetherInference.lean` |
| `InfoGeometry.Core.Generic.SymmetricLieAlgebra.B` | `InfoGeometry.Canonical.NoetherInference.fisher_metric_eq_killing_form_of_orbit_base_relation` | 1 | `lean/InfoGeometry/Core/SymmetricLieGeneric.lean` | `lean/InfoGeometry/Canonical/NoetherInference.lean` |
