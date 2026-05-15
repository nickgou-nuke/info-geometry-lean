# Functorial Invariance Audit

- Status: **PASS**
- Root declarations: `4174`
- Root declarations with canopy consumers: `318`
- Root declarations with rep-depth tags: `22`
- Untagged root declarations: `4152`
- Untagged root declarations with canopy consumers: `301`
- Isomorphism corridors (equiv/iso/simplex/projective): `26`
- Simplex/projective corridors: `4`

Tag coverage is informational only; PASS/FAIL is decided by
Core→canopy functorial connectivity and corridor checks, not by tag density.

## Root File Coverage

| File | Root Decls | Reaching Canopy |
|---|---:|---:|
| `lean/InfoGeometry/Geometry/BilingualPoincareMetric.lean` | 303 | 0 |
| `lean/InfoGeometry/Geometry/EntanglementGeometry.lean` | 277 | 0 |
| `lean/InfoGeometry/Geometry/BilingualAnalyticity.lean` | 247 | 9 |
| `lean/InfoGeometry/Geometry/SpectralDivisors.lean` | 172 | 0 |
| `lean/InfoGeometry/Geometry/ConstructiveKasparov.lean` | 163 | 0 |
| `lean/InfoGeometry/Core/SymmetricLie.lean` | 161 | 18 |
| `lean/InfoGeometry/Geometry/ChiralTubuleBoundary.lean` | 147 | 19 |
| `lean/InfoGeometry/Geometry/AnomalousErlangerHeight.lean` | 146 | 0 |
| `lean/InfoGeometry/Geometry/OpticalJonesV4.lean` | 137 | 0 |
| `lean/InfoGeometry/Geometry/DualFlat.lean` | 132 | 24 |
| `lean/InfoGeometry/MaxEnt/Jaynes.lean` | 120 | 0 |
| `lean/InfoGeometry/Geometry/ErlangerPhaseGeometry.lean` | 102 | 0 |
| `lean/InfoGeometry/Geometry/BerezinianCayleyVolume.lean` | 99 | 0 |
| `lean/InfoGeometry/Geometry/PhaseErlanger.lean` | 99 | 0 |
| `lean/InfoGeometry/Core/Involution.lean` | 95 | 9 |
| `lean/InfoGeometry/Geometry/OperatorBregmanDivergence.lean` | 87 | 11 |
| `lean/InfoGeometry/MaxEnt/JaynesInfoStatMech.lean` | 83 | 5 |
| `lean/InfoGeometry/Core/UnifiedGeometry.lean` | 82 | 5 |
| `lean/InfoGeometry/Core/SymmetricLieGeneric.lean` | 81 | 6 |
| `lean/InfoGeometry/MaxEnt/Finite.lean` | 79 | 25 |
| `lean/InfoGeometry/Geometry/OperatorialJonesConnection.lean` | 77 | 0 |
| `lean/InfoGeometry/Geometry/RealRotorCore.lean` | 72 | 0 |
| `lean/InfoGeometry/Convex/HessianGeometry.lean` | 70 | 18 |
| `lean/InfoGeometry/Convex/Legendre.lean` | 62 | 15 |
| `lean/InfoGeometry/Geometry/DiscreteModularSubgroup.lean` | 60 | 0 |
| `lean/InfoGeometry/Geometry/LegendreHessianInverse.lean` | 57 | 36 |
| `lean/InfoGeometry/Geometry/WindingSnap.lean` | 54 | 0 |
| `lean/InfoGeometry/Geometry/BilingualUpperHalfPlane.lean` | 52 | 0 |
| `lean/InfoGeometry/MaxEnt/Core.lean` | 48 | 3 |
| `lean/InfoGeometry/Geometry/KreinIsotropicCone.lean` | 47 | 0 |

## Corridor Samples

| Root Decl | Canopy Decl | Depth | Root File | Canopy File |
|---|---|---:|---|---|
| `InfoGeometry.Convex.BregmanDivergence.mk` | `InfoGeometry.Canonical.BregmanTriality.softmaxBregmanAttention` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/BregmanTriality.lean` |
| `InfoGeometry.Convex.Euclidean.scaledHessianGeometry` | `InfoGeometry.Canonical.DiagonalMetricModularBridge.countDiagonalHessianGeometry` | 1 | `lean/InfoGeometry/Convex/Euclidean.lean` | `lean/InfoGeometry/Canonical/DiagonalMetricModularBridge.lean` |
| `InfoGeometry.Convex.Euclidean.scaledHessianGeometry_metricOp_eq_smul_id` | `InfoGeometry.Canonical.DiagonalMetricModularBridge.countDiagonalHessianGeometryOfRelativeCountDensitySumBound_metricOp_eq_countModularHamiltonian` | 1 | `lean/InfoGeometry/Convex/Euclidean.lean` | `lean/InfoGeometry/Canonical/DiagonalMetricModularBridge.lean` |
| `InfoGeometry.Convex.HessianGeometry` | `InfoGeometry.Canonical.CalabiYauBridge.HasConstantMongeAmpereDensity` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/CalabiYauMetricRicci.lean` |
| `InfoGeometry.Convex.HessianGeometry.divergence` | `InfoGeometry.Canonical.SpectralInference.bayesianAction` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/SpectralInference.lean` |
| `InfoGeometry.Convex.HessianGeometry.divergence_nonneg` | `InfoGeometry.Canonical.SpectralInference.bayesianAction_nonneg` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/SpectralInference.lean` |
| `InfoGeometry.Convex.HessianGeometry.dualMap` | `InfoGeometry.Canonical.QFTTDFTLaunchpad.RungeGrossStationaryDualState` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/QFTTDFTLaunchpad.lean` |
| `InfoGeometry.Convex.HessianGeometry.grad` | `InfoGeometry.Canonical.RGFlow.dualDeriv_constantFlow` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/RGFlow.lean` |
| `InfoGeometry.Convex.HessianGeometry.metric` | `InfoGeometry.Canonical.CalabiYauBridge.isRicciFlat_of_unitRelativeVolume` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/CalabiYauMetricRicci.lean` |
| `InfoGeometry.Convex.HessianGeometry.metricOp` | `InfoGeometry.Canonical.CalabiYauBridge.metricLogDet_eq_zero_of_unitRelativeVolume` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/CalabiYauMetricRicci.lean` |
| `InfoGeometry.Convex.HessianGeometry.metricOp_isSymmetric` | `InfoGeometry.Canonical.DiracMetricCompatibility.ofMetric` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/DiracMetricCompatibility.lean` |
| `InfoGeometry.Convex.HessianGeometry.metric_quadratic_nonneg` | `InfoGeometry.Canonical.DiracMetricCompatibility.ofMetric` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/DiracMetricCompatibility.lean` |
| `InfoGeometry.Convex.HessianGeometry.potential` | `InfoGeometry.Canonical.AnomalyInflow.AnomalyInflowClosure` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/AnomalyInflow.lean` |
| `InfoGeometry.Convex.LegendrePotential` | `InfoGeometry.Canonical.SouriauTheoremTranslatorPacket.claimD_scalarLegendre_inverseHessian_eq_inv_fisher` | 1 | `lean/InfoGeometry/Convex/Legendre.lean` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean` |
| `InfoGeometry.Convex.LegendrePotential.bregman` | `InfoGeometry.Thermo.KL_param_eq_bregman_energy` | 1 | `lean/InfoGeometry/Convex/Legendre.lean` | `lean/InfoGeometry/Thermo/FromBregman.lean` |
| `InfoGeometry.Convex.LegendrePotential.eta` | `InfoGeometry.Canonical.SouriauTheoremTranslatorPacket.claimD_scalarLegendre_inverseHessian_eq_inv_fisher` | 1 | `lean/InfoGeometry/Convex/Legendre.lean` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean` |
| `InfoGeometry.Convex.LegendrePotential.f` | `InfoGeometry.Thermo.KL_param_eq_bregman_energy` | 1 | `lean/InfoGeometry/Convex/Legendre.lean` | `lean/InfoGeometry/Thermo/FromBregman.lean` |
| `InfoGeometry.Convex.LegendrePotential.fisher` | `InfoGeometry.Canonical.SouriauTheoremTranslatorPacket.claimD_scalarLegendre_inverseHessian_eq_inv_fisher` | 1 | `lean/InfoGeometry/Convex/Legendre.lean` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean` |
| `InfoGeometry.Convex.LegendrePotential.thetaOfEta` | `InfoGeometry.Canonical.SouriauTheoremTranslatorPacket.claimD_scalarLegendre_inverseHessian_eq_inv_fisher` | 1 | `lean/InfoGeometry/Convex/Legendre.lean` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean` |
| `InfoGeometry.Convex.LegendrePotential.thetaOfEta_deriv_eq_inv_fisher_of_hasDerivAt` | `InfoGeometry.Canonical.SouriauTheoremTranslatorPacket.claimD_scalarLegendre_inverseHessian_eq_inv_fisher` | 1 | `lean/InfoGeometry/Convex/Legendre.lean` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean` |
| `InfoGeometry.Convex.LogSumExp.RN` | `InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights_eq_euclideanAttentionWeights_of_constantKeyNorm` | 1 | `lean/InfoGeometry/Convex/LogSumExp.lean` | `lean/InfoGeometry/Canonical/AttentionPolarizedSplit.lean` |
| `InfoGeometry.Convex.LogSumExp.softmax` | `InfoGeometry.Canonical.Attention.gibbsWeight_polarizedPlusParams_eq_polarizedPlusAttentionWeights` | 1 | `lean/InfoGeometry/Convex/LogSumExp.lean` | `lean/InfoGeometry/Canonical/AttentionPolarizedGibbsBridge.lean` |
| `InfoGeometry.Convex.LogSumExp.softmax_add_uniformShift` | `InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights_eq_euclideanAttentionWeights_of_constantKeyNorm` | 1 | `lean/InfoGeometry/Convex/LogSumExp.lean` | `lean/InfoGeometry/Canonical/AttentionPolarizedSplit.lean` |
| `InfoGeometry.Convex.LogSumExp.sumExp` | `InfoGeometry.Canonical.Attention.gibbsWeight_polarizedPlusParams_eq_polarizedPlusAttentionWeights` | 1 | `lean/InfoGeometry/Convex/LogSumExp.lean` | `lean/InfoGeometry/Canonical/AttentionPolarizedGibbsBridge.lean` |
| `InfoGeometry.Convex.LogSumExp.sum_softmax_eq_one` | `InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights_sum_one` | 1 | `lean/InfoGeometry/Convex/LogSumExp.lean` | `lean/InfoGeometry/Canonical/AttentionPolarizedSplit.lean` |
| `InfoGeometry.Convex.LogSumExp.uniformShift` | `InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights_eq_euclideanAttentionWeights_of_constantKeyNorm` | 1 | `lean/InfoGeometry/Convex/LogSumExp.lean` | `lean/InfoGeometry/Canonical/AttentionPolarizedSplit.lean` |
| `InfoGeometry.Convex.NonzeroDoubledState` | `InfoGeometry.Canonical.ChiralTorsionBridge.UnnormalizedProjectiveState` | 1 | `lean/InfoGeometry/Convex/ProjectiveRays.lean` | `lean/InfoGeometry/Canonical/ChiralTorsionTwistor.lean` |
| `InfoGeometry.Convex.ProjectiveState` | `InfoGeometry.Canonical.ProjectiveAlgebraComparison.epsilon_is_mathlib_involute` | 1 | `lean/InfoGeometry/Convex/ProjectiveRays.lean` | `lean/InfoGeometry/Canonical/ProjectiveAlgebraComparison.lean` |
| `InfoGeometry.Convex.bregmanTriadicCore` | `InfoGeometry.Canonical.BregmanTriality.softmaxBregmanAttention` | 1 | `lean/InfoGeometry/Convex/HessianGeometry.lean` | `lean/InfoGeometry/Canonical/BregmanTriality.lean` |
| `InfoGeometry.Convex.projectivize` | `InfoGeometry.Canonical.ProjectiveSplitQ11Realization.projectiveRay_toMathlibProjectivization_fromMathlibProjectivization` | 1 | `lean/InfoGeometry/Convex/ProjectiveRays.lean` | `lean/InfoGeometry/Canonical/ProjectiveSplitQ11Realization.lean` |
