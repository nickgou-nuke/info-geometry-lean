# Vacuity Planner Report

> Status: `generated/historical report`
> Audited: 2026-05-02
> Note: Treat this as a snapshot. Regenerate before relying on it.
> See: [README.md](../README.md), [docs/README.md](../docs/README.md), [docs/CODEBASE_STATUS.md](../docs/CODEBASE_STATUS.md)

## Boundary

- plannerMode: planning-only
- mutationSurface: False
- automaticReplacement: False
- proofRepair: False
- strictAdmissibilityPrecheck: scaffold-only

## Input Coverage

- theoremSignificanceEntries: 7462
- declarationCount: 8295
- edgeCount: 53644
- ownerEntries: 7
- bridgePayloadFiles: 1
- bridgePayloadObjects: 1

## Normalization Snapshot

### Top exprSemantic head groups

| rank | surface | head | count | confidence |
|---:|---|---|---:|---:|
| 1 | local | Prop | 1 | 0.82 |
| 2 | local | p | 1 | 0.82 |
| 3 | target | p | 1 | 0.82 |

### Top fingerprint groups

| rank | surface | fingerprint | count | confidence |
|---:|---|---|---:|---:|
| 1 | local | shape/v1/head:fvar | 1 | 0.82 |
| 2 | local | shape/v1/head:sort:prop | 1 | 0.82 |
| 3 | target | shape/v1/head:fvar | 1 | 0.82 |

## Ranked Vacuity Candidates

| rank | declaration | score | confidence |
|---|---|---|---|
| 1 | InfoGeometry.Canonical.CliffordBridge.splitBilinear_eq_gaugeBilinear | 0.93 | 0.8495 |
| 2 | InfoGeometry.Canonical.CliffordBridge.splitQuadratic_eq_gaugeQuadratic | 0.93 | 0.8495 |
| 3 | InfoGeometry.Canonical.Determinant.capstone_logAbsVolume_add_from_zeta | 0.93 | 0.8495 |
| 4 | InfoGeometry.Canonical.IBFinitePythagorean.finiteWeightedKL_bind_marginal_decomposition_fullSupport | 0.93 | 0.8495 |
| 5 | InfoGeometry.Canonical.MajoranaKreinCartanSplit.projectiveDynamics_tomitaAtomSeed_J_comp_eps | 0.93 | 0.8495 |

## Ranked Owner Candidates

| rank | ownerFile | score | confidence |
|---|---|---|---|
| 1 | lean/InfoGeometry/Canonical/InformationPartitionCore.lean | 0.93 | 0.72 |
| 2 | lean/InfoGeometry/Canonical/PositiveRayCore.lean | 0.93 | 0.72 |
| 3 | lean/InfoGeometry/Canonical/RelativePotentialCore.lean | 0.93 | 0.72 |

## Ranked Replacement Candidates

| rank | replacementDecl | score | confidence |
|---|---|---|---|
| 1 | InfoGeometry.Canonical.CliffordBridge.B_agrees_with_Gauge_bilinear | 0.5673 | 0.8262 |
| 2 | InfoGeometry.Canonical.CliffordBridge.q_agrees_with_Gauge_quad | 0.5673 | 0.8262 |
| 3 | InfoGeometry.Canonical.Determinant.zetaRegularizedLogVolume_add | 0.558 | 0.8267 |
| 4 | InfoGeometry.Canonical.IBFinitePythagorean.finiteWeightedKL_bind_marginal_decomposition | 0.558 | 0.8267 |
| 5 | InfoGeometry.Canonical.Gauge.bilinear | 0.3813 | 0.7341 |

## Ranked Fingerprint Corridors

| rank | clusterKey | vacuityCount | replacementCount | score | confidence |
|---:|---|---:|---:|---:|---:|
| 1 | fp:none|head:InfoGeometry.Canonical.CliffordBridge.splitBilinear_eq_gaugeBilinear|kind:unknown|arity:?|binder:? | 1 | 0 | 0.419 | 0.8495 |
| 2 | fp:none|head:InfoGeometry.Canonical.CliffordBridge.splitQuadratic_eq_gaugeQuadratic|kind:unknown|arity:?|binder:? | 1 | 0 | 0.419 | 0.8495 |
| 3 | fp:none|head:InfoGeometry.Canonical.Determinant.capstone_logAbsVolume_add_from_zeta|kind:unknown|arity:?|binder:? | 1 | 0 | 0.419 | 0.8495 |
| 4 | fp:none|head:InfoGeometry.Canonical.IBFinitePythagorean.finiteWeightedKL_bind_marginal_decomposition_fullSupport|kind:unknown|arity:?|binder:? | 1 | 0 | 0.419 | 0.8495 |
| 5 | fp:none|head:InfoGeometry.Canonical.MajoranaKreinCartanSplit.projectiveDynamics_tomitaAtomSeed_J_comp_eps|kind:unknown|arity:?|binder:? | 1 | 0 | 0.419 | 0.8495 |

## Ranked Declaration Plans

| rank | candidate | probable_owner | probable_replacement | score | confidence |
|---:|---|---|---|---:|---:|
| 1 | InfoGeometry.Canonical.Determinant.capstone_logAbsVolume_add_from_zeta | lean/InfoGeometry/Canonical/InformationPartitionCore.lean | InfoGeometry.Canonical.Determinant.zetaRegularizedLogVolume_add | 0.5081 | 0.8376 |
| 2 | InfoGeometry.Canonical.IBFinitePythagorean.finiteWeightedKL_bind_marginal_decomposition_fullSupport | lean/InfoGeometry/Canonical/InformationPartitionCore.lean | InfoGeometry.Canonical.IBFinitePythagorean.finiteWeightedKL_bind_marginal_decomposition | 0.5081 | 0.8376 |
| 3 | InfoGeometry.Canonical.CliffordBridge.splitBilinear_eq_gaugeBilinear | lean/InfoGeometry/Canonical/InformationPartitionCore.lean | InfoGeometry.Canonical.CliffordBridge.B_agrees_with_Gauge_bilinear | 0.495 | 0.833 |
| 4 | InfoGeometry.Canonical.CliffordBridge.splitQuadratic_eq_gaugeQuadratic | lean/InfoGeometry/Canonical/InformationPartitionCore.lean | InfoGeometry.Canonical.CliffordBridge.q_agrees_with_Gauge_quad | 0.495 | 0.833 |
| 5 | InfoGeometry.Canonical.MajoranaKreinCartanSplit.projectiveDynamics_tomitaAtomSeed_J_comp_eps | lean/InfoGeometry/Canonical/InformationPartitionCore.lean | InfoGeometry.Canonical.Determinant.zetaRegularizedLogVolume_add | 0.4412 | 0.8281 |

## Strict Admissibility Pre-checks

| rank | candidate | replacementDecl | status | score | confidence |
|---:|---|---|---|---:|---:|
| 1 | InfoGeometry.Canonical.Determinant.capstone_logAbsVolume_add_from_zeta | InfoGeometry.Canonical.Determinant.zetaRegularizedLogVolume_add | needs-review | 0.2795 | 0.5863 |
| 2 | InfoGeometry.Canonical.IBFinitePythagorean.finiteWeightedKL_bind_marginal_decomposition_fullSupport | InfoGeometry.Canonical.IBFinitePythagorean.finiteWeightedKL_bind_marginal_decomposition | needs-review | 0.2795 | 0.5863 |
| 3 | InfoGeometry.Canonical.CliffordBridge.splitBilinear_eq_gaugeBilinear | InfoGeometry.Canonical.CliffordBridge.B_agrees_with_Gauge_bilinear | needs-review | 0.2722 | 0.5831 |
| 4 | InfoGeometry.Canonical.CliffordBridge.splitQuadratic_eq_gaugeQuadratic | InfoGeometry.Canonical.CliffordBridge.q_agrees_with_Gauge_quad | needs-review | 0.2722 | 0.5831 |
| 5 | InfoGeometry.Canonical.MajoranaKreinCartanSplit.projectiveDynamics_tomitaAtomSeed_J_comp_eps | InfoGeometry.Canonical.Determinant.zetaRegularizedLogVolume_add | blocked | 0.0882 | 0.2898 |

## Confidence Provenance Weights

- headSourceWeight: {"exprSemantic": 1.0, "textHeuristic": 0.55, "unavailable": 0.2}
- diagnosticProvenanceWeight: {"bridgeRule": 0.6, "fallback": 0.4, "leanTag": 1.0, "messagePattern": 0.75}
- violationLevelWeight: {"error": 1.0, "info": 0.45, "warning": 0.7}

## Planner Policy

- {"admissibilityReplacementWindow": 3, "corridorParticipationDecayModel": "harmonic", "precheckStatusPriority": {"blocked": 0, "needs-review": 1, "provisionally-admissible": 2}, "replacementClusterParticipationLimit": 3, "version": "v1"}
