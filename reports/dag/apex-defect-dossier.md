# Apex Defect Dossiers

Per-apex obstruction profiles on the **SCC-condensed** declaration DAG.
Doctrine: `docs/apex_defect_diagnosis.md`.

## Apex: `InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights`

| Scope | Value |
|---|---|
| Past cone | 5 components |
| Max shell | 2 |
| Forward cone (r=3) | 19 components |
| Dominant judgment | vertical |
| Judgment bag | {'vertical': 1} |
| Max depthNat | 5 |
| depthNat range | [5, 5] |
| Members | 1 |

### Raw Metrics + Severity

| Metric | Raw | Severity |
|---|---|---|
| shell_thinness | 1.0 | - |
| singleton_shell_pressure | 0.5 | **structural** |
| witness_deficit | 1.0 | **structural** |
| non_owner_mediation | 0.0 | - |
| skip_layer_density | 0.0 | - |
| judgment_mismatch_density | 0.0 | - |
| replacement_fragility | 0.0 | - |
| boundary_load | 1.0 | **structural** |

### Metadata Coverage

**4** of 5 cone components (80.0%) are **untagged** (no `@[rep_depth]` annotation).  Role-dependent metrics (non-owner mediation, witness deficit, binding mass) are sensitive to tagging coverage; untagged nodes are metadata-coverage debt, not structural defects.

### Witness Deficit Shells: [1, 2]

### Thin-Shell Chokepoints (sample)

| Representative | Shell | Shell size |
|---|---|---|
| `InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeigh` | 0 | 1 |
| `InfoGeometry.Canonical.Attention.ContextWindow` | 1 | 2 |
| `InfoGeometry.Convex.LogSumExp.softmax` | 1 | 2 |
| `InfoGeometry.Convex.LogSumExp.RN` | 2 | 2 |
| `InfoGeometry.Convex.LogSumExp.sumExp` | 2 | 2 |

### Suggested Read Order

| # | Representative | Shell | Judgment | File |
|---|---|---|---|---|
| 1 | `InfoGeometry.Convex.LogSumExp.sumExp` | 2 | untagged | lean/InfoGeometry/Convex/LogSumExp.lean |
| 2 | `InfoGeometry.Convex.LogSumExp.RN` | 2 | untagged | lean/InfoGeometry/Convex/LogSumExp.lean |
| 3 | `InfoGeometry.Convex.LogSumExp.softmax` | 1 | untagged | lean/InfoGeometry/Convex/LogSumExp.lean |
| 4 | `InfoGeometry.Canonical.Attention.ContextWindow` | 1 | untagged | lean/InfoGeometry/Canonical/Attention.lean |
| 5 | `InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights` | 0 | vertical | lean/InfoGeometry/Canonical/AttentionPolarizedSplit.lean |


## Apex: `InfoGeometry.Canonical.KreinDiracSpectralLift.transportDiracFlow`

| Scope | Value |
|---|---|
| Past cone | 18 components |
| Max shell | 4 |
| Forward cone (r=3) | 4 components |
| Dominant judgment | vertical |
| Judgment bag | {'vertical': 1} |
| Max depthNat | 4 |
| depthNat range | [4, 4] |
| Members | 1 |

### Raw Metrics + Severity

| Metric | Raw | Severity |
|---|---|---|
| shell_thinness | 0.3333 | mild |
| singleton_shell_pressure | 0.5 | **structural** |
| witness_deficit | 1.0 | **structural** |
| non_owner_mediation | 0.0 | - |
| skip_layer_density | 0.0 | - |
| judgment_mismatch_density | 0.0 | - |
| replacement_fragility | 0.75 | **structural** |
| boundary_load | 1.0 | **structural** |

### Metadata Coverage

**17** of 18 cone components (94.4%) are **untagged** (no `@[rep_depth]` annotation).  Role-dependent metrics (non-owner mediation, witness deficit, binding mass) are sensitive to tagging coverage; untagged nodes are metadata-coverage debt, not structural defects.

### Thin Transitions

| From shell | To shell | Size from | Size to | Ratio |
|---|---|---|---|---|
| 3 | 4 | 3 | 1 | 0.3333 |

### Witness Deficit Shells: [1, 2, 3, 4]

### Thin-Shell Chokepoints (sample)

| Representative | Shell | Shell size |
|---|---|---|
| `InfoGeometry.Canonical.KreinDiracSpectralLift.transportDirac` | 0 | 1 |
| `InfoGeometry.Quantum.RealMajorana.EndS` | 4 | 1 |

### Suggested Read Order

| # | Representative | Shell | Judgment | File |
|---|---|---|---|---|
| 1 | `InfoGeometry.Quantum.RealMajorana.EndS` | 4 | untagged | lean/InfoGeometry/Quantum/RealMajorana.lean |
| 2 | `InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform.B` | 3 | untagged | lean/InfoGeometry/Quantum/RealMajorana.lean |
| 3 | `InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform.Binv` | 3 | untagged | lean/InfoGeometry/Quantum/RealMajorana.lean |
| 4 | `InfoGeometry.Canonical.SpectralInference.SpectralTriple` | 3 | untagged | lean/InfoGeometry/Canonical/SpectralInference.lean |
| 5 | `InfoGeometry.Canonical.SpectralInference.InfoSpectralTriple.toSpectralTriple` | 2 | untagged | lean/InfoGeometry/Canonical/SpectralInference.lean |
| 6 | `InfoGeometry.Canonical.KreinDiracPolarizationBridge.transportEnd` | 2 | untagged | lean/InfoGeometry/Canonical/KreinDiracPolarizationBridge.lean |
| 7 | `InfoGeometry.Canonical.KreinDiracSpectralLift.instNormedRingContinuousLinearMapRealIdDoubledSpace` | 2 | untagged | lean/InfoGeometry/Canonical/KreinDiracSpectralLift.lean |
| 8 | `InfoGeometry.Canonical.SpectralInference.SpectralTriple.D` | 2 | untagged | lean/InfoGeometry/Canonical/SpectralInference.lean |
| 9 | `InfoGeometry.Krein.instL2Complete` | 1 | untagged | lean/InfoGeometry/Krein/KreinSpace.lean |
| 10 | `InfoGeometry.Krein.instL2NormedGroup` | 1 | untagged | lean/InfoGeometry/Krein/KreinSpace.lean |
| 11 | `InfoGeometry.Canonical.KreinDiracPolarizationBridge.transportDirac` | 1 | untagged | lean/InfoGeometry/Canonical/KreinDiracPolarizationBridge.lean |
| 12 | `InfoGeometry.Canonical.KreinDiracSpectralLift.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace` | 1 | untagged | lean/InfoGeometry/Canonical/KreinDiracSpectralLift.lean |
| 13 | `InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform` | 1 | untagged | lean/InfoGeometry/Quantum/RealMajorana.lean |
| 14 | `InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum` | 1 | untagged | lean/InfoGeometry/Quantum/RealMajorana.lean |
| 15 | `InfoGeometry.Krein.instL2InnerProduct` | 1 | untagged | lean/InfoGeometry/Krein/KreinSpace.lean |


## Apex: `InfoGeometry.Krein.SplitQuadratic.divergence_eq_half_signed_krein_sq`

| Scope | Value |
|---|---|
| Past cone | 19 components |
| Max shell | 2 |
| Forward cone (r=3) | 11 components |
| Dominant judgment | vertical |
| Judgment bag | {'vertical': 1} |
| Max depthNat | 3 |
| depthNat range | [3, 3] |
| Members | 1 |

### Raw Metrics + Severity

| Metric | Raw | Severity |
|---|---|---|
| shell_thinness | 0.6364 | - |
| singleton_shell_pressure | 0.5 | **structural** |
| witness_deficit | 1.0 | **structural** |
| non_owner_mediation | 0.0 | - |
| skip_layer_density | 0.0 | - |
| judgment_mismatch_density | 0.0 | - |
| replacement_fragility | 0.5 | **structural** |
| boundary_load | 1.0 | **structural** |

### Metadata Coverage

**18** of 19 cone components (94.7%) are **untagged** (no `@[rep_depth]` annotation).  Role-dependent metrics (non-owner mediation, witness deficit, binding mass) are sensitive to tagging coverage; untagged nodes are metadata-coverage debt, not structural defects.

### Witness Deficit Shells: [1, 2]

### Thin-Shell Chokepoints (sample)

| Representative | Shell | Shell size |
|---|---|---|
| `InfoGeometry.Krein.SplitQuadratic.divergence_eq_half_signed_` | 0 | 1 |

### Suggested Read Order

| # | Representative | Shell | Judgment | File |
|---|---|---|---|---|
| 1 | `InfoGeometry.Krein.krein_inner_prod_l2` | 2 | untagged | lean/InfoGeometry/Krein/KreinSpace.lean |
| 2 | `InfoGeometry.Krein.KreinSpace.J_selfAdj` | 2 | untagged | lean/InfoGeometry/Krein/KreinSpace.lean |
| 3 | `InfoGeometry.Krein.KreinSpace.mk` | 2 | untagged | lean/InfoGeometry/Krein/KreinSpace.lean |
| 4 | `InfoGeometry.Krein.KreinSpace` | 2 | untagged | lean/InfoGeometry/Krein/KreinSpace.lean |
| 5 | `InfoGeometry.Krein.signFlipLIE` | 2 | untagged | lean/InfoGeometry/Krein/KreinSpace.lean |
| 6 | `InfoGeometry.Krein.KreinSpace.J` | 2 | untagged | lean/InfoGeometry/Krein/KreinSpace.lean |
| 7 | `InfoGeometry.Krein.spectral_epsilon` | 2 | untagged | lean/InfoGeometry/Krein/DoubledSpace.lean |
| 8 | `InfoGeometry.Krein.SplitQuadratic.potential` | 1 | untagged | lean/InfoGeometry/Krein/SplitQuadratic.lean |
| 9 | `InfoGeometry.Krein.SplitQuadratic.divergence` | 1 | untagged | lean/InfoGeometry/Krein/SplitQuadratic.lean |
| 10 | `InfoGeometry.Krein.instL2Complete` | 1 | untagged | lean/InfoGeometry/Krein/KreinSpace.lean |
| 11 | `InfoGeometry.Krein.SplitQuadratic.grad` | 1 | untagged | lean/InfoGeometry/Krein/SplitQuadratic.lean |
| 12 | `InfoGeometry.Krein.instL2NormedGroup` | 1 | untagged | lean/InfoGeometry/Krein/KreinSpace.lean |
| 13 | `InfoGeometry.Krein.instKreinSpaceProdL2` | 1 | untagged | lean/InfoGeometry/Krein/KreinSpace.lean |
| 14 | `InfoGeometry.Krein.KreinSpace.kreinInner_symm` | 1 | untagged | lean/InfoGeometry/Krein/KreinSpace.lean |
| 15 | `InfoGeometry.Krein.SplitQuadratic.inner_grad_eq_kreinInner` | 1 | untagged | lean/InfoGeometry/Krein/SplitQuadratic.lean |


## Apex: `InfoGeometry.Convex.HessianGeometry.metricOp`

| Scope | Value |
|---|---|
| Past cone | 3 components |
| Max shell | 1 |
| Forward cone (r=3) | 292 components |
| Dominant judgment | vertical |
| Judgment bag | {'vertical': 1} |
| Max depthNat | 2 |
| depthNat range | [2, 2] |
| Members | 1 |

### Raw Metrics + Severity

| Metric | Raw | Severity |
|---|---|---|
| shell_thinness | 2.0 | - |
| singleton_shell_pressure | 1.0 | **structural** |
| witness_deficit | 1.0 | **structural** |
| non_owner_mediation | 0.0 | - |
| skip_layer_density | 0.0 | - |
| judgment_mismatch_density | 0.0 | - |
| replacement_fragility | 0.0 | - |
| boundary_load | 1.0 | **structural** |

### Metadata Coverage

**2** of 3 cone components (66.7%) are **untagged** (no `@[rep_depth]` annotation).  Role-dependent metrics (non-owner mediation, witness deficit, binding mass) are sensitive to tagging coverage; untagged nodes are metadata-coverage debt, not structural defects.

### Witness Deficit Shells: [1]

### Thin-Shell Chokepoints (sample)

| Representative | Shell | Shell size |
|---|---|---|
| `InfoGeometry.Convex.HessianGeometry.metricOp` | 0 | 1 |
| `InfoGeometry.Convex.HessianGeometry` | 1 | 2 |
| `InfoGeometry.Convex.HessianGeometry.grad` | 1 | 2 |

### Suggested Read Order

| # | Representative | Shell | Judgment | File |
|---|---|---|---|---|
| 1 | `InfoGeometry.Convex.HessianGeometry.grad` | 1 | untagged | lean/InfoGeometry/Convex/HessianGeometry.lean |
| 2 | `InfoGeometry.Convex.HessianGeometry` | 1 | untagged | lean/InfoGeometry/Convex/HessianGeometry.lean |
| 3 | `InfoGeometry.Convex.HessianGeometry.metricOp` | 0 | vertical | lean/InfoGeometry/Convex/HessianGeometry.lean |


## Apex: `InfoGeometry.Canonical.PositiveRayCore.logDensity`

| Scope | Value |
|---|---|
| Past cone | 36 components |
| Max shell | 11 |
| Forward cone (r=3) | 64 components |
| Dominant judgment | vertical |
| Judgment bag | {'vertical': 1} |
| Max depthNat | 1 |
| depthNat range | [1, 1] |
| Members | 1 |

### Raw Metrics + Severity

| Metric | Raw | Severity |
|---|---|---|
| shell_thinness | 0.5 | mild |
| singleton_shell_pressure | 0.3636 | mild |
| witness_deficit | 1.0 | **structural** |
| non_owner_mediation | 0.0 | - |
| skip_layer_density | 0.0 | - |
| judgment_mismatch_density | 0.0 | - |
| replacement_fragility | 0.8182 | **structural** |
| boundary_load | 1.0 | **structural** |

### Metadata Coverage

**35** of 36 cone components (97.2%) are **untagged** (no `@[rep_depth]` annotation).  Role-dependent metrics (non-owner mediation, witness deficit, binding mass) are sensitive to tagging coverage; untagged nodes are metadata-coverage debt, not structural defects.

### Thin Transitions

| From shell | To shell | Size from | Size to | Ratio |
|---|---|---|---|---|
| 8 | 9 | 2 | 1 | 0.5 |
| 9 | 10 | 1 | 1 | 1.0 |
| 10 | 11 | 1 | 1 | 1.0 |

### Witness Deficit Shells: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

### Thin-Shell Chokepoints (sample)

| Representative | Shell | Shell size |
|---|---|---|
| `InfoGeometry.Canonical.PositiveRayCore.logDensity` | 0 | 1 |
| `InfoGeometry.Projective.projectiveClassToConeInteriorStateSp` | 7 | 2 |
| `InfoGeometry.Projective.projectiveClassToConeInteriorStateSp` | 7 | 2 |
| `InfoGeometry.PositiveMeasure.ext` | 8 | 2 |
| `InfoGeometry.Projective.interiorToPositiveMeasure` | 8 | 2 |
| `InfoGeometry.PositiveMeasure.ext.match_1` | 9 | 1 |
| `InfoGeometry.PositiveMeasure.casesOn` | 10 | 1 |
| `InfoGeometry.PositiveMeasure.rec` | 11 | 1 |

### Suggested Read Order

| # | Representative | Shell | Judgment | File |
|---|---|---|---|---|
| 1 | `InfoGeometry.PositiveMeasure.rec` | 11 | untagged | lean/InfoGeometry/PositiveMeasure.lean |
| 2 | `InfoGeometry.PositiveMeasure.casesOn` | 10 | untagged | lean/InfoGeometry/PositiveMeasure.lean |
| 3 | `InfoGeometry.PositiveMeasure.ext.match_1` | 9 | untagged | lean/InfoGeometry/PositiveMeasure.lean |
| 4 | `InfoGeometry.Projective.interiorToPositiveMeasure` | 8 | untagged | lean/InfoGeometry/Projective/Bridge.lean |
| 5 | `InfoGeometry.PositiveMeasure.ext` | 8 | untagged | lean/InfoGeometry/PositiveMeasure.lean |
| 6 | `InfoGeometry.Projective.projectiveClassToConeInteriorStateSpace_injective` | 7 | untagged | lean/InfoGeometry/Projective/Bridge.lean |
| 7 | `InfoGeometry.Projective.projectiveClassToConeInteriorStateSpace_surjective` | 7 | untagged | lean/InfoGeometry/Projective/Bridge.lean |
| 8 | `InfoGeometry.PositiveMeasure.mk` | 6 | untagged | lean/InfoGeometry/PositiveMeasure.lean |
| 9 | `InfoGeometry.Projective.projectiveClassToConeInteriorStateSpace_bijective` | 6 | untagged | lean/InfoGeometry/Projective/Bridge.lean |
| 10 | `InfoGeometry.PositiveMeasure.pos` | 6 | untagged | lean/InfoGeometry/PositiveMeasure.lean |
| 11 | `InfoGeometry.Projective.positiveMeasureToEuclidean_apply` | 6 | untagged | lean/InfoGeometry/Projective/Bridge.lean |
| 12 | `InfoGeometry.Projective.projectiveEquivConeInteriorStateSpace` | 5 | untagged | lean/InfoGeometry/Projective/Bridge.lean |
| 13 | `InfoGeometry.Projective.positiveMeasureToEuclidean_scale` | 5 | untagged | lean/InfoGeometry/Projective/Bridge.lean |
| 14 | `InfoGeometry.Projective.positiveMeasureToEuclidean` | 5 | untagged | lean/InfoGeometry/Projective/Bridge.lean |
| 15 | `InfoGeometry.PositiveMeasure.scale` | 5 | untagged | lean/InfoGeometry/PositiveMeasure.lean |


*Computed in 2.8s.*
