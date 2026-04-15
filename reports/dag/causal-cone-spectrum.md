# Causal Cone Spectrum

Per-apex diagnostics on the **SCC-condensed** declaration DAG.
Definitions follow `docs/causal_cone_formal_definitions.md`.

## Apex: `InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights`

| Metric | Value |
|---|---|
| Past cone size | 5 |
| Max shell depth | 2 |
| Forward cone size | 19 |
| Declaration mass | 0.0 |
| Mass contributors | 0 |
| Binding witnesses | 0 |
| Binding mass | 0.0 |
| Boundary nodes | 4 |

### Shell Decomposition

| Shell | Size |
|---|---|
| 0 | 1 |
| 1 | 2 |
| 2 | 2 |

### Boundary Nodes (sample)

| Representative | Shell | Outermost | Low reuse | Low coherence support | Desc in cone | Coh support |
|---|---|---|---|---|---|---|
| `InfoGeometry.Canonical.Attention.ContextWindow` | 1 | False | True | True | 1 | 0 |
| `InfoGeometry.Convex.LogSumExp.softmax` | 1 | False | True | True | 1 | 0 |
| `InfoGeometry.Convex.LogSumExp.RN` | 2 | True | False | True | 2 | 0 |
| `InfoGeometry.Convex.LogSumExp.sumExp` | 2 | True | False | True | 1 | 0 |


## Apex: `InfoGeometry.Canonical.KreinDiracSpectralLift.transportDiracFlow`

| Metric | Value |
|---|---|
| Past cone size | 18 |
| Max shell depth | 4 |
| Forward cone size | 4 |
| Declaration mass | 0.0 |
| Mass contributors | 0 |
| Binding witnesses | 0 |
| Binding mass | 0.0 |
| Boundary nodes | 17 |

### Shell Decomposition

| Shell | Size |
|---|---|
| 0 | 1 |
| 1 | 9 |
| 2 | 4 |
| 3 | 3 |
| 4 | 1 |

### Boundary Nodes (sample)

| Representative | Shell | Outermost | Low reuse | Low coherence support | Desc in cone | Coh support |
|---|---|---|---|---|---|---|
| `InfoGeometry.Canonical.KreinDiracPolarizationBridge.transportDirac` | 1 | False | True | True | 1 | 0 |
| `InfoGeometry.Canonical.KreinDiracSpectralLift.instIsTopologicalRingContinuousLin` | 1 | False | True | True | 1 | 0 |
| `InfoGeometry.Canonical.SpectralInference.InfoSpectralTriple` | 1 | False | False | True | 3 | 0 |
| `InfoGeometry.Krein.DoubledSpace` | 1 | False | False | True | 3 | 0 |
| `InfoGeometry.Krein.instL2Complete` | 1 | False | True | True | 1 | 0 |
| `InfoGeometry.Krein.instL2InnerProduct` | 1 | False | True | True | 1 | 0 |
| `InfoGeometry.Krein.instL2NormedGroup` | 1 | False | False | True | 3 | 0 |
| `InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform` | 1 | False | False | True | 5 | 0 |
| `InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum` | 1 | False | False | True | 6 | 0 |
| `InfoGeometry.Canonical.KreinDiracPolarizationBridge.transportEnd` | 2 | False | True | True | 1 | 0 |


## Apex: `InfoGeometry.Krein.SplitQuadratic.divergence_eq_half_signed_krein_sq`

| Metric | Value |
|---|---|
| Past cone size | 19 |
| Max shell depth | 2 |
| Forward cone size | 13 |
| Declaration mass | 0.0 |
| Mass contributors | 0 |
| Binding witnesses | 0 |
| Binding mass | 0.0 |
| Boundary nodes | 18 |

### Shell Decomposition

| Shell | Size |
|---|---|
| 0 | 1 |
| 1 | 11 |
| 2 | 7 |

### Boundary Nodes (sample)

| Representative | Shell | Outermost | Low reuse | Low coherence support | Desc in cone | Coh support |
|---|---|---|---|---|---|---|
| `InfoGeometry.Krein.DoubledSpace` | 1 | False | False | True | 6 | 0 |
| `InfoGeometry.Krein.KreinSpace.kreinInner` | 1 | False | False | True | 5 | 0 |
| `InfoGeometry.Krein.KreinSpace.kreinInner_symm` | 1 | False | True | True | 1 | 0 |
| `InfoGeometry.Krein.SplitQuadratic.divergence` | 1 | False | True | True | 1 | 0 |
| `InfoGeometry.Krein.SplitQuadratic.grad` | 1 | False | False | True | 3 | 0 |
| `InfoGeometry.Krein.SplitQuadratic.inner_grad_eq_kreinInner` | 1 | False | True | True | 1 | 0 |
| `InfoGeometry.Krein.SplitQuadratic.potential` | 1 | False | False | True | 2 | 0 |
| `InfoGeometry.Krein.instKreinSpaceProdL2` | 1 | False | False | True | 4 | 0 |
| `InfoGeometry.Krein.instL2Complete` | 1 | False | False | True | 5 | 0 |
| `InfoGeometry.Krein.instL2InnerProduct` | 1 | False | False | True | 6 | 0 |


## Apex: `InfoGeometry.Convex.HessianGeometry.metricOp`

| Metric | Value |
|---|---|
| Past cone size | 3 |
| Max shell depth | 1 |
| Forward cone size | 326 |
| Declaration mass | 0.1917 |
| Mass contributors | 2 |
| Binding witnesses | 0 |
| Binding mass | 0.0 |
| Boundary nodes | 2 |

### Shell Decomposition

| Shell | Size |
|---|---|
| 0 | 1 |
| 1 | 2 |

### Boundary Nodes (sample)

| Representative | Shell | Outermost | Low reuse | Low coherence support | Desc in cone | Coh support |
|---|---|---|---|---|---|---|
| `InfoGeometry.Convex.HessianGeometry` | 1 | True | False | True | 2 | 0 |
| `InfoGeometry.Convex.HessianGeometry.grad` | 1 | True | False | True | 1 | 0 |


## Apex: `InfoGeometry.Canonical.PositiveRayCore.logDensity`

| Metric | Value |
|---|---|
| Past cone size | 36 |
| Max shell depth | 11 |
| Forward cone size | 104 |
| Declaration mass | 0.0714 |
| Mass contributors | 1 |
| Binding witnesses | 0 |
| Binding mass | 0.0 |
| Boundary nodes | 35 |

### Shell Decomposition

| Shell | Size |
|---|---|
| 0 | 1 |
| 1 | 3 |
| 2 | 3 |
| 3 | 6 |
| 4 | 7 |
| 5 | 5 |
| 6 | 4 |
| 7 | 2 |
| 8 | 2 |
| 9 | 1 |
| 11 | 1 |
| ... (1 shells omitted) | |

### Boundary Nodes (sample)

| Representative | Shell | Outermost | Low reuse | Low coherence support | Desc in cone | Coh support |
|---|---|---|---|---|---|---|
| `InfoGeometry.Canonical.PositiveRayCore.PositiveRay` | 1 | False | False | True | 2 | 0 |
| `InfoGeometry.Canonical.PositiveRayCore.gaugeSection` | 1 | False | True | True | 1 | 0 |
| `InfoGeometry.PositiveMeasure.mass` | 1 | False | False | True | 9 | 0 |
| `InfoGeometry.PositiveMeasure` | 2 | False | False | True | 24 | 0 |
| `InfoGeometry.PositiveMeasure.Proj` | 2 | False | False | True | 9 | 0 |
| `InfoGeometry.Projective.Normalize.normalizeOnProj` | 2 | False | True | True | 1 | 0 |
| `InfoGeometry.PositiveMeasure.instSetoidReal` | 3 | False | False | True | 4 | 0 |
| `InfoGeometry.Projective.ConeInteriorStateSpace` | 3 | False | False | True | 10 | 0 |
| `InfoGeometry.Projective.Normalize.normalizeOnConeInteriorStateSpace` | 3 | False | True | True | 1 | 0 |
| `InfoGeometry.Projective.SelfDualCone.cone` | 3 | False | False | True | 10 | 0 |


*Computed in 2.5s.*
