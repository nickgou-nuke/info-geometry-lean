# Gravitational Lean Context

- Query: `Souriau Fisher Onsager inverse metric entropy production`
- Graph source: `arango:faithful_raw`
- Nodes: `25947`
- Edges: `1184253`
- Synonym groups: `8`
- Requested layers: `all`
- Promotion allowed: `false`

## Representation Layers

- `unlabeled`: `22555`
- `L0_Count`: `2`; depth `0`; slug `count`
- `L1_Projective`: `193`; depth `1`; slug `projective`
- `L2_Operator`: `724`; depth `2`; slug `operator`
- `L3_Krein`: `1213`; depth `3`; slug `krein`
- `L4_ModularTransport`: `1207`; depth `4`; slug `transport`
- `L5_ThermodynamicClosure`: `53`; depth `5`; slug `thermo`

## Synonym Expansion

- `EQC-0043` matched `entropy, metric, production`; added `total`
- `EQC-0023` matched `entropy, metric, production`; added `curvature, diagonal, operatorial, probe, response, swapped`
- `EQC-0050` matched `entropy, metric, production`; added `metriplectic`
- `EQC-0182` matched `entropy, production`; added `beta`
- `EQC-0036` matched `fisher, metric`; added `eval, state`
- `EQC-0039` matched `entropy, metric`; added `coadjoint, orbit, rate`
- `EQC-0156` matched `inverse, metric`; added `canonical, compose, geometry, grand, identity, info, matrix2`
- `EQC-0101` matched `metric, souriau`; added `algebraic, coordinateless, geometric, kmsbridge, quantum, tensor`

## 1. `InfoGeometry.GrandCanonical.ResponseMatrix2.betaBeta`

- Score: `251.8125`
- Distance: `None`
- Module: `InfoGeometry.GrandCanonical.ResponseMatrix`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/GrandCanonical/ResponseMatrix.lean`
- Line: `57`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_ffcc2771b3fa581903e0a10b2a57e5fd0327b46c`
- SCC: `scc_8c92a93548ee13eb9271ca8da13313b2d294236a`
- Witness backed: `True`

```lean
-- 53:   deriv (fun t => muResponse params t μ) β
-- 54: 
-- 55: /-- Thermodynamic response / susceptibility matrix in `(β, μ)` coordinates. -/
-- 56: structure ResponseMatrix2 where
-- 57:   betaBeta : ℝ
-- 58:   betaMu   : ℝ
-- 59:   muBeta   : ℝ
-- 60:   muMu     : ℝ
-- 61: 
```

## 2. `InfoGeometry.GrandCanonical.ResponseMatrix2.betaMu`

- Score: `251.8125`
- Distance: `None`
- Module: `InfoGeometry.GrandCanonical.ResponseMatrix`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/GrandCanonical/ResponseMatrix.lean`
- Line: `58`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_b673d744466b69c992a3159cab6568d228c9b134`
- SCC: `scc_30d922504f3286ab6eac12664c189e34579c9a29`
- Witness backed: `True`

```lean
-- 54: 
-- 55: /-- Thermodynamic response / susceptibility matrix in `(β, μ)` coordinates. -/
-- 56: structure ResponseMatrix2 where
-- 57:   betaBeta : ℝ
-- 58:   betaMu   : ℝ
-- 59:   muBeta   : ℝ
-- 60:   muMu     : ℝ
-- 61: 
-- 62: namespace ResponseMatrix2
```

## 3. `InfoGeometry.GrandCanonical.ResponseMatrix2.muBeta`

- Score: `251.8125`
- Distance: `None`
- Module: `InfoGeometry.GrandCanonical.ResponseMatrix`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/GrandCanonical/ResponseMatrix.lean`
- Line: `59`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_c3794c979c75ee6b6e2ed95809739ef408aec6d3`
- SCC: `scc_21761d10a2f88f503924d8baa17aa36276b7279d`
- Witness backed: `True`

```lean
-- 55: /-- Thermodynamic response / susceptibility matrix in `(β, μ)` coordinates. -/
-- 56: structure ResponseMatrix2 where
-- 57:   betaBeta : ℝ
-- 58:   betaMu   : ℝ
-- 59:   muBeta   : ℝ
-- 60:   muMu     : ℝ
-- 61: 
-- 62: namespace ResponseMatrix2
-- 63: 
```

## 4. `InfoGeometry.Canonical.OperatorialCramerRao.inv_comparisonStateGeneratorMetric_self_le_of_unit_response`

- Score: `242.903682`
- Distance: `None`
- Module: `InfoGeometry.Canonical.OperatorialCramerRao`
- Declaration kind: `theorem`
- Representation layer: `L3_Krein`
- Representation depth: `3`
- Representation slug: `krein`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/OperatorialCramerRao.lean`
- Line: `92`

Layer note: Krein/doubled-geometry substrate

Doc:

Operatorial Cramer-Rao lower bound on the comparison-state channel metric.

If the channel pair `(X,Y)` has unit response and the reference channel `Y`
acts nontrivially on the comparison state, then the diagonal cost of `X`
dominates the inverse diagonal cost of `Y`.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_8ad0cf3675dde7984765cc97600b1f04745b52a1`
- SCC: `scc_3403f62a63cc5281cb4423b92554886a718ab3da`
- Witness backed: `True`

```lean
-- 88:       * comparisonStateGeneratorMetric (E := E) comparison Y Y := by
-- 89:   have hCS := comparisonStateGeneratorMetric_sq_le (E := E) comparison X Y
-- 90:   simpa [hUnit, pow_two] using hCS
-- 91: 
-- 92: /--
-- 93: Operatorial Cramer-Rao lower bound on the comparison-state channel metric.
-- 94: 
-- 95: If the channel pair `(X,Y)` has unit response and the reference channel `Y`
-- 96: acts nontrivially on the comparison state, then the diagonal cost of `X`
```

## 5. `InfoGeometry.GrandCanonical.ResponseMatrix2.muMu`

- Score: `242.748945`
- Distance: `None`
- Module: `InfoGeometry.GrandCanonical.ResponseMatrix`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/GrandCanonical/ResponseMatrix.lean`
- Line: `60`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_ae5f4f3280fd8a4f4f4aba3b649329ca9380aa2a`
- SCC: `scc_618a77e3eb1a4920a15f3ad8f8d52c1c8512c98f`
- Witness backed: `True`

```lean
-- 56: structure ResponseMatrix2 where
-- 57:   betaBeta : ℝ
-- 58:   betaMu   : ℝ
-- 59:   muBeta   : ℝ
-- 60:   muMu     : ℝ
-- 61: 
-- 62: namespace ResponseMatrix2
-- 63: 
-- 64: /-- Extensionality for finite response packets. -/
```

## 6. `InfoGeometry.Quantum.GeometricQuantumTensor.berry_alt`

- Score: `242.636552`
- Distance: `None`
- Module: `InfoGeometry.Quantum.GeometricTensor`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Quantum/GeometricTensor.lean`
- Line: `41`

Doc:

The Berry curvature is alternating. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_e0daa57b35c50248667de5a72817c9c6da5579b5`
- SCC: `scc_07bfa3f9a2849cc9ab053d3b8e1a74c487562856`
- Witness backed: `True`

```lean
-- 37:   berry  : LinearMap.BilinForm ℝ (DoubledSpace E)
-- 38:   /-- The metric is symmetric. -/
-- 39:   metric_symm : metric.IsSymm
-- 40:   /-- The Berry curvature is alternating. -/
-- 41:   berry_alt   : berry.IsAlt
-- 42:   /-- Kähler Compatibility: $\Omega(u, v) = g(K u, v)$. -/
-- 43:   compat      : ∀ u v, berry u v = metric (modularComplexI u) v
-- 44: 
-- 45: /-- Abbreviation for the Quantum Geometric Tensor. -/
```

## 7. `InfoGeometry.Quantum.GeometricQuantumTensor.metric_symm`

- Score: `240.484375`
- Distance: `None`
- Module: `InfoGeometry.Quantum.GeometricTensor`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Quantum/GeometricTensor.lean`
- Line: `39`

Doc:

The metric is symmetric. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_d0149dfad987c460bd4ca22c5627c05486268d5c`
- SCC: `scc_85d5a93505f95069973bee198766032f82f26944`
- Witness backed: `True`

```lean
-- 35:   metric : LinearMap.BilinForm ℝ (DoubledSpace E)
-- 36:   /-- The alternating Berry curvature (symplectic) component. -/
-- 37:   berry  : LinearMap.BilinForm ℝ (DoubledSpace E)
-- 38:   /-- The metric is symmetric. -/
-- 39:   metric_symm : metric.IsSymm
-- 40:   /-- The Berry curvature is alternating. -/
-- 41:   berry_alt   : berry.IsAlt
-- 42:   /-- Kähler Compatibility: $\Omega(u, v) = g(K u, v)$. -/
-- 43:   compat      : ∀ u v, berry u v = metric (modularComplexI u) v
```

## 8. `InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_add`

- Score: `240.3125`
- Distance: `None`
- Module: `InfoGeometry.Quantum.GeometricTensorOperatorLift`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`
- Line: `61`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_cceaf889cab416e1607fc5abc8fab1290d828fac`
- SCC: `scc_b57fc395c5cc36ad7f6d385018a69862af459a6d`
- Witness backed: `True`

```lean
-- 57:   ext u v
-- 58:   simp [metricOfOperator_apply]
-- 59: 
-- 60: omit [CompleteSpace E] in
-- 61: @[simp] theorem metricOfOperator_add
-- 62:     (A B : EndH) :
-- 63:     metricOfOperator (E := E) (A + B)
-- 64:       = metricOfOperator (E := E) A + metricOfOperator (E := E) B := by
-- 65:   ext u v
```

## 9. `InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_apply`

- Score: `240.3125`
- Distance: `None`
- Module: `InfoGeometry.Quantum.GeometricTensorOperatorLift`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`
- Line: `50`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_3200fffac72b2ab9d01c71a000902cfa8cb22da2`
- SCC: `scc_7b781b840d012f60ea18b09e6db9daea02ca648c`
- Witness backed: `True`

```lean
-- 46:       intro c u v
-- 47:       simp [real_inner_smul_right, smul_eq_mul, mul_add])
-- 48: 
-- 49: omit [CompleteSpace E] in
-- 50: @[simp] theorem metricOfOperator_apply
-- 51:     (A : EndH) (u v : H₂) :
-- 52:     metricOfOperator A u v = ⟪A u, v⟫_ℝ := rfl
-- 53: 
-- 54: omit [CompleteSpace E] in
```

## 10. `InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_neg`

- Score: `240.3125`
- Distance: `None`
- Module: `InfoGeometry.Quantum.GeometricTensorOperatorLift`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`
- Line: `69`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_0b4aebdc09857d33ff912f1b45745156b4048394`
- SCC: `scc_8801ae1c2b98ac2ff007caf18ca64546b36e1303`
- Witness backed: `True`

```lean
-- 65:   ext u v
-- 66:   simp [metricOfOperator_apply, inner_add_left]
-- 67: 
-- 68: omit [CompleteSpace E] in
-- 69: @[simp] theorem metricOfOperator_neg
-- 70:     (A : EndH) :
-- 71:     metricOfOperator (E := E) (-A)
-- 72:       = -metricOfOperator (E := E) A := by
-- 73:   ext u v
```

## 11. `InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_smul`

- Score: `240.3125`
- Distance: `None`
- Module: `InfoGeometry.Quantum.GeometricTensorOperatorLift`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`
- Line: `77`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_fe817702ac2c79444e54d9485c07307e6619701f`
- SCC: `scc_eff469e0c44a17e91b37d737fcbfe90c93b2a501`
- Witness backed: `True`

```lean
-- 73:   ext u v
-- 74:   simp [metricOfOperator_apply]
-- 75: 
-- 76: omit [CompleteSpace E] in
-- 77: @[simp] theorem metricOfOperator_smul
-- 78:     (c : ℝ) (A : EndH) :
-- 79:     metricOfOperator (E := E) (c • A)
-- 80:       = c • metricOfOperator (E := E) A := by
-- 81:   ext u v
```

## 12. `InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_zero`

- Score: `240.3125`
- Distance: `None`
- Module: `InfoGeometry.Quantum.GeometricTensorOperatorLift`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`
- Line: `55`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_d3f9e0502f0f7da74fa6c1d217fc2ab53615996b`
- SCC: `scc_68a5a131e1f4d5181ef79e4f04ede5a5979cb931`
- Witness backed: `True`

```lean
-- 51:     (A : EndH) (u v : H₂) :
-- 52:     metricOfOperator A u v = ⟪A u, v⟫_ℝ := rfl
-- 53: 
-- 54: omit [CompleteSpace E] in
-- 55: @[simp] theorem metricOfOperator_zero :
-- 56:     metricOfOperator (E := E) (0 : EndH) = 0 := by
-- 57:   ext u v
-- 58:   simp [metricOfOperator_apply]
-- 59: 
```
