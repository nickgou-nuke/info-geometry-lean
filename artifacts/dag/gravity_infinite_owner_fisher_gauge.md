# Gravitational Lean Context

- Query: `CyclicCoordinatelessSouriauFisherContext fisherMetric weylGauge ObservableMinimalCyclicCoordinatelessSouriauContext identity SLD cyclic algebraic state infinite operator algebra`
- Graph source: `arango:faithful_raw`
- Nodes: `29852`
- Edges: `1325307`
- Synonym groups: `8`
- Requested layers: `all`
- Promotion allowed: `false`

## Representation Layers

- `unlabeled`: `25435`
- `L0_Count`: `2`; depth `0`; slug `count`
- `L1_Projective`: `203`; depth `1`; slug `projective`
- `L2_Operator`: `836`; depth `2`; slug `operator`
- `L3_Krein`: `1338`; depth `3`; slug `krein`
- `L4_ModularTransport`: `1696`; depth `4`; slug `transport`
- `L5_ThermodynamicClosure`: `342`; depth `5`; slug `thermo`

## Synonym Expansion

- `EQC-0220` matched `algebraic, coordinateless, metric, souriau, state`; added `canonical, eval, geometric, geometry, info, kmsbridge, quantum, tensor`
- `EQC-0092` matched `fisher, metric, state`; added ``
- `EQC-0110` matched `context, operator, souriau`; added `hamiltonian, log, modular, moment`
- `EQC-0259` matched `context, infinite, souriau`; added `coadjoint, ent, finite, image, jaynes, max, metriplectic, orbit, problem`
- `EQC-0138` matched `gauge, weyl`; added `temperature, transform`
- `EQC-0103` matched `operator, souriau`; added `bkm, hessian, massieu`
- `EQC-0139` matched `gauge, weyl`; added `field, potential, strength`
- `EQC-0118` matched `operator, weyl`; added `character, mean, partition, readout`

## 1. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicAlgebraicState.sldQuantumFisherMetric_symm`

- Score: `693.254637`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `theorem`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `239`

Layer note: operator-algebraic bridge substrate

Faithful witness:

- Raw doc: `raw_info_nodes/raw_212402312ae2609c7e3885db7800dc3d35b33a95`
- SCC: `scc_482af73546d5f2c843b5129cf59791de8c5e4f38`
- Witness backed: `True`

```lean
-- 235:   symmetric := by
-- 236:     intro X Y
-- 237:     exact ω.cyclic (sld X) (sld Y)
-- 238: 
-- 239: @[rep_depth operator]
-- 240: theorem sldQuantumFisherMetric_symm
-- 241:     (sld : Tangent → Obs) (X Y : Tangent) :
-- 242:     (ω.sldQuantumFisherMetric sld).metric X Y =
-- 243:       (ω.sldQuantumFisherMetric sld).metric Y X :=
```

## 2. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicAlgebraicState.sldQuantumFisherMetric`

- Score: `661.426931`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `def`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `222`

Layer note: operator-algebraic bridge substrate

Doc:

Construct the coordinate-free SLD/Fisher metric from a cyclic algebraic state.

The metric symmetry is not another hypothesis: it is derived from cyclicity.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_351367abdc2f33b6ce6d9dec4bfce15c39f3db56`
- SCC: `scc_e9392a9ea5abade138097ada334e70d176792117`
- Witness backed: `True`

```lean
-- 218: 
-- 219: variable {Tangent : Type v}
-- 220: variable (ω : CyclicAlgebraicState (H := H))
-- 221: 
-- 222: /--
-- 223: Construct the coordinate-free SLD/Fisher metric from a cyclic algebraic state.
-- 224: 
-- 225: The metric symmetry is not another hypothesis: it is derived from cyclicity.
-- 226: -/
```

## 3. `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.SouriauLieThermoKKTContext.operatorialSouriauFisherMetric_packet_of_cramerRaoResponse`

- Score: `653.832898`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauLieThermoKKTBridge`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean`
- Line: `1121`

Layer note: modular/transport/flow substrate

Doc:

Operatorial Souriau-Fisher metric packet.

The Souriau-Fisher metric is exposed here as the doubled-Krein
`comparisonStateGeneratorMetric`, not as a finite response matrix or a scalar
Kähler-potential label.  The Hessian/Onsager readout identity is paired with
the Cramer-Rao channel metric realization and the resulting second-law
nonnegativity.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_f47968fd4b0f9e1d51a1521f88e71da61059114b`
- SCC: `scc_594e85d1e143269740a6388164936bacaf1046af`
- Witness backed: `True`

```lean
-- 1117: 
-- 1118: /--
-- 1119: Operatorial Souriau-Fisher metric packet.
-- 1120: 
-- 1121: The Souriau-Fisher metric is exposed here as the doubled-Krein
-- 1122: `comparisonStateGeneratorMetric`, not as a finite response matrix or a scalar
-- 1123: Kähler-potential label.  The Hessian/Onsager readout identity is paired with
-- 1124: the Cramer-Rao channel metric realization and the resulting second-law
-- 1125: nonnegativity.
```

## 4. `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.fisherMetric_nonneg`

- Score: `644.655061`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauLieThermoKKTBridge`
- Declaration kind: `theorem`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean`
- Line: `621`

Layer note: operator-algebraic bridge substrate

Doc:

The coordinateless quantum-Fisher/Bures metric is nonnegative by data. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_e2ced99cc920aeced86893e24f777ab4f52e2880`
- SCC: `scc_d993c60709c14cdfab633dcd54894a18696e32ee`
- Witness backed: `True`

```lean
-- 617: 
-- 618: /-- The coordinateless quantum-Fisher/Bures metric is nonnegative by data. -/
-- 619: @[rep_depth operator]
-- 620: theorem fisherMetric_nonneg :
-- 621:     0 ≤ K.quantumFisherMetric :=
-- 622:   K.quantumFisherMetric_nonneg
-- 623: 
-- 624: /-- KMS and Weyl covariance are explicit algebraic hypotheses, not coordinates. -/
-- 625: @[rep_depth operator]
```

## 5. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CoordinatelessSouriauFisherContext.weylGauge`

- Score: `642.1961`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `363`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_d02e20a12a685f8f081937bea227c6f409306f01`
- SCC: `scc_c449e94150cad4e7ef776f1fc29afe4fcd98abbb`
- Witness backed: `True`

```lean
-- 359:   kms : KMSState (H := H) sigma beta
-- 360:   kms_state_eq : kms.state = state
-- 361:   souriauMoment : OperatorSouriauMoment (H := H) Symmetry
-- 362:   fisherMetric : QuantumFisherSLDMetric (H := H) Tangent state
-- 363:   weylGauge : WeylAlgebraGauge (H := H) state
-- 364: 
-- 365: namespace CoordinatelessSouriauFisherContext
-- 366: 
-- 367: variable {Symmetry : Type v} {Tangent : Type v}
```

## 6. `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.FullCoadjointOrbitMetriplecticContext.weylGaugeCovariant_proof`

- Score: `635.462014`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauLieThermoKKTBridge`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean`
- Line: `285`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_5692d1c2e1d170f5c253a6f415beac4beda9fe40`
- SCC: `scc_d092af108ed1520fb352631e6638175f68e5257c`
- Witness backed: `True`

```lean
-- 281:   weylGaugeCovariant : Prop
-- 282:   weylGaugeCovariant_proof : weylGaugeCovariant
-- 283:   supertraceFreeStress : Prop
-- 284:   supertraceFreeStress_proof : supertraceFreeStress
-- 285: 
-- 286: namespace FullCoadjointOrbitMetriplecticContext
-- 287: 
-- 288: variable {G Gdual Orbit : Type*}
-- 289: 
```

## 7. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CoordinatelessSouriauFisherContext.fisherMetric`

- Score: `634.968633`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `362`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_175303c2d1763eaecc3ce660f59eceb955eabc5e`
- SCC: `scc_e90b78d677b867b5679ca49fd0a4db4607d70fb3`
- Witness backed: `True`

```lean
-- 358:   beta : ℝ
-- 359:   kms : KMSState (H := H) sigma beta
-- 360:   kms_state_eq : kms.state = state
-- 361:   souriauMoment : OperatorSouriauMoment (H := H) Symmetry
-- 362:   fisherMetric : QuantumFisherSLDMetric (H := H) Tangent state
-- 363:   weylGauge : WeylAlgebraGauge (H := H) state
-- 364: 
-- 365: namespace CoordinatelessSouriauFisherContext
-- 366: 
```

## 8. `InfoGeometry.Canonical.SouriauConformalKKT.ConformalWeylTKKKKTJordanLieContext.fieldStrength_transformWeylGaugeByPotential_eq`

- Score: `629.148985`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauConformalKKTContext`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauConformalKKTContext.lean`
- Line: `824`

Layer note: modular/transport/flow substrate

Doc:

Potential-form Weyl gauge transformations preserve the associated
field-strength object.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_7046be9c074f52ff32b764e7736983c8f7007acc`
- SCC: `scc_b1e398cac60ea864127c4990e9a619fee48bf6b0`
- Witness backed: `True`

```lean
-- 820:     (αW : WeylGaugeParameter EndH₂ EndH₂) :
-- 821:     (C.transformWeylGaugeByPotential Δ αW).SatisfiesKKT_TKK_Weyl_JordanLieClosure := by
-- 822:   exact (C.transformWeylGaugeByPotential Δ αW).satisfiesKKT_TKK_Weyl_JordanLieClosure
-- 823: 
-- 824: /--
-- 825: Potential-form Weyl gauge transformations preserve the associated
-- 826: field-strength object.
-- 827: -/
-- 828: @[rep_depth transport]
```

## 9. `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.FullCoadjointOrbitMetriplecticContext.weylGaugeCovariant`

- Score: `620.175`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauLieThermoKKTBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean`
- Line: `284`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_59511eeb0c2df227eff4cb01067af7695e5a53de`
- SCC: `scc_47977916a6f5aa9318e7d734f0539bf15ac54349`
- Witness backed: `True`

```lean
-- 280:         reversibleEntropyRate x + dissipativeEntropyRate x
-- 281:   weylGaugeCovariant : Prop
-- 282:   weylGaugeCovariant_proof : weylGaugeCovariant
-- 283:   supertraceFreeStress : Prop
-- 284:   supertraceFreeStress_proof : supertraceFreeStress
-- 285: 
-- 286: namespace FullCoadjointOrbitMetriplecticContext
-- 287: 
-- 288: variable {G Gdual Orbit : Type*}
```

## 10. `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.quantumFisherMetric_nonneg`

- Score: `619.572534`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauLieThermoKKTBridge`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean`
- Line: `614`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_844a4f57d513b929d22e50b6e5a2b81f61a394d2`
- SCC: `scc_7c554ed3ee87b8be34baadfabaf84b38a168571b`
- Witness backed: `True`

```lean
-- 610:   quantumFisherMetric : ℝ
-- 611:   quantumFisherMetric_nonneg : 0 ≤ quantumFisherMetric
-- 612: 
-- 613: namespace CoordinatelessKMSFisherState
-- 614: 
-- 615: variable {Obs : Type*}
-- 616: variable (K : CoordinatelessKMSFisherState Obs)
-- 617: 
-- 618: /-- The coordinateless quantum-Fisher/Bures metric is nonnegative by data. -/
```

## 11. `InfoGeometry.Canonical.WeylGaugeField.transformByPotential_apply`

- Score: `616.233141`
- Distance: `None`
- Module: `InfoGeometry.Canonical.WeylGaugeField`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/WeylGaugeField.lean`
- Line: `178`

Doc:

Pointwise expansion of `transformByPotential`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_8d52fe0b88ad0b2178a86d82d59dc77d061d7ed5`
- SCC: `scc_6795a7af2e0fabf8079f4e6d24005b46cbb34c81`
- Witness backed: `True`

```lean
-- 174:     (B : WeylGaugeField X A)
-- 175:     (α : WeylGaugeParameter X A) : WeylGaugeField X A where
-- 176:   gaugeOf x := B.gaugeOf x - Δ.diff α.shiftOf x
-- 177: 
-- 178: /-- Pointwise expansion of `transformByPotential`. -/
-- 179: @[simp] theorem transformByPotential_apply
-- 180:     (Δ : WeylDifferentialOperator K X A)
-- 181:     (B : WeylGaugeField X A)
-- 182:     (α : WeylGaugeParameter X A)
```

## 12. `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.quantumFisherMetric`

- Score: `616.128763`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauLieThermoKKTBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean`
- Line: `613`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_7a89de1f55bb4d0c0c896aaeddbb6989358e728a`
- SCC: `scc_76059fee2be5e004b741fb9e8d754564837883dd`
- Witness backed: `True`

```lean
-- 609:   weylAutomorphismInvariant : Prop
-- 610:   quantumFisherMetric : ℝ
-- 611:   quantumFisherMetric_nonneg : 0 ≤ quantumFisherMetric
-- 612: 
-- 613: namespace CoordinatelessKMSFisherState
-- 614: 
-- 615: variable {Obs : Type*}
-- 616: variable (K : CoordinatelessKMSFisherState Obs)
-- 617: 
```
