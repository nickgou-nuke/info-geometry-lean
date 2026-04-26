# Gravitational Lean Context

- Query: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicModularTimeKMSContext`
- Graph source: `arango:faithful_raw`
- Nodes: `34355`
- Edges: `1473813`
- Synonym groups: `8`
- Requested layers: `all`
- Promotion allowed: `false`

## Representation Layers

- `unlabeled`: `29357`
- `L0_Count`: `2`; depth `0`; slug `count`
- `L1_Projective`: `219`; depth `1`; slug `projective`
- `L2_Operator`: `1033`; depth `2`; slug `operator`
- `L3_Krein`: `1369`; depth `3`; slug `krein`
- `L4_ModularTransport`: `1828`; depth `4`; slug `transport`
- `L5_ThermodynamicClosure`: `547`; depth `5`; slug `thermo`

## Synonym Expansion

- `EQC-0220` matched `canonical, coordinateless, geometry, info, kmsbridge, souriau`; added `algebraic, eval, geometric, metric, quantum, state, tensor`
- `EQC-0218` matched `canonical, geometry, info, modular`; added `certified, kreg, log, reduction`
- `EQC-0263` matched `canonical, geometry, info, modular`; added `conjugation, krein, takesaki, tomita`
- `EQC-0221` matched `canonical, geometry, info, souriau`; added `coarse, dirac, grain, sector, zorn`
- `EQC-0252` matched `canonical, geometry, info, modular`; added `core, density, potential, relative`
- `EQC-0267` matched `canonical, geometry, info, modular`; added `algebra, package, primitive, supercharge, unified`
- `EQC-0253` matched `canonical, geometry, info, modular`; added `representative`
- `EQC-0260` matched `canonical, geometry, info, souriau`; added `beta, pairing, temperature, thermodynamics, weight`

## 1. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicModularTimeKMSContext.state_eval_one`

- Score: `658.224126`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `theorem`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `361`

Layer note: operator-algebraic bridge substrate

Doc:

The underlying cyclic state remains normalized. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_67f81ffa6f4d0695d14c0fe6d89c772d84e636b6`
- SCC: `scc_3b63deb51154431a38b601d8584914ba21ef7af6`
- Witness backed: `True`

```lean
-- 357: theorem kms_eval_mul_modular_eq_eval_flip (A B : Obs) :
-- 358:     M.state.state.eval (A * M.sigma M.beta B) = M.state.state.eval (B * A) := by
-- 359:   simpa [CyclicModularTimeKMSContext.sigma, identityAdditiveModularFlow] using M.state.cyclic A B
-- 360: 
-- 361: /-- The underlying cyclic state remains normalized. -/
-- 362: @[rep_depth operator]
-- 363: theorem state_eval_one :
-- 364:     M.state.state.eval 1 = 1 :=
-- 365:   M.state.state.eval_one
```

## 2. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicModularTimeKMSContext.state`

- Score: `655.461982`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `331`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_78332b146f3dee4c1e3bcf3c3addb8b4fdf36616`
- SCC: `scc_e44aa0c8d6431980339162271ab09a2d30d3adbf`
- Witness backed: `True`

```lean
-- 327: cyclicity rather than carried as a separate hypothesis field.
-- 328: -/
-- 329: @[rep_depth operator]
-- 330: structure CyclicModularTimeKMSContext where
-- 331:   state : CyclicAlgebraicState (H := H)
-- 332:   beta : ℝ
-- 333: 
-- 334: namespace CyclicModularTimeKMSContext
-- 335: 
```

## 3. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicModularTimeKMSContext.beta`

- Score: `649.049482`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `332`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_3e76ae6e45e6394eac1e6b316227abdc757d80c2`
- SCC: `scc_fb85fb6e1483ac0770e5a1dc3bca67259ea4da86`
- Witness backed: `True`

```lean
-- 328: -/
-- 329: @[rep_depth operator]
-- 330: structure CyclicModularTimeKMSContext where
-- 331:   state : CyclicAlgebraicState (H := H)
-- 332:   beta : ℝ
-- 333: 
-- 334: namespace CyclicModularTimeKMSContext
-- 335: 
-- 336: variable (M : CyclicModularTimeKMSContext (H := H))
```

## 4. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicModularTimeKMSContext.modular_time_add`

- Score: `645.029723`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `theorem`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `343`

Layer note: operator-algebraic bridge substrate

Doc:

Modular time is additive on the constructive cyclic branch. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_63ac8867d7935dd5bd848ce2e263b572d8d7f15d`
- SCC: `scc_6017a36c10ad4dc92c012858fa57b87696591629`
- Witness backed: `True`

```lean
-- 339: @[rep_depth operator]
-- 340: def sigma (_M : CyclicModularTimeKMSContext (H := H)) : AdditiveModularFlow (H := H) :=
-- 341:   identityAdditiveModularFlow (H := H)
-- 342: 
-- 343: /-- Modular time is additive on the constructive cyclic branch. -/
-- 344: @[rep_depth operator]
-- 345: theorem modular_time_add (s t : ℝ) :
-- 346:     M.sigma (s + t) = M.sigma s * M.sigma t :=
-- 347:   AdditiveModularFlow.map_add M.sigma s t
```

## 5. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicModularTimeKMSContext.kms_eval_mul_modular_eq_eval_flip`

- Score: `644.655061`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `theorem`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `355`

Layer note: operator-algebraic bridge substrate

Doc:

KMS identity derived from cyclicity; no `KMSState` packet is consumed. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_0109ad32a1fd3c802f715fd7eea6e0a4a5350fc7`
- SCC: `scc_5c551f7f2367a9b6cb8c02565f2b453611353297`
- Witness backed: `True`

```lean
-- 351: theorem modular_time_zero :
-- 352:     M.sigma 0 = 1 :=
-- 353:   AdditiveModularFlow.map_zero M.sigma
-- 354: 
-- 355: /-- KMS identity derived from cyclicity; no `KMSState` packet is consumed. -/
-- 356: @[rep_depth operator]
-- 357: theorem kms_eval_mul_modular_eq_eval_flip (A B : Obs) :
-- 358:     M.state.state.eval (A * M.sigma M.beta B) = M.state.state.eval (B * A) := by
-- 359:   simpa [CyclicModularTimeKMSContext.sigma, identityAdditiveModularFlow] using M.state.cyclic A B
```

## 6. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicModularTimeKMSContext.modular_time_zero`

- Score: `640.508047`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `theorem`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `349`

Layer note: operator-algebraic bridge substrate

Doc:

Modular time starts at the identity automorphism on the constructive branch. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_8e7cf961b92ef51b6432440633ff5fc7031ec8c2`
- SCC: `scc_f76fd50f0dbc754c414703d1698132057da083b6`
- Witness backed: `True`

```lean
-- 345: theorem modular_time_add (s t : ℝ) :
-- 346:     M.sigma (s + t) = M.sigma s * M.sigma t :=
-- 347:   AdditiveModularFlow.map_add M.sigma s t
-- 348: 
-- 349: /-- Modular time starts at the identity automorphism on the constructive branch. -/
-- 350: @[rep_depth operator]
-- 351: theorem modular_time_zero :
-- 352:     M.sigma 0 = 1 :=
-- 353:   AdditiveModularFlow.map_zero M.sigma
```

## 7. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicModularTimeKMSContext.casesOn`

- Score: `636.70862`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `321`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_29e59a136e40f2623863f84cce3e40366cdb809d`
- SCC: `scc_ff76b2ab0c77ba34a11be8bf8dfb2660be4ae6a4`
- Witness backed: `True`

```lean
-- 317:   M.kms.eval_mul_modular_eq_eval_flip A B
-- 318: 
-- 319: end ModularTimeKMSContext
-- 320: 
-- 321: /--
-- 322: Constructive modular-time KMS context on the cyclic identity-flow branch.
-- 323: 
-- 324: This is the infinite/operator-algebraic owner that removes the explicit
-- 325: `kms : KMSState` packet from `ModularTimeKMSContext`: the state is cyclic, the
```

## 8. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicModularTimeKMSContext.mk.noConfusion`

- Score: `636.70862`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `330`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_7df331004f35c44bd7b7079786363dad8214a865`
- SCC: `scc_f5115e3b56b020d37c230939cdf6a77e72895a7b`
- Witness backed: `True`

```lean
-- 326: modular flow is the identity additive flow, and the KMS identity is proved from
-- 327: cyclicity rather than carried as a separate hypothesis field.
-- 328: -/
-- 329: @[rep_depth operator]
-- 330: structure CyclicModularTimeKMSContext where
-- 331:   state : CyclicAlgebraicState (H := H)
-- 332:   beta : ℝ
-- 333: 
-- 334: namespace CyclicModularTimeKMSContext
```

## 9. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicModularTimeKMSContext.noConfusion`

- Score: `636.70862`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `321`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_7e07dff349237182cea936a2be10544838443f49`
- SCC: `scc_5e8b20f4fd2ccb1af2cfb023e9cc6c9976f4d874`
- Witness backed: `True`

```lean
-- 317:   M.kms.eval_mul_modular_eq_eval_flip A B
-- 318: 
-- 319: end ModularTimeKMSContext
-- 320: 
-- 321: /--
-- 322: Constructive modular-time KMS context on the cyclic identity-flow branch.
-- 323: 
-- 324: This is the infinite/operator-algebraic owner that removes the explicit
-- 325: `kms : KMSState` packet from `ModularTimeKMSContext`: the state is cyclic, the
```

## 10. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicModularTimeKMSContext.recOn`

- Score: `636.70862`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `321`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_e6cf4705d3c8a30ff1ab626a1d5cfaf7f1c89362`
- SCC: `scc_6306f090dd0529d2520f2bca904c7f5a4c7a5ae7`
- Witness backed: `True`

```lean
-- 317:   M.kms.eval_mul_modular_eq_eval_flip A B
-- 318: 
-- 319: end ModularTimeKMSContext
-- 320: 
-- 321: /--
-- 322: Constructive modular-time KMS context on the cyclic identity-flow branch.
-- 323: 
-- 324: This is the infinite/operator-algebraic owner that removes the explicit
-- 325: `kms : KMSState` packet from `ModularTimeKMSContext`: the state is cyclic, the
```

## 11. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicModularTimeKMSContext.mk`

- Score: `629.980986`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `constructor`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `330`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_bdf209df606a456c6f004613791f25f068d43aa8`
- SCC: `scc_bf6b94e34b6237de89b3f10db75a969da28d84dc`
- Witness backed: `True`

```lean
-- 326: modular flow is the identity additive flow, and the KMS identity is proved from
-- 327: cyclicity rather than carried as a separate hypothesis field.
-- 328: -/
-- 329: @[rep_depth operator]
-- 330: structure CyclicModularTimeKMSContext where
-- 331:   state : CyclicAlgebraicState (H := H)
-- 332:   beta : ℝ
-- 333: 
-- 334: namespace CyclicModularTimeKMSContext
```

## 12. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicModularTimeKMSContext.sigma`

- Score: `625.918468`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `def`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `338`

Layer note: operator-algebraic bridge substrate

Doc:

The owned modular automorphism group is the identity flow. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_8c5fdde1e1b854431b44e5bf51d3f0de08437b06`
- SCC: `scc_65a26a23bd90ff6176dc02d5da5bca571e717849`
- Witness backed: `True`

```lean
-- 334: namespace CyclicModularTimeKMSContext
-- 335: 
-- 336: variable (M : CyclicModularTimeKMSContext (H := H))
-- 337: 
-- 338: /-- The owned modular automorphism group is the identity flow. -/
-- 339: @[rep_depth operator]
-- 340: def sigma (_M : CyclicModularTimeKMSContext (H := H)) : AdditiveModularFlow (H := H) :=
-- 341:   identityAdditiveModularFlow (H := H)
-- 342: 
```
