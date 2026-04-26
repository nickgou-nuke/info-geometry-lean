# Gravitational Lean Context

- Query: `PrimeGasOperatorialFierzPacket operatorInformationHessian FierzStressProjectionContext`
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

- `EQC-0128` matched `projection, stress`; added `total`
- `EQC-0341` matched `projection, stress`; added `readout, skeleton`
- `EQC-0103` matched `hessian, operator`; added `bkm, massieu, souriau`
- `EQC-0104` matched `projection, stress`; added `coadjoint, moment, orbit, super, tensor`
- `EQC-0110` matched `context, operator`; added `hamiltonian, log, modular`
- `EQC-0148` matched `operator, operatorial`; added `anomaly, cci, chiral, incidence, obstruction, projector`
- `EQC-0116` matched `context, hessian`; added `coord, dual, geometry, info, inverse, legendre, model, potential, thermo`
- `EQC-0102` matched `hessian, operator`; added `ambient, bridge, canonical, coordinate, core, data, defect, density, energy, gibbs, minus, plus, positive, projective, ray, real, recomposition, relative`

## 1. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.operatorInformationHessian_projectedStress_eq_fierzHilbert`

- Score: `1026.1395`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `92`

Layer note: modular/transport/flow substrate

Doc:

Stress readout of the operatorial Hessian/BKM proxy.

This is the conservative Lean form of the Fierz stress projection claim:
the equality holds only after the explicit projection/readout compatibility
context is supplied.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_4ab17cf45771a9acfe079dd9a9f7d6f6a59e879b`
- SCC: `scc_6727f8578fbef48cccc392514d6ffe19c32940bb`
- Witness backed: `True`

```lean
-- 88: theorem projectedStressReadout_eq_fierzHilbert (B : EndH) :
-- 89:     C.projectedStressReadout B = infoHilbert (E := E) (C.projectedState B) := by
-- 90:   exact C.stress_eq_fierzHilbert B
-- 91: 
-- 92: /--
-- 93: Stress readout of the operatorial Hessian/BKM proxy.
-- 94: 
-- 95: This is the conservative Lean form of the Fierz stress projection claim:
-- 96: the equality holds only after the explicit projection/readout compatibility
```

## 2. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.operatorInformationHessian_projectedStress_fierz_identity`

- Score: `1002.34737`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `123`

Layer note: modular/transport/flow substrate

Doc:

Fierz channel identity for the stress projection of the operatorial Hessian.

This is the current spin-2/stress theorem surface: the squared projected
stress decomposes into scalar, symplectic, and area Fierz channels of the
projected Hessian state.  It is not a global linearized-gravity theorem.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_3e2181eb1e4b1371558ae6449b17bdac9af555ef`
- SCC: `scc_aa4d4ede210d7be1794d855f6d1bf0d06bb1b8d0`
- Witness backed: `True`

```lean
-- 119:           (transportCommutator X (transportCommutator X A))) := by
-- 120:   exact C.projectedStressReadout_eq_fierzHilbert
-- 121:     (transportCommutator X (transportCommutator X A))
-- 122: 
-- 123: /--
-- 124: Fierz channel identity for the stress projection of the operatorial Hessian.
-- 125: 
-- 126: This is the current spin-2/stress theorem surface: the squared projected
-- 127: stress decomposes into scalar, symplectic, and area Fierz channels of the
```

## 3. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.operatorInformationHessian_projectedStress_majorana_identity`

- Score: `997.21546`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `145`

Layer note: modular/transport/flow substrate

Doc:

Majorana/zero-area specialization of the projected stress identity.

If the projected Hessian state lies on the Majorana Fierz shadow, the area term
vanishes and the projected stress square is the scalar-plus-symplectic channel
sum.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_6b1072ac965b57f997b75480fec273ae95711ac4`
- SCC: `scc_92d4e35b62bc3d75f5d4d835725cad2f74a310bb`
- Witness backed: `True`

```lean
-- 141:   rw [C.operatorInformationHessian_projectedStress_eq_fierzHilbert X A]
-- 142:   exact information_fierz_identity
-- 143:     (E := E) (C.projectedState (operatorInformationHessian (E := E) X A))
-- 144: 
-- 145: /--
-- 146: Majorana/zero-area specialization of the projected stress identity.
-- 147: 
-- 148: If the projected Hessian state lies on the Majorana Fierz shadow, the area term
-- 149: vanishes and the projected stress square is the scalar-plus-symplectic channel
```

## 4. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.stressTensorReadout`

- Score: `649.455757`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `52`

Doc:

Stress-tensor scalar readout on projected operator responses. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_1430efc2568700410cd61f4eb50545a0e4039fed`
- SCC: `scc_4ec0dcf2ec224def07c1258e54d7bae8a2499c73`
- Witness backed: `True`

```lean
-- 48:   spin2Projector : EndH → EndH
-- 49:   /-- State readout used to evaluate Fierz channels after projection. -/
-- 50:   projectedFierzState : EndH → H₂
-- 51:   /-- Stress-tensor scalar readout on projected operator responses. -/
-- 52:   stressTensorReadout : EndH → ℝ
-- 53:   /-- The spin-2 projection is a projector on the operator lane. -/
-- 54:   spin2Projector_idempotent :
-- 55:     ∀ B : EndH, spin2Projector (spin2Projector B) = spin2Projector B
-- 56:   /--
```

## 5. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.spin2Projector`

- Score: `649.363206`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `48`

Doc:

Candidate spin-2 projection on operator Hessian responses. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_db8632e11d5d1a4fcf5544dbd643838a5e742187`
- SCC: `scc_b46ee2460760fb5c0ed87a63a1b1afde414fdb5b`
- Witness backed: `True`

```lean
-- 44: -/
-- 45: @[rep_depth transport]
-- 46: structure FierzStressProjectionContext where
-- 47:   /-- Candidate spin-2 projection on operator Hessian responses. -/
-- 48:   spin2Projector : EndH → EndH
-- 49:   /-- State readout used to evaluate Fierz channels after projection. -/
-- 50:   projectedFierzState : EndH → H₂
-- 51:   /-- Stress-tensor scalar readout on projected operator responses. -/
-- 52:   stressTensorReadout : EndH → ℝ
```

## 6. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.spin2Projector_idempotent`

- Score: `643.784483`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `54`

Doc:

The spin-2 projection is a projector on the operator lane. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_6b9e45de193c759631506c6c21d3da4eeb215a33`
- SCC: `scc_f12748c9bdf560be64e12629a45248d3e24e6625`
- Witness backed: `True`

```lean
-- 50:   projectedFierzState : EndH → H₂
-- 51:   /-- Stress-tensor scalar readout on projected operator responses. -/
-- 52:   stressTensorReadout : EndH → ℝ
-- 53:   /-- The spin-2 projection is a projector on the operator lane. -/
-- 54:   spin2Projector_idempotent :
-- 55:     ∀ B : EndH, spin2Projector (spin2Projector B) = spin2Projector B
-- 56:   /--
-- 57:   Compatibility gate: projected stress equals the Hilbert/Fierz channel of the
-- 58:   projected operator's associated doubled state.
```

## 7. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.projectedStressReadout`

- Score: `635.811285`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `def`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `69`

Layer note: modular/transport/flow substrate

Doc:

Projected stress readout of an arbitrary operator response. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_834572282a2ae360388bf770fb25d0301e589de9`
- SCC: `scc_d2a3e90c2f1e07288251d6de4a1af9dcab4bf4cc`
- Witness backed: `True`

```lean
-- 65: namespace FierzStressProjectionContext
-- 66: 
-- 67: variable (C : FierzStressProjectionContext (E := E))
-- 68: 
-- 69: /-- Projected stress readout of an arbitrary operator response. -/
-- 70: @[rep_depth transport]
-- 71: def projectedStressReadout (B : EndH) : ℝ :=
-- 72:   C.stressTensorReadout (C.spin2Projector B)
-- 73: 
```

## 8. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext`

- Score: `630.602964`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `inductive`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `36`

Layer note: modular/transport/flow substrate

Doc:

Proof-carrying Fierz projection context for the stress-tensor shadow of the
operatorial Hessian.

`spin2Projector` is intentionally supplied as data.  The repo does not yet
derive the physical spin-2 projection from Clifford/Fierz completeness; this
context records exactly what must be provided before the Hessian may be read as
a stress-tensor channel.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_05f1c8cbcbffebcb88edd9e48a25bbb024baa377`
- SCC: `scc_7451bad258fea7fb67dd0e0f5fd6ae5f3b6e3ddc`
- Witness backed: `True`

```lean
-- 32: 
-- 33: local notation "H₂" => DoubledSpace E
-- 34: local notation "EndH" => H₂ →L[ℝ] H₂
-- 35: 
-- 36: /--
-- 37: Proof-carrying Fierz projection context for the stress-tensor shadow of the
-- 38: operatorial Hessian.
-- 39: 
-- 40: `spin2Projector` is intentionally supplied as data.  The repo does not yet
```

## 9. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.projectedStressReadout_eq_fierzHilbert`

- Score: `629.091827`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `86`

Layer note: modular/transport/flow substrate

Doc:

The projected stress readout is the Hilbert/Fierz channel by compatibility. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_77abf5a025222db8d1afdabf989a90cdb2be7b83`
- SCC: `scc_d67b4d78909817abccb76da2aa575c98c92cc573`
- Witness backed: `True`

```lean
-- 82:     C.projectedStressReadout (C.spin2Projector B) =
-- 83:       C.projectedStressReadout B := by
-- 84:   simp [projectedStressReadout, C.spin2Projector_idempotent B]
-- 85: 
-- 86: /-- The projected stress readout is the Hilbert/Fierz channel by compatibility. -/
-- 87: @[rep_depth transport]
-- 88: theorem projectedStressReadout_eq_fierzHilbert (B : EndH) :
-- 89:     C.projectedStressReadout B = infoHilbert (E := E) (C.projectedState B) := by
-- 90:   exact C.stress_eq_fierzHilbert B
```

## 10. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.projectedStressReadout_projected`

- Score: `628.889071`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `79`

Layer note: modular/transport/flow substrate

Doc:

The projected stress readout is invariant under a second projection. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_a6fbe614bfb10986f550ac529f418f9421802f8e`
- SCC: `scc_11a69e6435e59219010dd5e6332dcdffb1b0f2f9`
- Witness backed: `True`

```lean
-- 75: @[rep_depth transport]
-- 76: def projectedState (B : EndH) : H₂ :=
-- 77:   C.projectedFierzState (C.spin2Projector B)
-- 78: 
-- 79: /-- The projected stress readout is invariant under a second projection. -/
-- 80: @[rep_depth transport]
-- 81: theorem projectedStressReadout_projected (B : EndH) :
-- 82:     C.projectedStressReadout (C.spin2Projector B) =
-- 83:       C.projectedStressReadout B := by
```

## 11. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.doubleTransportCommutator_projectedStress_eq_fierzHilbert`

- Score: `628.055625`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `108`

Layer note: modular/transport/flow substrate

Doc:

The same stress readout through the double transport-commutator presentation
of the BKM proxy.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_acc19c6fd024e9f9b8fbb744082f176273a352af`
- SCC: `scc_373c542f0ed0211dc321c03ce89559f65bd275fe`
- Witness backed: `True`

```lean
-- 104:         (C.projectedState (operatorInformationHessian (E := E) X A)) :=
-- 105:   C.projectedStressReadout_eq_fierzHilbert
-- 106:     (operatorInformationHessian (E := E) X A)
-- 107: 
-- 108: /--
-- 109: The same stress readout through the double transport-commutator presentation
-- 110: of the BKM proxy.
-- 111: -/
-- 112: @[rep_depth transport]
```

## 12. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.projectedState`

- Score: `619.447019`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `def`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `74`

Layer note: modular/transport/flow substrate

Doc:

Projected Fierz state of an arbitrary operator response. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_ab247abff200e3734e85fc88e656120d979b10c9`
- SCC: `scc_9f8d88ac7e2eec538efbc9ece35426b5d9e6a37b`
- Witness backed: `True`

```lean
-- 70: @[rep_depth transport]
-- 71: def projectedStressReadout (B : EndH) : ℝ :=
-- 72:   C.stressTensorReadout (C.spin2Projector B)
-- 73: 
-- 74: /-- Projected Fierz state of an arbitrary operator response. -/
-- 75: @[rep_depth transport]
-- 76: def projectedState (B : EndH) : H₂ :=
-- 77:   C.projectedFierzState (C.spin2Projector B)
-- 78: 
```

## 13. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.casesOn`

- Score: `615.037396`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `36`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_37acb430f879d79a6596c65fc3d87b7ea4d1c9eb`
- SCC: `scc_8d5435a5b7c514d10460c77b33d34e0a98122024`
- Witness backed: `True`

```lean
-- 32: 
-- 33: local notation "H₂" => DoubledSpace E
-- 34: local notation "EndH" => H₂ →L[ℝ] H₂
-- 35: 
-- 36: /--
-- 37: Proof-carrying Fierz projection context for the stress-tensor shadow of the
-- 38: operatorial Hessian.
-- 39: 
-- 40: `spin2Projector` is intentionally supplied as data.  The repo does not yet
```

## 14. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.mk.noConfusion`

- Score: `615.037396`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `46`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_cccedc3839c27800c41fdcc1a329d1cbf76b27ef`
- SCC: `scc_e3360b029eb6fa4ef74cb04ab7bae10a7d305053`
- Witness backed: `True`

```lean
-- 42: context records exactly what must be provided before the Hessian may be read as
-- 43: a stress-tensor channel.
-- 44: -/
-- 45: @[rep_depth transport]
-- 46: structure FierzStressProjectionContext where
-- 47:   /-- Candidate spin-2 projection on operator Hessian responses. -/
-- 48:   spin2Projector : EndH → EndH
-- 49:   /-- State readout used to evaluate Fierz channels after projection. -/
-- 50:   projectedFierzState : EndH → H₂
```

## 15. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.noConfusion`

- Score: `615.037396`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `36`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_235ed5092f21b67cb1d7e375b7ef7abd3f0a8521`
- SCC: `scc_f00f4e215655a753bd012f9b5c5a7bff9cbb41a5`
- Witness backed: `True`

```lean
-- 32: 
-- 33: local notation "H₂" => DoubledSpace E
-- 34: local notation "EndH" => H₂ →L[ℝ] H₂
-- 35: 
-- 36: /--
-- 37: Proof-carrying Fierz projection context for the stress-tensor shadow of the
-- 38: operatorial Hessian.
-- 39: 
-- 40: `spin2Projector` is intentionally supplied as data.  The repo does not yet
```

## 16. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.recOn`

- Score: `615.037396`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `36`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_623e757f29d307b8ac489e79be9c40d3dc56d0cb`
- SCC: `scc_c50bca40a1c43f9b85f7d4b1e9734bd506c5cd97`
- Witness backed: `True`

```lean
-- 32: 
-- 33: local notation "H₂" => DoubledSpace E
-- 34: local notation "EndH" => H₂ →L[ℝ] H₂
-- 35: 
-- 36: /--
-- 37: Proof-carrying Fierz projection context for the stress-tensor shadow of the
-- 38: operatorial Hessian.
-- 39: 
-- 40: `spin2Projector` is intentionally supplied as data.  The repo does not yet
```

## 17. `InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian_eq_observableLieHessian`

- Score: `614.916422`
- Distance: `None`
- Module: `InfoGeometry.Canonical.OperatorialHessianBridge`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/OperatorialHessianBridge.lean`
- Line: `310`

Layer note: modular/transport/flow substrate

Doc:

The Operatorial Information Hessian equals the raw algebraic Lie Hessian.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_759d7825a747e4028898ef8bc1cdebbcd205f0e9`
- SCC: `scc_84f645b7b76b3b60c2fb41a60f58abc25688ef67`
- Witness backed: `True`

```lean
-- 306:     operatorInformationHessian (E := E) X A = transportCommutator X (transportCommutator X A) := by
-- 307:   unfold operatorInformationHessian
-- 308:   rw [← lieBracket_eq_transportCommutator, ← lieBracket_eq_transportCommutator]
-- 309: 
-- 310: /--
-- 311: The Operatorial Information Hessian equals the raw algebraic Lie Hessian.
-- 312: -/
-- 313: @[rep_depth transport]
-- 314: theorem operatorInformationHessian_eq_observableLieHessian (X A : EndH) :
```

## 18. `InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian_eq_double_transportCommutator`

- Score: `614.228`
- Distance: `None`
- Module: `InfoGeometry.Canonical.OperatorialHessianBridge`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/OperatorialHessianBridge.lean`
- Line: `300`

Layer note: modular/transport/flow substrate

Doc:

The Operatorial Information Hessian matches the explicit double transport
commutator (the formalization of the Bogoliubov-Kubo-Mori BKM metric proxy).


Faithful witness:

- Raw doc: `raw_info_nodes/raw_06871a1164d201b34612974468f0a90f0a0c4e93`
- SCC: `scc_c3432b86e50b9f7b3239eba4d8fbdc22eaf3ec39`
- Witness backed: `True`

```lean
-- 296: @[rep_depth transport]
-- 297: def observableLieHessian (X A : EndH) : EndH :=
-- 298:   X * (X * A - A * X) - (X * A - A * X) * X
-- 299: 
-- 300: /--
-- 301: The Operatorial Information Hessian matches the explicit double transport
-- 302: commutator (the formalization of the Bogoliubov-Kubo-Mori BKM metric proxy).
-- 303: -/
-- 304: @[rep_depth transport]
```

## 19. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.stress_eq_fierzHilbert`

- Score: `614.02104`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `60`

Doc:

Compatibility gate: projected stress equals the Hilbert/Fierz channel of the
projected operator's associated doubled state.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_0157bf121f8e13ec57b9f51d1d9702a4e3bb1543`
- SCC: `scc_f97e22e23ad8e74ae717bce63eb57ce5ab3f1097`
- Witness backed: `True`

```lean
-- 56:   /--
-- 57:   Compatibility gate: projected stress equals the Hilbert/Fierz channel of the
-- 58:   projected operator's associated doubled state.
-- 59:   -/
-- 60:   stress_eq_fierzHilbert :
-- 61:     ∀ B : EndH,
-- 62:       stressTensorReadout (spin2Projector B) =
-- 63:         infoHilbert (E := E) (projectedFierzState (spin2Projector B))
-- 64: 
```

## 20. `InfoGeometry.Canonical.OperatorialHessianBridge.deriv2_scalarLogReadout_zero_eq_probe_operatorInformationHessian_of_stationary`

- Score: `613.378703`
- Distance: `None`
- Module: `InfoGeometry.Canonical.OperatorialHessianBridge`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/OperatorialHessianBridge.lean`
- Line: `225`

Layer note: modular/transport/flow substrate

Doc:

Normalized stationary scalar log-Hessian bridge. If the scalar readout is
normalized at the seed and the first scalar Lie variation vanishes, the scalar
second derivative of the logarithmic readout is exactly the probe of the
operatorial Lie Hessian.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_0b21bcc46b5d73d070629396229c831284364c40`
- SCC: `scc_2bd159fef51afcdce0c4fcf9284c6b087fdd719d`
- Witness backed: `True`

```lean
-- 221:     simpa [g, f] using deriv2_scalarTransportReadout_zero (E := E) ω X A
-- 222:   rw [hg0, hfderiv0, hgderiv0]
-- 223:   ring
-- 224: 
-- 225: /--
-- 226: Normalized stationary scalar log-Hessian bridge. If the scalar readout is
-- 227: normalized at the seed and the first scalar Lie variation vanishes, the scalar
-- 228: second derivative of the logarithmic readout is exactly the probe of the
-- 229: operatorial Lie Hessian.
```

## 21. `InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian`

- Score: `611.493612`
- Distance: `None`
- Module: `InfoGeometry.Canonical.OperatorialHessianBridge`
- Declaration kind: `def`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/OperatorialHessianBridge.lean`
- Line: `285`

Layer note: modular/transport/flow substrate

Doc:

The Operatorial Information Hessian (BKM metric proxy) is the double
transport commutator.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_33e8a8dca34affc3940edf0e8b582ed8b0363732`
- SCC: `scc_4e9ab382af0e73b5baa38884620f5efd88540282`
- Witness backed: `True`

```lean
-- 281:   rw [CertifiedModularReduction.modularLieHessian_eq_nested_commutator (c := c) A]
-- 282:   rw [lieBracket_eq_transportCommutator]
-- 283:   rw [lieBracket_eq_transportCommutator]
-- 284: 
-- 285: /--
-- 286: The Operatorial Information Hessian (BKM metric proxy) is the double
-- 287: transport commutator.
-- 288: -/
-- 289: @[rep_depth transport]
```

## 22. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.projectedFierzState`

- Score: `611.3195`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `50`

Doc:

State readout used to evaluate Fierz channels after projection. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_8c8cd859bd80745a08985fb593430ea7035c3b83`
- SCC: `scc_a425b8b1a38c4bee9c0639a8eeccb7c3f39fb501`
- Witness backed: `True`

```lean
-- 46: structure FierzStressProjectionContext where
-- 47:   /-- Candidate spin-2 projection on operator Hessian responses. -/
-- 48:   spin2Projector : EndH → EndH
-- 49:   /-- State readout used to evaluate Fierz channels after projection. -/
-- 50:   projectedFierzState : EndH → H₂
-- 51:   /-- Stress-tensor scalar readout on projected operator responses. -/
-- 52:   stressTensorReadout : EndH → ℝ
-- 53:   /-- The spin-2 projection is a projector on the operator lane. -/
-- 54:   spin2Projector_idempotent :
```

## 23. `InfoGeometry.Canonical.FierzStressProjectionBridge.FierzStressProjectionContext.mk`

- Score: `609.170833`
- Distance: `None`
- Module: `InfoGeometry.Canonical.FierzStressProjectionBridge`
- Declaration kind: `constructor`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- Line: `46`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_6abfe2c59bd0163cf63a75c9d24e613a5f342780`
- SCC: `scc_5adcef1981af363bb3f603cc78a931b03467a0e0`
- Witness backed: `True`

```lean
-- 42: context records exactly what must be provided before the Hessian may be read as
-- 43: a stress-tensor channel.
-- 44: -/
-- 45: @[rep_depth transport]
-- 46: structure FierzStressProjectionContext where
-- 47:   /-- Candidate spin-2 projection on operator Hessian responses. -/
-- 48:   spin2Projector : EndH → EndH
-- 49:   /-- State readout used to evaluate Fierz channels after projection. -/
-- 50:   projectedFierzState : EndH → H₂
```

## 24. `InfoGeometry.Canonical.SuperchargeRoleBridge.deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian_of_paritySuperchargeOp`

- Score: `608.829261`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SuperchargeRoleBridge`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SuperchargeRoleBridge.lean`
- Line: `136`

Layer note: modular/transport/flow substrate

Doc:

The second transport landing of the primitive parity supercharge is exactly
the operatorial Hessian evaluated on the same carrier operator `J`.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_b64009133d6f48cfa2a1fe0634b14f9d5366f3e6`
- SCC: `scc_822a886f698cd197cbcb5d8d89efc649a36b5cb3`
- Witness backed: `True`

```lean
-- 132:   simpa using
-- 133:     transportedParityModularGapSeed_eq_phaseAntilinearCAR_of_commute_phaseLinearPart
-- 134:       (E := E) V hComm
-- 135: 
-- 136: /--
-- 137: The second transport landing of the primitive parity supercharge is exactly
-- 138: the operatorial Hessian evaluated on the same carrier operator `J`.
-- 139: -/
-- 140: @[rep_depth transport]
```

## 25. `InfoGeometry.Canonical.SuperchargeRoleBridge.deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian_of_modular_j`

- Score: `603.99826`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SuperchargeRoleBridge`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SuperchargeRoleBridge.lean`
- Line: `152`

Layer note: modular/transport/flow substrate

Doc:

Root-name form of the second transport landing as operatorial Hessian. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_3840a1191602f2d89d239b15224253ff9092e47e`
- SCC: `scc_979a622b948ff1ec30cb55c33d402338a65d00ee`
- Witness backed: `True`

```lean
-- 148:   simpa [paritySuperchargeOp] using
-- 149:     deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian
-- 150:       (E := E) V
-- 151: 
-- 152: /-- Root-name form of the second transport landing as operatorial Hessian. -/
-- 153: @[rep_depth transport]
-- 154: theorem deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian_of_modular_j
-- 155:     (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
-- 156:     let X := V.connectionGenerator
```
