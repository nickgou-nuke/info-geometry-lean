# Gravitational Lean Context

- Query: `CoordinatelessSouriauKMSBridge CyclicAlgebraicState KMSState ModularTimeKMSContext identityAdditiveModularFlow infinite operator algebra`
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

- `EQC-0220` matched `algebraic, coordinateless, kmsbridge, souriau, state`; added `canonical, eval, geometric, geometry, info, metric, quantum, tensor`
- `EQC-0382` matched `flow, modular, souriau, time`; added `thermal, tomita`
- `EQC-0125` matched `additive, flow, modular, souriau`; added `carrier, form, krein, seed, shift, standard`
- `EQC-0135` matched `flow, souriau, time`; added ``
- `EQC-0171` matched `modular, souriau, time`; added `derivation, lie`
- `EQC-0110` matched `modular, operator, souriau`; added `context, hamiltonian, log, moment`
- `EQC-0328` matched `additive, flow, modular`; added `automorphism, data, group, nikodym, radon`
- `EQC-0115` matched `modular, operator, souriau`; added `delta, generator, negative, real`

## 1. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.ModularTimeKMSContext.modular_time_zero`

- Score: `1038.409249`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `theorem`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `307`

Layer note: operator-algebraic bridge substrate

Doc:

Modular time starts at the identity automorphism. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_a453b51b0277051208be2f003bb70dd9f789a144`
- SCC: `scc_f3d690cf4c1f415330abfecc0a63d1aefbff23a7`
- Witness backed: `True`

```lean
-- 303: theorem modular_time_add (s t : ℝ) :
-- 304:     M.sigma (s + t) = M.sigma s * M.sigma t :=
-- 305:   AdditiveModularFlow.map_add M.sigma s t
-- 306: 
-- 307: /-- Modular time starts at the identity automorphism. -/
-- 308: @[rep_depth operator]
-- 309: theorem modular_time_zero :
-- 310:     M.sigma 0 = 1 :=
-- 311:   AdditiveModularFlow.map_zero M.sigma
```

## 2. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.ModularTimeKMSContext.modular_time_add`

- Score: `1032.34`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `theorem`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `301`

Layer note: operator-algebraic bridge substrate

Doc:

Modular time is additive: `σ_{s+t}=σ_s σ_t`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_2f9d11ff4ca28b3bcd2e4f4508720e307bb3ea8e`
- SCC: `scc_cf84d516f67c7550fd208b28411c692515c1bbcc`
- Witness backed: `True`

```lean
-- 297: namespace ModularTimeKMSContext
-- 298: 
-- 299: variable (M : ModularTimeKMSContext (H := H))
-- 300: 
-- 301: /-- Modular time is additive: `σ_{s+t}=σ_s σ_t`. -/
-- 302: @[rep_depth operator]
-- 303: theorem modular_time_add (s t : ℝ) :
-- 304:     M.sigma (s + t) = M.sigma s * M.sigma t :=
-- 305:   AdditiveModularFlow.map_add M.sigma s t
```

## 3. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.ModularTimeKMSContext.kms_eval_mul_modular_eq_eval_flip`

- Score: `1025.802174`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `theorem`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `313`

Layer note: operator-algebraic bridge substrate

Doc:

KMS identity expressed through the modular-time context. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_3bf05688613ded6cfe96ab8364fbe847213d69f4`
- SCC: `scc_224de67a54e5309d9ee23a39944a6701944ccce0`
- Witness backed: `True`

```lean
-- 309: theorem modular_time_zero :
-- 310:     M.sigma 0 = 1 :=
-- 311:   AdditiveModularFlow.map_zero M.sigma
-- 312: 
-- 313: /-- KMS identity expressed through the modular-time context. -/
-- 314: @[rep_depth operator]
-- 315: theorem kms_eval_mul_modular_eq_eval_flip (A B : Obs) :
-- 316:     M.kms.state.eval (A * M.sigma M.beta B) = M.kms.state.eval (B * A) :=
-- 317:   M.kms.eval_mul_modular_eq_eval_flip A B
```

## 4. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicAlgebraicState.identityKMS_eval_mul_modular_eq_eval_flip`

- Score: `1023.008216`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `theorem`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `147`

Layer note: operator-algebraic bridge substrate

Faithful witness:

- Raw doc: `raw_info_nodes/raw_e6ca56a0fef6fab5f060d0f58fe74d8cbea55567`
- SCC: `scc_3d878d68c0e60d1e1d4e2e2bb3dd5aaac586a68b`
- Witness backed: `True`

```lean
-- 143:   kms_identity := by
-- 144:     intro A B
-- 145:     simpa [identityAdditiveModularFlow] using ω.cyclic A B
-- 146: 
-- 147: @[rep_depth operator]
-- 148: theorem identityKMS_eval_mul_modular_eq_eval_flip (beta : ℝ) (A B : Obs) :
-- 149:     (ω.toIdentityKMSState beta).state.eval
-- 150:         (A * (identityAdditiveModularFlow (H := H)) beta B) =
-- 151:       (ω.toIdentityKMSState beta).state.eval (B * A) :=
```

## 5. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicAlgebraicState.sldQuantumFisherMetric_symm`

- Score: `1015.47027`
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

## 6. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicAlgebraicState.cyclic`

- Score: `1010.3125`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `76`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_e8a1f3e7d0b04e6a5a31351f3ff89417ed3cb3c7`
- SCC: `scc_bc74c6201fb3c1f3f2b7a9090d61a1836eab7892`
- Witness backed: `True`

```lean
-- 72: -/
-- 73: @[rep_depth operator]
-- 74: structure CyclicAlgebraicState where
-- 75:   state : AlgebraicState (H := H)
-- 76:   cyclic : ∀ A B : Obs, state.eval (A * B) = state.eval (B * A)
-- 77: 
-- 78: namespace CyclicAlgebraicState
-- 79: 
-- 80: variable (ω : CyclicAlgebraicState (H := H))
```

## 7. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.ModularTimeKMSContext`

- Score: `1007.589972`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `inductive`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `285`

Layer note: operator-algebraic bridge substrate

Doc:

Modular-time package for a KMS state.

This is the coordinate-free replacement for an external time coordinate: time is
the additive parameter of the modular automorphism group.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_d71555aa361a0821d1d9252377a97dab5cae2a38`
- SCC: `scc_a41dbc13fb8d9bc518f6c76f8163a3068afdc702`
- Witness backed: `True`

```lean
-- 281:   state_invariant := by
-- 282:     intro A
-- 283:     rfl
-- 284: 
-- 285: /--
-- 286: Modular-time package for a KMS state.
-- 287: 
-- 288: This is the coordinate-free replacement for an external time coordinate: time is
-- 289: the additive parameter of the modular automorphism group.
```

## 8. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.identityAdditiveModularFlow`

- Score: `1004.562764`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `def`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `89`

Layer note: operator-algebraic bridge substrate

Doc:

Identity modular flow on the observable algebra. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_23b78efbc6b8c7d01b2c40d047bd493530d52454`
- SCC: `scc_e909be04427d412d62d7df68b86ebf4b93fb0b64`
- Witness backed: `True`

```lean
-- 85:   ω.cyclic A B
-- 86: 
-- 87: end CyclicAlgebraicState
-- 88: 
-- 89: /-- Identity modular flow on the observable algebra. -/
-- 90: @[rep_depth operator]
-- 91: def identityAdditiveModularFlow : AdditiveModularFlow (H := H) where
-- 92:   toFun := fun _ => 1
-- 93:   map_zero' := rfl
```

## 9. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicAlgebraicState.eval_mul_comm`

- Score: `1002.551793`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `theorem`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `82`

Layer note: operator-algebraic bridge substrate

Faithful witness:

- Raw doc: `raw_info_nodes/raw_790af771f951119468f741c2517a9e7efd436c8a`
- SCC: `scc_95da9efd5a9a72aebbce952dd6ea9b57e99e7619`
- Witness backed: `True`

```lean
-- 78: namespace CyclicAlgebraicState
-- 79: 
-- 80: variable (ω : CyclicAlgebraicState (H := H))
-- 81: 
-- 82: @[rep_depth operator]
-- 83: theorem eval_mul_comm (A B : Obs) :
-- 84:     ω.state.eval (A * B) = ω.state.eval (B * A) :=
-- 85:   ω.cyclic A B
-- 86: 
```

## 10. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicAlgebraicState.toIdentityKMSState`

- Score: `1002.13947`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `def`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `133`

Layer note: operator-algebraic bridge substrate

Doc:

Constructive KMS state on the identity modular branch.

No density matrix or trace is introduced: the proof is exactly cyclicity of the
algebraic state.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_33fff2d02a47129278106b4b0b37ffd077db82d6`
- SCC: `scc_03d9f8460bfdd151c09e922afe2a5515d1400025`
- Witness backed: `True`

```lean
-- 129: namespace CyclicAlgebraicState
-- 130: 
-- 131: variable (ω : CyclicAlgebraicState (H := H))
-- 132: 
-- 133: /--
-- 134: Constructive KMS state on the identity modular branch.
-- 135: 
-- 136: No density matrix or trace is introduced: the proof is exactly cyclicity of the
-- 137: algebraic state.
```

## 11. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicAlgebraicState.toCoordinatelessSouriauFisherContext`

- Score: `1001.32074`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `def`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `423`

Layer note: operator-algebraic bridge substrate

Doc:

Constructive coordinateless Souriau/KMS/Fisher packet on the cyclic identity
modular branch.

This proves the table entries that are constructible from the current repo
owners: algebraic state normalization, KMS identity, operator-valued Souriau
moment, SLD/Fisher symmetry, and Weyl identity-gauge invariance.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_24e12dc2d974de4989e942c0f1e7c080b7df4db5`
- SCC: `scc_fa68713a268d231703355033b08131df79480f36`
- Witness backed: `True`

```lean
-- 419: 
-- 420: variable {Symmetry : Type v} {Tangent : Type v}
-- 421: variable (ω : CyclicAlgebraicState (H := H))
-- 422: 
-- 423: /--
-- 424: Constructive coordinateless Souriau/KMS/Fisher packet on the cyclic identity
-- 425: modular branch.
-- 426: 
-- 427: This proves the table entries that are constructible from the current repo
```

## 12. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.CyclicAlgebraicState.state`

- Score: `983.381133`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `75`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_38caeca163d0b9ec4330a338d058de0ed0994335`
- SCC: `scc_e2d44e2156da78b09ee2d064c26356b24a5adf03`
- Witness backed: `True`

```lean
-- 71: trivial-modular KMS branch and to prove SLD/Fisher symmetry.
-- 72: -/
-- 73: @[rep_depth operator]
-- 74: structure CyclicAlgebraicState where
-- 75:   state : AlgebraicState (H := H)
-- 76:   cyclic : ∀ A B : Obs, state.eval (A * B) = state.eval (B * A)
-- 77: 
-- 78: namespace CyclicAlgebraicState
-- 79: 
```
