# Gravitational Lean Context

- Query: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem.fisher_onsager_metriplectic_constructive_proof_packet`
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

- `EQC-0259` matched `canonical, coadjoint, geometry, info, metriplectic, orbit, souriau`; added `context, ent, finite, image, infinite, jaynes, max, moment, problem`
- `EQC-0221` matched `canonical, geometry, info, souriau`; added `coarse, dirac, grain, sector, zorn`
- `EQC-0260` matched `canonical, geometry, info, souriau`; added `beta, geometric, pairing, temperature, thermodynamics, weight`
- `EQC-0081` matched `canonical, geometry, info, souriau`; added `density, energy, grand, param, two`
- `EQC-0220` matched `canonical, geometry, info, souriau`; added `algebraic, coordinateless, eval, kmsbridge, metric, quantum, state, tensor`
- `EQC-0247` matched `canonical, geometry, info, orbit`; added `algebroid, axis, clock, closure, complex, dictionary, dilation, equivariance, hestenes, internal, krein, lie, modular, operator, phase, projector, real, rosetta, takesaki, tomita, winding`
- `EQC-0032` matched `coadjoint, metriplectic, orbit`; added `entropy, rate`
- `EQC-0151` matched `canonical, geometry, info`; added `conformal, inference, unification`

## 1. `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.SouriauLieThermoKKTContext`

- Score: `351.302586`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauLieThermoKKTBridge`
- Declaration kind: `inductive`
- Representation layer: `L5_ThermodynamicClosure`
- Representation depth: `5`
- Representation slug: `thermo`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean`
- Line: `679`

Layer note: thermodynamic/free-energy/closure substrate

Doc:

Combined Souriau Lie-thermodynamic optimization context.

The equalities keep the finite Fenchel, finite metriplectic, and conformal
density-weight shadows on the same Souriau moment map and geometric
temperature.  The operatorial Krein/Onsager lane is carried separately because
it lives on the doubled operator carrier, not on the finite state space.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_ce575f190416177d052b5209b6012375a646d489`
- SCC: `scc_ccf560995c7acb52ad324a18e383e0a0215c132c`
- Witness backed: `True`

```lean
-- 675: attribute [terminal] algebraic_equilibrium_packet
-- 676: 
-- 677: end CoordinatelessKMSFisherState
-- 678: 
-- 679: /--
-- 680: Combined Souriau Lie-thermodynamic optimization context.
-- 681: 
-- 682: The equalities keep the finite Fenchel, finite metriplectic, and conformal
-- 683: density-weight shadows on the same Souriau moment map and geometric
```

## 2. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitMetriplecticContext.geometricTemperature`

- Score: `330.153034`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `46`

Doc:

Souriau geometric temperature, i.e. a Lie-algebra generator. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_c3eaa3dd0a635b80170c2f877abc3a20be130b19`
- SCC: `scc_f43c82f70ee3b8b4a5af954245fd5736336f69a7`
- Witness backed: `True`

```lean
-- 42:     (Orbit : Type u) (LieAlg : Type v) (LieCoalg : Type w) where
-- 43:   /-- Moment map into the coadjoint dual lane. -/
-- 44:   moment : Orbit → LieCoalg
-- 45:   /-- Souriau geometric temperature, i.e. a Lie-algebra generator. -/
-- 46:   geometricTemperature : LieAlg
-- 47:   /-- Predicate selecting the coadjoint orbit containing the moment image. -/
-- 48:   isOnCoadjointOrbit : LieCoalg → Prop
-- 49:   /-- Reversible/Hamiltonian generator on the orbit. -/
-- 50:   reversibleVectorField : Orbit → Orbit
```

## 3. `InfoGeometry.Canonical.SouriauThermodynamics.geometricTemperatureWeightPairing_eq_beta_mul_shiftedMomentReadout`

- Score: `328.943566`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauThermodynamics`
- Declaration kind: `theorem`
- Representation layer: `L5_ThermodynamicClosure`
- Representation depth: `5`
- Representation slug: `thermo`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SouriauThermodynamics.lean`
- Line: `89`

Layer note: thermodynamic/free-energy/closure substrate

Doc:

The finite Souriau weight pairing is exactly the exponent observable used by
the grand-canonical Gibbs kernel.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_28f625ee8c18ae7cdf31a6d370b714d2b4513661`
- SCC: `scc_a03331c1cb9dd6bad22a5aadc3b47d5816738c1e`
- Witness backed: `True`

```lean
-- 85: noncomputable def shiftedMomentReadout
-- 86:     (M : SouriauMomentMap α) (T : GeometricTemperature) (x : α) : ℝ :=
-- 87:   shiftedEnergy (toGrandCanonicalTwoParam M) T.mu x
-- 88: 
-- 89: /--
-- 90: The finite Souriau weight pairing is exactly the exponent observable used by
-- 91: the grand-canonical Gibbs kernel.
-- 92: -/
-- 93: @[rep_depth thermo]
```

## 4. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.entropy_gradient_eq_beta_holds`

- Score: `326.684601`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `528`

Doc:

Proof that the entropy gradient recovers the geometric-temperature coordinate. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_b7aa9752e72452f95ba0c596fe522f89752ac0ad`
- SCC: `scc_914f612464aec96af0630a94f25cf9a3efb89826`
- Witness backed: `True`

```lean
-- 524:   /-- Entropy gradient recovers the geometric-temperature coordinate. -/
-- 525:   entropy_gradient_eq_beta : Prop
-- 526:   /-- Proof that the entropy gradient recovers the geometric-temperature coordinate. -/
-- 527: -- theorem-class: bridge
-- 528:   entropy_gradient_eq_beta_holds : entropy_gradient_eq_beta
-- 529:   /-- Entropy Hessian is the inverse Fisher metric on the coadjoint dual lane. -/
-- 530: -- theorem-class: bridge
-- 531:   entropy_hessian_eq_inverse_fisher :
-- 532:     ∀ (Q : LieCoalg),
```

## 5. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.entropy_gradient_eq_beta`

- Score: `321.80525`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `525`

Doc:

Entropy gradient recovers the geometric-temperature coordinate. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_770ec9ba6136b47e5e5dcb425e1f7b9bdeafacbc`
- SCC: `scc_7325ff973e56dd0f810c2dc6294233267fe60967`
- Witness backed: `True`

```lean
-- 521:   /-- Proof of the Fenchel-Legendre contact equation. -/
-- 522: -- theorem-class: bridge
-- 523:   fenchel_legendre_contact_holds : fenchel_legendre_contact
-- 524:   /-- Entropy gradient recovers the geometric-temperature coordinate. -/
-- 525:   entropy_gradient_eq_beta : Prop
-- 526:   /-- Proof that the entropy gradient recovers the geometric-temperature coordinate. -/
-- 527: -- theorem-class: bridge
-- 528:   entropy_gradient_eq_beta_holds : entropy_gradient_eq_beta
-- 529:   /-- Entropy Hessian is the inverse Fisher metric on the coadjoint dual lane. -/
```

## 6. `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.dimensionAgnostic_squareDissipation_secondLaw`

- Score: `320.435256`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauLieThermoKKTBridge`
- Declaration kind: `theorem`
- Representation layer: `L5_ThermodynamicClosure`
- Representation depth: `5`
- Representation slug: `thermo`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean`
- Line: `599`

Layer note: thermodynamic/free-energy/closure substrate

Doc:

Dimension-agnostic constructive second law for the full coadjoint-orbit lane.

This is not the finite Souriau shadow.  It routes through
`InfiniteCoadjointOrbitMetriplecticContext.ofMomentImageSquareDissipation`,
where the reversible entropy channel is definitionally zero and the
dissipative/total channel is a square of a real dissipation amplitude.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_612a96d27dbc3d4fc883376349c1113d46dfc5b6`
- SCC: `scc_92b560c10625475206901dfd47bd469a5d05d3b2`
- Witness backed: `True`

```lean
-- 595: 
-- 596: variable {G Gdual Orbit : Type*}
-- 597: 
-- 598: -- theorem-class: bridge
-- 599: /--
-- 600: Dimension-agnostic constructive second law for the full coadjoint-orbit lane.
-- 601: 
-- 602: This is not the finite Souriau shadow.  It routes through
-- 603: `InfiniteCoadjointOrbitMetriplecticContext.ofMomentImageSquareDissipation`,
```

## 7. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitMetriplecticContext.metricEntropyRate`

- Score: `319.287375`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `58`

Doc:

Metric/Onsager entropy-production channel. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_1f346cc802f709e15cd33c853cab9b7dcbf6738a`
- SCC: `scc_7cd8d6634e6c44ba05c312dd636353c2b146f01e`
- Witness backed: `True`

```lean
-- 54:   entropy : Orbit → ℝ
-- 55:   /-- Reversible entropy-production channel. -/
-- 56:   reversibleEntropyRate : Orbit → ℝ
-- 57:   /-- Metric/Onsager entropy-production channel. -/
-- 58:   metricEntropyRate : Orbit → ℝ
-- 59:   /-- Total metriplectic entropy-production channel. -/
-- 60:   totalEntropyRate : Orbit → ℝ
-- 61:   /-- The moment image lies on the selected coadjoint orbit. -/
-- 62: -- theorem-class: bridge
```

## 8. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitMetriplecticContext.moment_mem_orbit`

- Score: `317.063117`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `63`

Doc:

The moment image lies on the selected coadjoint orbit. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_8ef200b03190a95aff5d998aba423ad9083af496`
- SCC: `scc_5adca96e763ab25dfa7d9a16793034a67deb8afc`
- Witness backed: `True`

```lean
-- 59:   /-- Total metriplectic entropy-production channel. -/
-- 60:   totalEntropyRate : Orbit → ℝ
-- 61:   /-- The moment image lies on the selected coadjoint orbit. -/
-- 62: -- theorem-class: bridge
-- 63:   moment_mem_orbit : ∀ x : Orbit, isOnCoadjointOrbit (moment x)
-- 64:   /-- Hamiltonian/coadjoint motion closes on the same orbit. -/
-- 65: -- theorem-class: bridge
-- 66:   reversible_preserves_orbit :
-- 67:     ∀ x : Orbit, isOnCoadjointOrbit (moment (reversibleVectorField x))
```

## 9. `InfoGeometry.Canonical.SouriauTomitaModularFlowBridge.SouriauTomitaLogContext.modularHamiltonian_eq_moment_geometricTemperature`

- Score: `316.95056`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauTomitaModularFlowBridge`
- Declaration kind: `theorem`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SouriauTomitaModularFlowBridge.lean`
- Line: `170`

Layer note: operator-algebraic bridge substrate

Doc:

The modular Hamiltonian is the Souriau moment at geometric temperature. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_3ea155ae002f7c46d50babb794c15e747cb83c14`
- SCC: `scc_014a2210de5368a9d147551d30b761741a5b9c1c`
- Witness backed: `True`

```lean
-- 166:     C.souriauMoment.thermalGenerator =
-- 167:       C.souriauMoment.momentOperator C.souriauMoment.geometricTemperature :=
-- 168:   C.souriauMoment.thermalGenerator_eq_moment_geometricTemperature
-- 169: 
-- 170: /-- The modular Hamiltonian is the Souriau moment at geometric temperature. -/
-- 171: @[rep_depth operator]
-- 172: theorem modularHamiltonian_eq_moment_geometricTemperature :
-- 173:     C.modularHamiltonian =
-- 174:       C.souriauMoment.momentOperator C.souriauMoment.geometricTemperature :=
```

## 10. `InfoGeometry.Canonical.SouriauTomitaModularFlowBridge.SouriauTomitaLogContext.souriauModularGenerator_eq_moment_geometricTemperature`

- Score: `316.928143`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauTomitaModularFlowBridge`
- Declaration kind: `theorem`
- Representation layer: `L2_Operator`
- Representation depth: `2`
- Representation slug: `operator`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SouriauTomitaModularFlowBridge.lean`
- Line: `163`

Layer note: operator-algebraic bridge substrate

Doc:

The Souriau modular generator is the moment at geometric temperature. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_c3d4313b5094121c66038391c4dae1221c645b38`
- SCC: `scc_e300c5ca7b30386864adb2c2585b80ee919a97d7`
- Witness backed: `True`

```lean
-- 159:         (E := H) C.souriauMoment.thermalGenerator t A :=
-- 160:   additiveModularFlowOfGenerator_apply
-- 161:     (H := H) C.souriauMoment.thermalGenerator t A
-- 162: 
-- 163: /-- The Souriau modular generator is the moment at geometric temperature. -/
-- 164: @[rep_depth operator]
-- 165: theorem souriauModularGenerator_eq_moment_geometricTemperature :
-- 166:     C.souriauMoment.thermalGenerator =
-- 167:       C.souriauMoment.momentOperator C.souriauMoment.geometricTemperature :=
```

## 11. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitMetriplecticContext.metric_flow_closes_on_coadjoint_orbit`

- Score: `313.944045`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `339`

Layer note: modular/transport/flow substrate

Doc:

Metric/Onsager flow is a valid orbit-level state update. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_54f73953e665cb12b442c91e85d128c106b36013`
- SCC: `scc_f90c3c05e882b65e691d39ae70923a6541e5d359`
- Witness backed: `True`

```lean
-- 335:     C.isOnCoadjointOrbit (C.moment (C.reversibleVectorField x)) :=
-- 336:   C.reversible_preserves_orbit x
-- 337: 
-- 338: -- theorem-class: bridge
-- 339: /-- Metric/Onsager flow is a valid orbit-level state update. -/
-- 340: @[rep_depth transport]
-- 341: theorem metric_flow_closes_on_coadjoint_orbit (x : Orbit) :
-- 342:     C.isOnCoadjointOrbit (C.moment (C.metricVectorField x)) :=
-- 343:   C.metric_preserves_state x
```

## 12. `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge.OperatorSouriauMoment.geometricTemperature`

- Score: `313.0211`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- Line: `165`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_3e51f6fb7e95744c4933dfad71bb77f30cdfec6a`
- SCC: `scc_566a8ae6a78ce066149355d15c358489fe6b3835`
- Witness backed: `True`

```lean
-- 161: -/
-- 162: @[rep_depth operator]
-- 163: structure OperatorSouriauMoment (Symmetry : Type v) where
-- 164:   momentOperator : Symmetry → Obs
-- 165:   geometricTemperature : Symmetry
-- 166: 
-- 167: namespace OperatorSouriauMoment
-- 168: 
-- 169: variable {Symmetry : Type v}
```
