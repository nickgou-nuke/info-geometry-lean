# Gravitational Lean Context

- Query: `InfoGeometry.Canonical.RelativeDeterminantScatteringSocket`
- Graph source: `arango`
- Nodes: `56014`
- Edges: `388729`
- Synonym groups: `0`
- Requested layers: `all`
- Promotion allowed: `false`

## Representation Layers

- `unlabeled`: `56014`

## 1. `InfoGeometry.Canonical.RelativeModularOperator.relativeModularHamiltonianReadout_self`

- Score: `188.896223`
- Distance: `0`
- Module: `InfoGeometry.Canonical.RelativeModularOperator`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean`
- Line: `449`

Doc:

Self-relative modular Hamiltonian readout vanishes.


```lean
-- 445:   rw [relativeModularHamiltonianReadout_eq_inv_card_mul_relativeModularVolumePotential]
-- 446:   rw [relativeModularVolumePotential_cocycle (n := n) q q0 q1]
-- 447:   ring
-- 448: 
-- 449: /--
-- 450: Self-relative modular Hamiltonian readout vanishes.
-- 451: -/
-- 452: @[simp, rep_depth thermo, capstone]
-- 453: theorem relativeModularHamiltonianReadout_self
```

## 2. `InfoGeometry.Canonical.ThermodynamicGenerator.souriauTemperatureVector_eq_stateRelativeModularGenerator`

- Score: `185.652983`
- Distance: `0`
- Module: `InfoGeometry.Canonical.ThermodynamicGenerator`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/ThermodynamicGenerator.lean`
- Line: `66`

```lean
-- 62:     souriauTemperatureVector (E := E) P ψ
-- 63:       =
-- 64:     InfoGeometry.Canonical.RelativeModularPotential.transportGenerator (E := E) P ψ := rfl
-- 65: 
-- 66: @[rep_depth transport, simp] theorem souriauTemperatureVector_eq_stateRelativeModularGenerator
-- 67:     (P : PotentialDatum (E := E)) (ψ : H₂) :
-- 68:     souriauTemperatureVector (E := E) P ψ
-- 69:       =
-- 70:     stateRelativeModularGenerator (E := E) P.modularData ψ := by
```

## 3. `InfoGeometry.Thermo.ModularKLDivergence.relative_modular_hamiltonian_readout_self`

- Score: `169.922964`
- Distance: `0`
- Module: `InfoGeometry.Thermo.ModularKLDivergence`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Thermo/ModularKLDivergence.lean`
- Line: `105`

Doc:

Self-relative modular Hamiltonian readout vanishes. 

```lean
-- 101:   exact
-- 102:     relativeModularHamiltonianReadout_eq_average_relativeModularPotential
-- 103:       (n := n) q q0
-- 104: 
-- 105: /-- Self-relative modular Hamiltonian readout vanishes. -/
-- 106: theorem relative_modular_hamiltonian_readout_self
-- 107:     (q : PositiveRay (Fin n)) :
-- 108:     relativeModularHamiltonianReadout (n := n) q q = 0 := by
-- 109:   exact relativeModularHamiltonianReadout_self (n := n) q
```

## 4. `InfoGeometry.Canonical.RelativeModularHamiltonian.relativeModularHamiltonianExpectation_self`

- Score: `167.818307`
- Distance: `0`
- Module: `InfoGeometry.Canonical.RelativeModularHamiltonian`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean`
- Line: `143`

```lean
-- 139:   rw [relativeModularHamiltonianExpectation_eq_readout]
-- 140:   exact relativeModularHamiltonianReadout_eq_inv_card_mul_relativeModularVolumePotential
-- 141:     (n := n) q q0
-- 142: 
-- 143: @[simp, rep_depth thermo, capstone]
-- 144: theorem relativeModularHamiltonianExpectation_self
-- 145:     (q : PositiveRay (Fin n)) :
-- 146:     relativeModularHamiltonianExpectation (n := n) q q = 0 := by
-- 147:   rw [relativeModularHamiltonianExpectation_eq_readout]
```

## 5. `InfoGeometry.Canonical.RelativeModularOperator.relativeModularVolumePotential_self`

- Score: `163.929521`
- Distance: `0`
- Module: `InfoGeometry.Canonical.RelativeModularOperator`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean`
- Line: `291`

```lean
-- 287:   unfold relativeModularVolumePotential
-- 288:   rw [log_relativeModularVolumeShadow_cocycle (n := n) q q0 q1]
-- 289:   ring
-- 290: 
-- 291: @[simp, rep_depth thermo, capstone]
-- 292: theorem relativeModularVolumePotential_self
-- 293:     (q : PositiveRay (Fin n)) :
-- 294:     relativeModularVolumePotential (n := n) q q = 0 := by
-- 295:   unfold relativeModularVolumePotential
```

## 6. `InfoGeometry.Canonical.RelativeModularOperator.relativeModularVolumeShadow_self`

- Score: `163.929521`
- Distance: `0`
- Module: `InfoGeometry.Canonical.RelativeModularOperator`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean`
- Line: `210`

```lean
-- 206:   intro i hi
-- 207:   rw [relativeDensity_eq_exp_relativeLogDensity]
-- 208:   positivity
-- 209: 
-- 210: @[simp] theorem relativeModularVolumeShadow_self
-- 211:     (q : PositiveRay (Fin n)) :
-- 212:     relativeModularVolumeShadow (n := n) q q = 1 := by
-- 213:   unfold relativeModularVolumeShadow
-- 214:   rw [relativeModularOperator_self]
```

## 7. `InfoGeometry.Canonical.RelativeModularPotential.generator_eq`

- Score: `161.636179`
- Distance: `0`
- Module: `InfoGeometry.Canonical.RelativeModularPotential`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularPotential.lean`
- Line: `169`

```lean
-- 165:   informationFunctional := value (E := E) P
-- 166:   firstVariation := firstVariation (E := E) P
-- 167:   secondVariation := fun ψ => channelCorrelationAtState (E := E) ψ
-- 168: 
-- 169: @[rep_depth transport, simp] theorem generator_eq
-- 170:     (P : PotentialDatum (E := E)) (ψ : H₂) :
-- 171:     generator (E := E) P ψ = stateRelativeModularGenerator (E := E) P.modularData ψ := rfl
-- 172: 
-- 173: @[rep_depth transport, simp] theorem modularSeed_eq
```

## 8. `InfoGeometry.Canonical.RelativeModularPotential.modularSeed_eq`

- Score: `161.636179`
- Distance: `0`
- Module: `InfoGeometry.Canonical.RelativeModularPotential`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularPotential.lean`
- Line: `173`

```lean
-- 169: @[rep_depth transport, simp] theorem generator_eq
-- 170:     (P : PotentialDatum (E := E)) (ψ : H₂) :
-- 171:     generator (E := E) P ψ = stateRelativeModularGenerator (E := E) P.modularData ψ := rfl
-- 172: 
-- 173: @[rep_depth transport, simp] theorem modularSeed_eq
-- 174:     (P : PotentialDatum (E := E)) (ψ : H₂) :
-- 175:     modularSeed (E := E) P ψ = P.modularData.modularSeed ψ := rfl
-- 176: 
-- 177: @[rep_depth transport, simp] theorem transportGenerator_eq
```

## 9. `InfoGeometry.Canonical.RelativeModularPotential.transportGenerator_eq`

- Score: `159.019831`
- Distance: `0`
- Module: `InfoGeometry.Canonical.RelativeModularPotential`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularPotential.lean`
- Line: `177`

```lean
-- 173: @[rep_depth transport, simp] theorem modularSeed_eq
-- 174:     (P : PotentialDatum (E := E)) (ψ : H₂) :
-- 175:     modularSeed (E := E) P ψ = P.modularData.modularSeed ψ := rfl
-- 176: 
-- 177: @[rep_depth transport, simp] theorem transportGenerator_eq
-- 178:     (P : PotentialDatum (E := E)) (ψ : H₂) :
-- 179:     transportGenerator (E := E) P ψ
-- 180:       =
-- 181:     stateRelativeModularGenerator (E := E) P.modularData ψ := rfl
```

## 10. `InfoGeometry.Canonical.RNDeterminantConnesChainBridge.relativeModularVolumeShadow_state_chain`

- Score: `152.092215`
- Distance: `0`
- Module: `InfoGeometry.Canonical.RNDeterminantConnesChainBridge`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean`
- Line: `53`

Doc:

Determinant/Jacobian shadow chain rule on the finite modular operator lane.
This is the determinant-group-homomorphism form of state-to-state composition.


```lean
-- 49:       = relativeModularOperator (n := n) q q0
-- 50:           * relativeModularOperator (n := n) q0 q1 :=
-- 51:   relativeModularOperator_cocycle (n := n) q q0 q1
-- 52: 
-- 53: /--
-- 54: Determinant/Jacobian shadow chain rule on the finite modular operator lane.
-- 55: This is the determinant-group-homomorphism form of state-to-state composition.
-- 56: -/
-- 57: @[rep_depth operator]
```

## 11. `InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeLogDensityOperator_diag`

- Score: `151.09397`
- Distance: `0`
- Module: `InfoGeometry.Canonical.RelativeSurprisalOperatorLift`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean`
- Line: `183`

```lean
-- 179:     rayLogDensityOperator (n := n) q i i =
-- 180:       InfoGeometry.Canonical.PositiveRayCore.logDensity (α := Fin n) q i := by
-- 181:   rw [rayLogDensityOperator, firstQuantize_apply_diag]
-- 182: 
-- 183: @[simp] theorem relativeLogDensityOperator_diag
-- 184:     (q q0 : InfoGeometry.Canonical.PositiveRayCore.PositiveRay (Fin n)) (i : Fin n) :
-- 185:     relativeLogDensityOperator (n := n) q q0 i i =
-- 186:       InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity (α := Fin n) q q0 i := by
-- 187:   rw [relativeLogDensityOperator, firstQuantize_apply_diag]
```

## 12. `InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeModularPotentialOperator_diag`

- Score: `151.09397`
- Distance: `0`
- Module: `InfoGeometry.Canonical.RelativeSurprisalOperatorLift`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean`
- Line: `189`

```lean
-- 185:     relativeLogDensityOperator (n := n) q q0 i i =
-- 186:       InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity (α := Fin n) q q0 i := by
-- 187:   rw [relativeLogDensityOperator, firstQuantize_apply_diag]
-- 188: 
-- 189: @[simp] theorem relativeModularPotentialOperator_diag
-- 190:     (q q0 : InfoGeometry.Canonical.PositiveRayCore.PositiveRay (Fin n)) (i : Fin n) :
-- 191:     relativeModularPotentialOperator (n := n) q q0 i i =
-- 192:       InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential (α := Fin n) q q0 i := by
-- 193:   rw [relativeModularPotentialOperator, firstQuantize_apply_diag]
```
