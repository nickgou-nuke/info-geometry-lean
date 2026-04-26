# Gravitational Lean Context

- Query: `PrimeGasJaynesConjecture prime occupation Gibbs model Euler product partition`
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

- `EQC-0114` matched `gibbs, jaynes, model, partition`; added `bernoulli, class, clifford, density, ent, exp, exponential, family, finite, flow, geometry, hessian, info, max, metric, modular, multinomial, numerator, operator, problem, quotient, real, rotor, weight`
- `EQC-0364` matched `gibbs, partition`; added `supercharacter`
- `EQC-0097` matched `gas, partition`; added `character, functional, supervolume, weyl`
- `EQC-0001` matched `euler`; added ``
- `EQC-0113` matched `model`; added `massieu, theta`
- `EQC-0367` matched `partition`; added `pfaffian, reg`
- `EQC-0366` matched `model`; added `connected, convex, odd, path`
- `EQC-0385` matched `partition`; added `function, integral`

## 1. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.partition_nonneg`

- Score: `301.792202`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `178`

Doc:

The finite exponential-family partition function is nonnegative. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_14dfe66ff11160b23924720b87d7dc1db8f00770`
- SCC: `scc_2db393570e17b63467f673a319129ce69a360d00`
- Witness backed: `True`

```lean
-- 174: /-- Partition function `Z(lam) = ∑ q(x) exp(E_lam(x))`. -/
-- 175: def partition (J : FiniteJaynesProblem α ι) (lam : ι → ℝ) : ℝ :=
-- 176:   ∑ x, (J.prior x).toReal * Real.exp (J.energy lam x)
-- 177: 
-- 178: /-- The finite exponential-family partition function is nonnegative. -/
-- 179: lemma partition_nonneg (J : FiniteJaynesProblem α ι) (lam : ι → ℝ) :
-- 180:     0 ≤ J.partition lam := by
-- 181:   unfold partition
-- 182:   refine Finset.sum_nonneg ?_
```

## 2. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.partition`

- Score: `277.519722`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `174`

Doc:

Partition function `Z(lam) = ∑ q(x) exp(E_lam(x))`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_dc3a3920fa7dfa3c82ce40d8ed86d304a0f7b940`
- SCC: `scc_76561019ffaa1fbb77bcc401df1a6e28b4d11cba`
- Witness backed: `True`

```lean
-- 170: @[simp] lemma energy_zero (J : FiniteJaynesProblem α ι) (x : α) :
-- 171:     J.energy (fun _ => 0) x = 0 := by
-- 172:   simp [energy]
-- 173: 
-- 174: /-- Partition function `Z(lam) = ∑ q(x) exp(E_lam(x))`. -/
-- 175: def partition (J : FiniteJaynesProblem α ι) (lam : ι → ℝ) : ℝ :=
-- 176:   ∑ x, (J.prior x).toReal * Real.exp (J.energy lam x)
-- 177: 
-- 178: /-- The finite exponential-family partition function is nonnegative. -/
```

## 3. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsWeight_nonneg`

- Score: `276.041667`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `221`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_ba87ed2929ee71adab9688c7865a9be1af720af2`
- SCC: `scc_a22cb13f802bf318066137ae093e19e90c707446`
- Witness backed: `True`

```lean
-- 217: /-- Unnormalized Gibbs weight `q(x) e^{E_lam(x)}`. -/
-- 218: def gibbsWeight (J : FiniteJaynesProblem α ι) (lam : ι → ℝ) (x : α) : ℝ :=
-- 219:   (J.prior x).toReal * Real.exp (J.energy lam x)
-- 220: 
-- 221: @[simp] lemma gibbsWeight_nonneg
-- 222:     (J : FiniteJaynesProblem α ι) (lam : ι → ℝ) (x : α) :
-- 223:     0 ≤ J.gibbsWeight lam x := by
-- 224:   exact mul_nonneg (J.prior x).toReal_nonneg (le_of_lt (Real.exp_pos _))
-- 225: 
```

## 4. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsWeight`

- Score: `269.953782`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `217`

Doc:

Unnormalized Gibbs weight `q(x) e^{E_lam(x)}`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_5aae1efe223adf0b013bb581323f4a154286f281`
- SCC: `scc_fe37f854fe72100249159568b9044c8716b14561`
- Witness backed: `True`

```lean
-- 213:     (hprior : J.FullSupportPrior) (lam : ι → ℝ) :
-- 214:     J.partition lam ≠ 0 :=
-- 215:   (J.partition_pos_of_fullSupport hprior lam).ne'
-- 216: 
-- 217: /-- Unnormalized Gibbs weight `q(x) e^{E_lam(x)}`. -/
-- 218: def gibbsWeight (J : FiniteJaynesProblem α ι) (lam : ι → ℝ) (x : α) : ℝ :=
-- 219:   (J.prior x).toReal * Real.exp (J.energy lam x)
-- 220: 
-- 221: @[simp] lemma gibbsWeight_nonneg
```

## 5. `InfoGeometry.MaxEnt.partition`

- Score: `268.536576`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `35`

Doc:

Jaynes partition function `Z(lam) = ∑ᵢ exp(-lam fᵢ)`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_3df55cf488400e49db4563b1b0912ac1c16d7c1b`
- SCC: `scc_f493f42e74e4b9fe820be5889d16a68f9f2030b3`
- Witness backed: `True`

```lean
-- 31:   norm : ∑ i, p i = 1
-- 32:   expectation : ∑ i, p i * f i = expectationVal
-- 33:   nonneg : ∀ i, 0 ≤ p i
-- 34: 
-- 35: /-- Jaynes partition function `Z(lam) = ∑ᵢ exp(-lam fᵢ)`. -/
-- 36: noncomputable def partition (f : Fin n → ℝ) (lam : ℝ) : ℝ :=
-- 37:   ∑ i, Real.exp (-lam * f i)
-- 38: 
-- 39: /-- Log-partition `log Z(lam)`. -/
```

## 6. `InfoGeometry.ExponentialFamily.Bernoulli.logPartition`

- Score: `267.113646`
- Distance: `None`
- Module: `InfoGeometry.ExponentialFamily.Bernoulli`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/ExponentialFamily/Bernoulli.lean`
- Line: `12`

Doc:

Bernoulli log-partition function: ψ(η) = log(1 + exp η). 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_d1a0c51f199bfe233a4b5c715bbfab566fc0cf9b`
- SCC: `scc_1dc17abb5a724c3ac01d51db06f8153f8e147529`
- Witness backed: `True`

```lean
-- 8: 
-- 9: open InfoGeometry.Convex
-- 10: open InfoGeometry.Canonical.Triality
-- 11: 
-- 12: /-- Bernoulli log-partition function: ψ(η) = log(1 + exp η). -/
-- 13: noncomputable def logPartition (η : ℝ) : ℝ :=
-- 14:   Real.log (1 + Real.exp η)
-- 15: 
-- 16: /-- The Bernoulli dual map is the expectation parameter: p = exp(η) / (1 + exp(η)). -/
```

## 7. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.partition_zero`

- Score: `265.129707`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `281`

Doc:

At zero multipliers, the finite partition function equals `1`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_9eff6c4aed65b92aa8a50b254d28a5a38b502374`
- SCC: `scc_29cc04047961ff148eac947ca0d2b77913e8ceb5`
- Witness backed: `True`

```lean
-- 277: /-- Finite free-energy potential `ψ(lam) = log Z(lam)`. -/
-- 278: noncomputable def logPartition (J : FiniteJaynesProblem α ι) (lam : ι → ℝ) : ℝ :=
-- 279:   Real.log (J.partition lam)
-- 280: 
-- 281: /-- At zero multipliers, the finite partition function equals `1`. -/
-- 282: lemma partition_zero (J : FiniteJaynesProblem α ι) :
-- 283:     J.partition (fun _ => 0) = 1 := by
-- 284:   unfold partition energy
-- 285:   simpa using sum_toReal_eq_one J.prior
```

## 8. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.partition_ne_zero_of_fullSupport`

- Score: `261.516322`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `209`

Doc:

Full prior support yields nonvanishing partition function. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_1d2ad19c4fa881244e5fbd2bf83b81b303fd004e`
- SCC: `scc_76e2183edd43dc6422b18d66aaaa0e16e9d10ffa`
- Witness backed: `True`

```lean
-- 205:       (fun y _hy => mul_nonneg (J.prior y).toReal_nonneg (le_of_lt (Real.exp_pos _)))
-- 206:       (by simp)
-- 207:   exact lt_of_lt_of_le hx0 hle
-- 208: 
-- 209: /-- Full prior support yields nonvanishing partition function. -/
-- 210: lemma partition_ne_zero_of_fullSupport
-- 211:     (J : FiniteJaynesProblem α ι)
-- 212:     [Nonempty α]
-- 213:     (hprior : J.FullSupportPrior) (lam : ι → ℝ) :
```

## 9. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsDist_pointwise`

- Score: `258.36375`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `349`

Doc:

The Gibbs posterior satisfies the exponential tilt formula pointwise. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_1dcbf829744aec88b64ac73edb03c534125e34be`
- SCC: `scc_54ffb92aa15e2ee6066398ab7922ab88031e155d`
- Witness backed: `True`

```lean
-- 345:   unfold dualObjective
-- 346:   rw [J.logPartition_zero]
-- 347:   simp
-- 348: 
-- 349: /-- The Gibbs posterior satisfies the exponential tilt formula pointwise. -/
-- 350: lemma gibbsDist_pointwise
-- 351:     (J : FiniteJaynesProblem α ι)
-- 352:     (lam : ι → ℝ) (hZ : J.partition lam ≠ 0) (x : α) :
-- 353:     ((J.gibbsDist lam hZ) x).toReal = J.gibbsProb lam hZ x := by
```

## 10. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsProb_eq_prior_mul_exp_tilt`

- Score: `258.2535`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `387`

Doc:

Pointwise exponential-tilt shape relative to the prior. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_ea139b187510c7d645d909e4aa65c73202298414`
- SCC: `scc_9eb714114867867131bbb956ea7589baff69c08b`
- Witness backed: `True`

```lean
-- 383:   · have h_hi := h i hi
-- 384:     rw [← h_eq i] at h_hi
-- 385:     exact h_hi
-- 386: 
-- 387: /-- Pointwise exponential-tilt shape relative to the prior. -/
-- 388: lemma gibbsProb_eq_prior_mul_exp_tilt
-- 389:     (J : FiniteJaynesProblem α ι)
-- 390:     (lam : ι → ℝ)
-- 391:     (hZ : J.partition lam ≠ 0)
```

## 11. `InfoGeometry.Clifford.Rotor.modularFlow`

- Score: `257.707377`
- Distance: `None`
- Module: `InfoGeometry.Clifford.GeometricRotor`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Clifford/GeometricRotor.lean`
- Line: `102`

Doc:

Modular flow is the 1-parameter family `R(s) = exp(-K s / 2)`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_aaef22be2b49e4c2886c9d2af881a751f7ed36c7`
- SCC: `scc_9339296b1c7b98ddfb8fc6778b8e5d30661c0af2`
- Witness backed: `True`

```lean
-- 98: `ψ ↦ R (R̃ ψ)`. -/
-- 99: noncomputable def evolve (R : Rotor E) (ψ : InfoGeometry.Krein.DoubledSpace E) : InfoGeometry.Krein.DoubledSpace E :=
-- 100:   R.exp (R.reverse ψ)
-- 101: 
-- 102: /-- Modular flow is the 1-parameter family `R(s) = exp(-K s / 2)`. -/
-- 103: def modularFlow (K : Bivector E) (s : ℝ) : Rotor E :=
-- 104:   { B := K, θ := s }
-- 105: 
-- 106: @[simp] theorem evolve_zero (K : Bivector E) (ψ : InfoGeometry.Krein.DoubledSpace E) :
```

## 12. `InfoGeometry.Canonical.SouriauConformalKKT.OperatorialWeylSupercharacterContext`

- Score: `256.910714`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauConformalKKTContext`
- Declaration kind: `inductive`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SouriauConformalKKTContext.lean`
- Line: `380`

Layer note: modular/transport/flow substrate

Doc:

Operatorial boson/fermion statistics context for the conformal
Gibbs-Souriau partition.

The statistical split is carried by readout functionals on the same doubled
operator carrier.  The bosonic sector contributes with positive sign, the
fermionic sector with negative sign, and the total Souriau/Weyl readout is
their difference.  No finite weight enumeration is used here.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_abce58a009f687d2fbbeadc77b6394154a2b2755`
- SCC: `scc_665387dc3b114f6ffe6887a8f3de74cacf293883`
- Witness backed: `True`

```lean
-- 376: end ConformalGibbsSouriauOperatorContext
-- 377: 
-- 378: /-! ## Operatorial boson/fermion supercharacter split -/
-- 379: 
-- 380: /--
-- 381: Operatorial boson/fermion statistics context for the conformal
-- 382: Gibbs-Souriau partition.
-- 383: 
-- 384: The statistical split is carried by readout functionals on the same doubled
```

## 13. `InfoGeometry.MaxEnt.JaynesRNMaxEnt.partitionFunction_pos`

- Score: `255.574744`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.JaynesRNMaxEnt`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/JaynesRNMaxEnt.lean`
- Line: `140`

Doc:

The Gibbs partition function is strictly positive when the exponential tilt is integrable. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_76b889600f3e42fb352a83accc6573ad8ed11a84`
- SCC: `scc_9e560e5a885511b36d0f58b1fb25878396cb36d6`
- Witness backed: `True`

```lean
-- 136:     0 ≤ partitionFunction (μ₀ := μ₀) (C := C) lam := by
-- 137:   unfold partitionFunction
-- 138:   exact integral_nonneg (fun x => by positivity)
-- 139: 
-- 140: /-- The Gibbs partition function is strictly positive when the exponential tilt is integrable. -/
-- 141: theorem partitionFunction_pos (lam : ι → ℝ)
-- 142:     (hInt : PartitionIntegrable (μ₀ := μ₀) (C := C) lam) :
-- 143:     0 < partitionFunction (μ₀ := μ₀) (C := C) lam := by
-- 144:   simpa [partitionFunction, PartitionIntegrable] using
```

## 14. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.partition_pos_of_fullSupport`

- Score: `255.420603`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `190`

Doc:

Full prior support yields strict positivity of the partition function. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_0976a080b31f0600058b86931b24dc26fa67a544`
- SCC: `scc_5523b10892bac34137b0dfd0d1d1de05c0125a67`
- Witness backed: `True`

```lean
-- 186: /-- Full support on the finite prior. -/
-- 187: def FullSupportPrior (J : FiniteJaynesProblem α ι) : Prop :=
-- 188:   ∀ x, 0 < (J.prior x).toReal
-- 189: 
-- 190: /-- Full prior support yields strict positivity of the partition function. -/
-- 191: lemma partition_pos_of_fullSupport
-- 192:     (J : FiniteJaynesProblem α ι)
-- 193:     [Nonempty α]
-- 194:     (hprior : J.FullSupportPrior) (lam : ι → ℝ) :
```

## 15. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.energy`

- Score: `255.18225`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `166`

Doc:

Exponential-family score `E_lam(x) = ∑_{i ∈ index} lam_i f_i(x)`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_102f7bb50d3d47622bac11e790893533b4308faa`
- SCC: `scc_53baaccc66201cc920feec5983b20fb3f29e1701`
- Witness backed: `True`

```lean
-- 162:   target : ι → ℝ
-- 163: 
-- 164: namespace FiniteJaynesProblem
-- 165: 
-- 166: /-- Exponential-family score `E_lam(x) = ∑_{i ∈ index} lam_i f_i(x)`. -/
-- 167: def energy (J : FiniteJaynesProblem α ι) (lam : ι → ℝ) (x : α) : ℝ :=
-- 168:   ∑ i ∈ J.index, lam i * J.feature i x
-- 169: 
-- 170: @[simp] lemma energy_zero (J : FiniteJaynesProblem α ι) (x : α) :
```

## 16. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.energy_zero`

- Score: `254.525726`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `170`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_42792c56c04fc2d9f9a0c7c221a0c3736e110f7f`
- SCC: `scc_1c9b80aa501963014631d674f7a040ad5c0dd583`
- Witness backed: `True`

```lean
-- 166: /-- Exponential-family score `E_lam(x) = ∑_{i ∈ index} lam_i f_i(x)`. -/
-- 167: def energy (J : FiniteJaynesProblem α ι) (lam : ι → ℝ) (x : α) : ℝ :=
-- 168:   ∑ i ∈ J.index, lam i * J.feature i x
-- 169: 
-- 170: @[simp] lemma energy_zero (J : FiniteJaynesProblem α ι) (x : α) :
-- 171:     J.energy (fun _ => 0) x = 0 := by
-- 172:   simp [energy]
-- 173: 
-- 174: /-- Partition function `Z(lam) = ∑ q(x) exp(E_lam(x))`. -/
```

## 17. `InfoGeometry.MaxEnt.JaynesRNMaxEnt.partitionFunction_nonneg`

- Score: `254.19298`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.JaynesRNMaxEnt`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/JaynesRNMaxEnt.lean`
- Line: `134`

Doc:

The Gibbs partition function is nonnegative. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_1273e83ab489225ce7e6a3ec0bf2ef6ada9a8bd5`
- SCC: `scc_e92208f79869d6bb85c14e64d2b4bd7dc3c0990e`
- Witness backed: `True`

```lean
-- 130:       (f := potential (C := C) lam)
-- 131:       (aemeasurable_potential (μ₀ := μ₀) (C := C) lam))
-- 132: 
-- 133: omit [IsProbabilityMeasure μ₀] in
-- 134: /-- The Gibbs partition function is nonnegative. -/
-- 135: lemma partitionFunction_nonneg (lam : ι → ℝ) :
-- 136:     0 ≤ partitionFunction (μ₀ := μ₀) (C := C) lam := by
-- 137:   unfold partitionFunction
-- 138:   exact integral_nonneg (fun x => by positivity)
```

## 18. `InfoGeometry.MaxEnt.gibbsWithPrior_eq_exp_sub_logPartition`

- Score: `253.440505`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Jaynes`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Jaynes.lean`
- Line: `180`

Doc:

Prior-weighted Gibbs form as an exponential tilt with log-partition. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_679041c288f8889c527aedf86a3dc4c25edf4eb2`
- SCC: `scc_aca234f9411cc887662032b8ccd43664d4a6182d`
- Witness backed: `True`

```lean
-- 176: noncomputable def logPartitionWithPrior
-- 177:     (q : ProbabilityDist (Fin n)) (f : Fin n → ℝ) (lam : ℝ) : ℝ :=
-- 178:   Real.log (partitionWithPrior q f lam)
-- 179: 
-- 180: /-- Prior-weighted Gibbs form as an exponential tilt with log-partition. -/
-- 181: lemma gibbsWithPrior_eq_exp_sub_logPartition
-- 182:     (q : ProbabilityDist (Fin n)) (f : Fin n → ℝ) (lam : ℝ) (i : Fin n) :
-- 183:     gibbsWithPrior q f lam i =
-- 184:       (q i).toReal * Real.exp (-lam * f i - logPartitionWithPrior q f lam) := by
```

## 19. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.target`

- Score: `251.450852`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `162`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_dc76b2f70bb4dbb122a14569eabe8a5e11782b5f`
- SCC: `scc_ff2819b62eb04d6b013d9259af22f1b4a96ddd8b`
- Witness backed: `True`

```lean
-- 158: structure FiniteJaynesProblem (α ι : Type*) [Fintype α] [DecidableEq α] [DecidableEq ι] where
-- 159:   prior : ProbabilityDist α
-- 160:   index : Finset ι
-- 161:   feature : ι → α → ℝ
-- 162:   target : ι → ℝ
-- 163: 
-- 164: namespace FiniteJaynesProblem
-- 165: 
-- 166: /-- Exponential-family score `E_lam(x) = ∑_{i ∈ index} lam_i f_i(x)`. -/
```

## 20. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsDist`

- Score: `251.095336`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `253`

Doc:

Gibbs posterior as a `ProbabilityDist`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_a29f8b24826ad30f99c5eac469613c4ee6223222`
- SCC: `scc_8c8f8d59db458f89eeb9e65c5e9117caf3532ad6`
- Witness backed: `True`

```lean
-- 249:   -- By definition, ∑ x, J.gibbsWeight lam x is exactly J.partition lam
-- 250:   change J.partition lam / J.partition lam = 1
-- 251:   exact div_self hZ
-- 252: 
-- 253: /-- Gibbs posterior as a `ProbabilityDist`. -/
-- 254: noncomputable def gibbsDist
-- 255:     (J : FiniteJaynesProblem α ι)
-- 256:     (lam : ι → ℝ) (hZ : J.partition lam ≠ 0) : ProbabilityDist α :=
-- 257:   PMF.ofFintype (fun x => ENNReal.ofReal (J.gibbsProb lam hZ x)) (by
```

## 21. `InfoGeometry.ExponentialFamily.Bernoulli.bernoulliHessianGeometry`

- Score: `249.334799`
- Distance: `None`
- Module: `InfoGeometry.ExponentialFamily.Bernoulli`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/ExponentialFamily/Bernoulli.lean`
- Line: `27`

Doc:

Bernoulli family as a 1D Hessian Geometry. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_79c2dcff782459b576e3fa20e3d949684ed126a2`
- SCC: `scc_78fd69107168f758656f73f13381aacb0e22ad51`
- Witness backed: `True`

```lean
-- 23:     apply hbase.log
-- 24:     linarith [Real.exp_pos η]
-- 25:   simpa [logPartition] using hlog.deriv
-- 26: 
-- 27: /-- Bernoulli family as a 1D Hessian Geometry. -/
-- 28: noncomputable def bernoulliHessianGeometry : HessianGeometry1D where
-- 29:   potential := logPartition
-- 30: 
-- 31: /-- The metric of the Bernoulli family is the variance: p(1-p). -/
```

## 22. `InfoGeometry.ExponentialFamily.familyDensity`

- Score: `249.010387`
- Distance: `None`
- Module: `InfoGeometry.ExponentialFamily.Finite`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/ExponentialFamily/Finite.lean`
- Line: `48`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_67c719c1c6c3165813209fa08ec7dec6372af787`
- SCC: `scc_3c96274e0511dd037204dc604ab3f7dd7e259d87`
- Witness backed: `True`

```lean
-- 44: 
-- 45: noncomputable def familyStatistic (F : FiniteExponentialFamilyData α) (x : α) (θ : ℝ) : ℝ :=
-- 46:   θ * F.stat x + Real.log ((F.base x).toReal)
-- 47: 
-- 48: noncomputable def familyDensity (F : FiniteExponentialFamilyData α) (θ : ℝ) (x : α) : ℝ :=
-- 49:   (F.base x).toReal * Real.exp (θ * F.stat x) / familyPartition F θ
-- 50: 
-- 51: section Nonempty
-- 52: 
```

## 23. `InfoGeometry.ExponentialFamily.familyPartition`

- Score: `249.010387`
- Distance: `None`
- Module: `InfoGeometry.ExponentialFamily.Finite`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/ExponentialFamily/Finite.lean`
- Line: `39`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_5c34ad336941852d80b2d5d79a1f5b81c1794b60`
- SCC: `scc_1ebdf60aaaeaec712285c8cd3d2a90c55adca71d`
- Witness backed: `True`

```lean
-- 35:   base_pos : ∀ x, 0 < (base x).toReal
-- 36: 
-- 37: variable {α : Type _} [Fintype α]
-- 38: 
-- 39: noncomputable def familyPartition (F : FiniteExponentialFamilyData α) (θ : ℝ) : ℝ :=
-- 40:   ∑ x, (F.base x).toReal * Real.exp (θ * F.stat x)
-- 41: 
-- 42: noncomputable def familyLogPartition (F : FiniteExponentialFamilyData α) (θ : ℝ) : ℝ :=
-- 43:   Real.log (familyPartition F θ)
```

## 24. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.mk`

- Score: `248.375978`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `constructor`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `158`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_9490819fa767de9c60911a285c9bc44ad6dfa513`
- SCC: `scc_d723c96d78ce022b3846f5c24374e809e3802a83`
- Witness backed: `True`

```lean
-- 154: variable [Fintype α] [DecidableEq α]
-- 155: variable [DecidableEq ι]
-- 156: 
-- 157: /-- Finite Jaynes problem data: prior + finite feature family + targets. -/
-- 158: structure FiniteJaynesProblem (α ι : Type*) [Fintype α] [DecidableEq α] [DecidableEq ι] where
-- 159:   prior : ProbabilityDist α
-- 160:   index : Finset ι
-- 161:   feature : ι → α → ℝ
-- 162:   target : ι → ℝ
```

## 25. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem`

- Score: `248.257742`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `inductive`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `157`

Doc:

Finite Jaynes problem data: prior + finite feature family + targets. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_8019dc65ff95bed4ce720efdfb853fc42b60ee56`
- SCC: `scc_e8bea7a948ab72fb1465268e3ed7fbbdeafd4f88`
- Witness backed: `True`

```lean
-- 153: variable {α ι : Type*}
-- 154: variable [Fintype α] [DecidableEq α]
-- 155: variable [DecidableEq ι]
-- 156: 
-- 157: /-- Finite Jaynes problem data: prior + finite feature family + targets. -/
-- 158: structure FiniteJaynesProblem (α ι : Type*) [Fintype α] [DecidableEq α] [DecidableEq ι] where
-- 159:   prior : ProbabilityDist α
-- 160:   index : Finset ι
-- 161:   feature : ι → α → ℝ
```
