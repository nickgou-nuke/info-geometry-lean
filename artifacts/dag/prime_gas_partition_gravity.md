# Gravitational Lean Context

- Query: `Euler product partition function countable prime occupation Gibbs`
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

- `EQC-0364` matched `gibbs, partition`; added `operator, supercharacter`
- `EQC-0385` matched `function, partition`; added `character, functional, integral`
- `EQC-0070` matched `function, partition`; added `capstone, weyl`
- `EQC-0055` matched `function, partition`; added `adapted, basis, global, shadow`
- `EQC-0114` matched `gibbs, partition`; added `bernoulli, class, clifford, density, ent, exp, exponential, family, finite, flow, geometry, hessian, info, jaynes, max, metric, model, modular, multinomial, numerator, problem, quotient, real, rotor, weight`
- `EQC-0001` matched `euler`; added ``
- `EQC-0367` matched `partition`; added `pfaffian, reg`
- `EQC-0053` matched `euler`; added `curvature, index`

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

## 2. `InfoGeometry.SuperMetriplectic.AdaptedBasisWeylCharacterCapstone.partition_eq_globalShadow`

- Score: `300.14375`
- Distance: `None`
- Module: `InfoGeometry.SuperMetriplectic.WeylCharacter`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/SuperMetriplectic/WeylCharacter.lean`
- Line: `224`

Doc:

The Weyl character partition function is the adapted scalar global shadow. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_a1793ad398d172e7c255b91566f300f2073fd186`
- SCC: `scc_9bba84e1101c492e3a9774dcc092d822a34b8152`
- Witness backed: `True`

```lean
-- 220: namespace AdaptedBasisWeylCharacterCapstone
-- 221: 
-- 222: variable {ι : Type*} [Fintype ι]
-- 223: 
-- 224: /-- The Weyl character partition function is the adapted scalar global shadow. -/
-- 225: theorem partition_eq_globalShadow
-- 226:     (C : AdaptedBasisWeylCharacterCapstone ι) :
-- 227:     C.characterPacket.partitionFunction = C.adaptedBasis.globalShadow :=
-- 228:   C.partition_matches_globalShadow
```

## 3. `InfoGeometry.SuperMetriplectic.AdaptedBasisWeylCharacterCapstone.weyl_character_adapted_basis_capstone`

- Score: `300.108066`
- Distance: `None`
- Module: `InfoGeometry.SuperMetriplectic.WeylCharacter`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/SuperMetriplectic/WeylCharacter.lean`
- Line: `248`

Doc:

Combined Weyl-character capstone:
partition equals adapted global shadow, BPS index equals supercharacter,
temperature derivative vanishes, Fisher curvature is nonnegative, and the
`Cl(4,4)` degeneracy distribution is exposed.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_47aa9393d889ec4b6e73ec8ae19874b1071e6489`
- SCC: `scc_48424c296f684189d4d193cc150e29ee3db443d1`
- Witness backed: `True`

```lean
-- 244:     (C : AdaptedBasisWeylCharacterCapstone ι) :
-- 245:     0 ≤ C.fisher.fisherCurvature :=
-- 246:   C.fisher.fisher_nonnegative
-- 247: 
-- 248: /--
-- 249: Combined Weyl-character capstone:
-- 250: partition equals adapted global shadow, BPS index equals supercharacter,
-- 251: temperature derivative vanishes, Fisher curvature is nonnegative, and the
-- 252: `Cl(4,4)` degeneracy distribution is exposed.
```

## 4. `InfoGeometry.SuperMetriplectic.AdaptedBasisWeylCharacterCapstone.partition_matches_globalShadow`

- Score: `278.028971`
- Distance: `None`
- Module: `InfoGeometry.SuperMetriplectic.WeylCharacter`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/SuperMetriplectic/WeylCharacter.lean`
- Line: `215`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_12344d9892e52183456a5929919101f1fab610d7`
- SCC: `scc_86022dc9a5e41b065e79a6219ebe7d415743d75b`
- Witness backed: `True`

```lean
-- 211:   superCharacter : SuperWeylCharacterSplit
-- 212:   witten : WittenIndexCharacterPacket
-- 213:   fisher : CharacterFisherCurvatureShadow
-- 214:   cl44Distribution : Cl44WeylCharacterDistribution
-- 215:   partition_matches_globalShadow :
-- 216:     characterPacket.partitionFunction = adaptedBasis.globalShadow
-- 217:   superCharacter_matches_witten :
-- 218:     witten.split = superCharacter
-- 219: 
```

## 5. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.partition`

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

## 6. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsWeight_nonneg`

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

## 7. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.energy`

- Score: `272.34825`
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

## 8. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsWeight`

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

## 9. `InfoGeometry.MaxEnt.partition`

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

## 10. `InfoGeometry.ExponentialFamily.Bernoulli.logPartition`

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

## 11. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.index`

- Score: `266.0625`
- Distance: `None`
- Module: `InfoGeometry.MaxEnt.Finite`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/MaxEnt/Finite.lean`
- Line: `160`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_12fe210a1c4e7c8aa2e2f690847e628bbad99384`
- SCC: `scc_90273b651d11a11d4c63154b4266d5c5cbde91ee`
- Witness backed: `True`

```lean
-- 156: 
-- 157: /-- Finite Jaynes problem data: prior + finite feature family + targets. -/
-- 158: structure FiniteJaynesProblem (α ι : Type*) [Fintype α] [DecidableEq α] [DecidableEq ι] where
-- 159:   prior : ProbabilityDist α
-- 160:   index : Finset ι
-- 161:   feature : ι → α → ℝ
-- 162:   target : ι → ℝ
-- 163: 
-- 164: namespace FiniteJaynesProblem
```

## 12. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.partition_zero`

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

## 13. `InfoGeometry.SuperMetriplectic.AdaptedBasisWeylCharacterCapstone.witten_index_eq_superCharacter`

- Score: `261.961236`
- Distance: `None`
- Module: `InfoGeometry.SuperMetriplectic.WeylCharacter`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/SuperMetriplectic/WeylCharacter.lean`
- Line: `230`

Doc:

Witten index is the supercharacter after the BPS specialization. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_c25c584817c216ec59203949e5a4f36038fba2b8`
- SCC: `scc_807afb7f5b6d092afec556c80b793d977767616e`
- Witness backed: `True`

```lean
-- 226:     (C : AdaptedBasisWeylCharacterCapstone ι) :
-- 227:     C.characterPacket.partitionFunction = C.adaptedBasis.globalShadow :=
-- 228:   C.partition_matches_globalShadow
-- 229: 
-- 230: /-- Witten index is the supercharacter after the BPS specialization. -/
-- 231: theorem witten_index_eq_superCharacter
-- 232:     (C : AdaptedBasisWeylCharacterCapstone ι) :
-- 233:     C.witten.indexValue = C.superCharacter.superCharacter := by
-- 234:   rw [C.witten.index_eq_superCharacter, C.superCharacter_matches_witten]
```

## 14. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.partition_ne_zero_of_fullSupport`

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

## 15. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsDist_pointwise`

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

## 16. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsProb_eq_prior_mul_exp_tilt`

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

## 17. `InfoGeometry.Clifford.Rotor.modularFlow`

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

## 18. `InfoGeometry.Canonical.SouriauConformalKKT.OperatorialWeylSupercharacterContext`

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

## 19. `InfoGeometry.SuperMetriplectic.AdaptedBasisWeylCharacterCapstone.superCharacter_matches_witten`

- Score: `256.219753`
- Distance: `None`
- Module: `InfoGeometry.SuperMetriplectic.WeylCharacter`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/SuperMetriplectic/WeylCharacter.lean`
- Line: `217`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_b9cefb58b4276369a1a95253fd83556a6efa6e2a`
- SCC: `scc_c10de87309b7968462e56ac159b1d1143a59e296`
- Witness backed: `True`

```lean
-- 213:   fisher : CharacterFisherCurvatureShadow
-- 214:   cl44Distribution : Cl44WeylCharacterDistribution
-- 215:   partition_matches_globalShadow :
-- 216:     characterPacket.partitionFunction = adaptedBasis.globalShadow
-- 217:   superCharacter_matches_witten :
-- 218:     witten.split = superCharacter
-- 219: 
-- 220: namespace AdaptedBasisWeylCharacterCapstone
-- 221: 
```

## 20. `InfoGeometry.MaxEnt.JaynesRNMaxEnt.partitionFunction_pos`

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

## 21. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.partition_pos_of_fullSupport`

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

## 22. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.energy_zero`

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

## 23. `InfoGeometry.SuperMetriplectic.AdaptedBasisWeylCharacterCapstone.superCharacter`

- Score: `253.106159`
- Distance: `None`
- Module: `InfoGeometry.SuperMetriplectic.WeylCharacter`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/SuperMetriplectic/WeylCharacter.lean`
- Line: `211`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_70cbef6f8350086829ff715870b8042297686b57`
- SCC: `scc_0805ce766dd74d04c9873023616c81621eb02f6c`
- Witness backed: `True`

```lean
-- 207: -/
-- 208: structure AdaptedBasisWeylCharacterCapstone (ι : Type*) [Fintype ι] where
-- 209:   adaptedBasis : InvolutionAdaptedSuperMetriplecticBasis
-- 210:   characterPacket : WeylCharacterGibbsPacket ι
-- 211:   superCharacter : SuperWeylCharacterSplit
-- 212:   witten : WittenIndexCharacterPacket
-- 213:   fisher : CharacterFisherCurvatureShadow
-- 214:   cl44Distribution : Cl44WeylCharacterDistribution
-- 215:   partition_matches_globalShadow :
```

## 24. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.GibbsSouriauGramAnalyticWitness`

- Score: `251.971584`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `inductive`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `813`

Layer note: modular/transport/flow substrate

Doc:

Analytic Gibbs-Souriau witness for the infinite/coordinateless lane.

This is not a finite state shadow and it does not hide differentiation under an
integral behind prose.  A concrete model must supply the actual integration
functional, Gibbs weight, centered moment features, first/second derivative
laws, and covariance identity.  Once those analytic obligations are supplied,
the theorem below composes them with the already-owned Legendre/Gram/square
dissipation route.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_77b1cd2abb75e8b06b36cd8e390ac1eb4f393cdf`
- SCC: `scc_b08bca0c6f3ba3e9f1c91efc29ccd3a4fed5d06c`
- Witness backed: `True`

```lean
-- 809: 
-- 810: variable {Feature : Type*}
-- 811: variable [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature]
-- 812: 
-- 813: /--
-- 814: Analytic Gibbs-Souriau witness for the infinite/coordinateless lane.
-- 815: 
-- 816: This is not a finite state shadow and it does not hide differentiation under an
-- 817: integral behind prose.  A concrete model must supply the actual integration
```

## 25. `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.target`

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
