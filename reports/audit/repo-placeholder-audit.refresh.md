# Lean Placeholder Trust Audit

Generated: `2026-05-14T19:33:13.040122+00:00`

- Modules scanned: **1529**
- Modules with findings: **586**
- Total findings: **1764** (hard=0, soft=1762, advisory=2)

## `InfoGeometry.Algebraic.ChiralOperatorAlgebra`
- path: `lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L103: **SOFT** `skeletal-proof` in `theorem canonical_modularHamiltonian`
  - proof appears to be tactic-automation-only or skeletal
  - `101: `

## `InfoGeometry.Algebraic.CliffordSymmetryLift`
- path: `lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L52: **SOFT** `skeletal-proof` in `theorem splitCliffordLift_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `50: `

## `InfoGeometry.Algebraic.NarainOrthogonalCore`
- path: `lean/InfoGeometry/Algebraic/NarainOrthogonalCore.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L66: **SOFT** `skeletal-proof` in `theorem chargeSwapLinearEquiv_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `64: `
- L102: **SOFT** `skeletal-proof` in `theorem chargeParityTwistLinearEquiv_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `100: `

## `InfoGeometry.Algebraic.OperatorSurgery`
- path: `lean/InfoGeometry/Algebraic/OperatorSurgery.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L44: **SOFT** `skeletal-proof` in `theorem null_idempotent`
  - proof appears to be tactic-automation-only or skeletal
  - `42: theorem core_idempotent : S.coreProjector * S.coreProjector = S.coreProjector :=`
- L48: **SOFT** `skeletal-proof` in `theorem core_null_orthogonal`
  - proof appears to be tactic-automation-only or skeletal
  - `46: theorem null_idempotent : S.nullProjector * S.nullProjector = S.nullProjector := by`

## `InfoGeometry.Algebraic.RealModularReadout`
- path: `lean/InfoGeometry/Algebraic/RealModularReadout.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L123: **SOFT** `skeletal-proof` in `theorem normSq_conj`
  - proof appears to be tactic-automation-only or skeletal
  - `121: `
- L357: **SOFT** `skeletal-proof` in `theorem pullbackReadout_T_eq_one`
  - proof appears to be tactic-automation-only or skeletal
  - `355:     RealUpperHalfPlane → R :=`

## `InfoGeometry.Algebraic.SplitQuadraticForm`
- path: `lean/InfoGeometry/Algebraic/SplitQuadraticForm.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L51: **SOFT** `skeletal-proof` in `theorem splitWeight_inr`
  - proof appears to be tactic-automation-only or skeletal
  - `49: `
- L65: **SOFT** `skeletal-proof` in `theorem splitQuadraticForm_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `63: `
- L99: **SOFT** `skeletal-proof` in `theorem splitQuadraticForm_negBasisVector`
  - proof appears to be tactic-automation-only or skeletal
  - `97: `

## `InfoGeometry.Algebraic.SplitSuperGeometry`
- path: `lean/InfoGeometry/Algebraic/SplitSuperGeometry.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L95: **SOFT** `skeletal-proof` in `theorem supertrace_zero`
  - proof appears to be tactic-automation-only or skeletal
  - `93: `
- L165: **SOFT** `skeletal-proof` in `theorem splitCliffordParityInvolution_vector`
  - proof appears to be tactic-automation-only or skeletal
  - `163: `
- L346: **SOFT** `skeletal-proof` in `theorem parityOp_comp_self`
  - proof appears to be tactic-automation-only or skeletal
  - `344: `

## `InfoGeometry.Application.STUOperatorBridge`
- path: `lean/InfoGeometry/Application/STUOperatorBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L62: **SOFT** `skeletal-proof` in `theorem drazinCore_add_nil`
  - proof appears to be tactic-automation-only or skeletal
  - `60: section`

## `InfoGeometry.Arithmetic.ArithmeticKMS`
- path: `lean/InfoGeometry/Arithmetic/ArithmeticKMS.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L137: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `135: `
- L195: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `193: `
- L250: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `248: `

## `InfoGeometry.Arithmetic.LPrimitive`
- path: `lean/InfoGeometry/Arithmetic/LPrimitive.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L84: **SOFT** `skeletal-proof` in `theorem mem_LMultiplesOfSet_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `82:     LPrimitiveFinset A :=`

## `InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge`
- path: `lean/InfoGeometry/Arithmetic/PrimitiveBinarySuperZetaBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L46: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `44: `

## `InfoGeometry.Arithmetic.PrimitivePrimeProjectiveTemperature`
- path: `lean/InfoGeometry/Arithmetic/PrimitivePrimeProjectiveTemperature.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L47: **SOFT** `skeletal-proof` in `theorem arithmeticPrimeRestrictedPartition_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `45: def arithmeticPrimeInvertedPartitionDensity (A : Finset ℕ) (u : ℝ) : ℝ :=`
- L54: **SOFT** `skeletal-proof` in `theorem arithmeticPrimeInvertedPartitionDensity_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `52:       arithmeticPrimePartition A β :=`

## `InfoGeometry.Arithmetic.PrimitiveSetsAbove`
- path: `lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean`
- findings: 30 (hard=0, soft=30, advisory=0)

- L257: **SOFT** `skeletal-proof` in `theorem PrimitiveFinset_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `255:   intro n hn`
- L263: **SOFT** `skeletal-proof` in `theorem SupportedAboveFinset_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `261:     PrimitiveFinset A ↔ PrimitiveSet (A : Set ℕ) := by`
- L270: **SOFT** `skeletal-proof` in `theorem primitiveWeight_eq_zero_of_not_lt_two`
  - proof appears to be tactic-automation-only or skeletal
  - `268:     SupportedAboveFinset x A ↔ SupportedAbove x (A : Set ℕ) := by`
- L299: **SOFT** `skeletal-proof` in `theorem realVonMangoldt_eq_if_isPrimePow`
  - proof appears to be tactic-automation-only or skeletal
  - `297:     positivity`
- L303: **SOFT** `skeletal-proof` in `theorem realVonMangoldt_one`
  - proof appears to be tactic-automation-only or skeletal
  - `301:     realVonMangoldt n = if IsPrimePow n then Real.log (Nat.minFac n) else 0 := by`
- L312: **SOFT** `skeletal-proof` in `theorem realVonMangoldt_eq_zero_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `310:   rw [realVonMangoldt]`
- L316: **SOFT** `skeletal-proof` in `theorem realVonMangoldt_ne_zero_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `314:     realVonMangoldt n = 0 ↔ ¬ IsPrimePow n := by`
- L320: **SOFT** `skeletal-proof` in `theorem realVonMangoldt_pos_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `318:     realVonMangoldt n ≠ 0 ↔ IsPrimePow n := by`
- L324: **SOFT** `skeletal-proof` in `theorem realVonMangoldt_apply_pow`
  - proof appears to be tactic-automation-only or skeletal
  - `322:     0 < realVonMangoldt n ↔ IsPrimePow n := by`
- L328: **SOFT** `skeletal-proof` in `theorem realVonMangoldt_apply_prime`
  - proof appears to be tactic-automation-only or skeletal
  - `326:     realVonMangoldt (n ^ k) = realVonMangoldt n := by`
- L332: **SOFT** `skeletal-proof` in `theorem sum_realVonMangoldt_divisors`
  - proof appears to be tactic-automation-only or skeletal
  - `330:     realVonMangoldt p = Real.log p := by`
- L354: **SOFT** `skeletal-proof` in `theorem primitiveModularKernel_eq_mellinKernel_shift`
  - proof appears to be tactic-automation-only or skeletal
  - `352:   rw [log_primitiveInverseBase h]`
- L502: **SOFT** `skeletal-proof` in `theorem primitiveWeight_mul_eq_of_right_one`
  - proof appears to be tactic-automation-only or skeletal
  - `500:     exact primitiveWeight_nonneg n`
- L627: **SOFT** `skeletal-proof` in `theorem primitiveWeightSum_empty`
  - proof appears to be tactic-automation-only or skeletal
  - `625:   intro n hn`
- L631: **SOFT** `skeletal-proof` in `theorem primitiveWeightSum_singleton`
  - proof appears to be tactic-automation-only or skeletal
  - `629:     primitiveWeightSum ∅ = 0 := by`
- L635: **SOFT** `skeletal-proof` in `theorem arithmeticCountWeight_eq_mul_kernel`
  - proof appears to be tactic-automation-only or skeletal
  - `633:     primitiveWeightSum ({n} : Finset ℕ) = primitiveWeight n := by`
- L639: **SOFT** `skeletal-proof` in `theorem arithmeticPartition_eq_sum`
  - proof appears to be tactic-automation-only or skeletal
  - `637:     arithmeticCountWeight counts s n = counts n * primitiveMellinKernel n s := by`
- L643: **SOFT** `skeletal-proof` in `theorem arithmeticTotalMass_eq_sum`
  - proof appears to be tactic-automation-only or skeletal
  - `641:     arithmeticPartition A counts s = Finset.sum A (fun n => counts n * primitiveMellinKernel n s) := by`
- L647: **SOFT** `skeletal-proof` in `theorem arithmeticBaseShape_eq_div`
  - proof appears to be tactic-automation-only or skeletal
  - `645:     arithmeticTotalMass A counts = Finset.sum A counts := by`
- L848: **SOFT** `skeletal-proof` in `theorem arithmeticShapeMellin_eq_sum`
  - proof appears to be tactic-automation-only or skeletal
  - `846: `
- L853: **SOFT** `skeletal-proof` in `theorem arithmeticPartition_empty`
  - proof appears to be tactic-automation-only or skeletal
  - `851:       = Finset.sum A (fun n => arithmeticBaseShape A counts n * primitiveMellinKernel n s) := by`
- L857: **SOFT** `skeletal-proof` in `theorem arithmeticTotalMass_empty`
  - proof appears to be tactic-automation-only or skeletal
  - `855:     arithmeticPartition ∅ counts s = 0 := by`
- L861: **SOFT** `skeletal-proof` in `theorem arithmeticShapeMellin_empty`
  - proof appears to be tactic-automation-only or skeletal
  - `859:     arithmeticTotalMass ∅ counts = 0 := by`
- L865: **SOFT** `skeletal-proof` in `theorem arithmeticPrimePartition_eq_sum`
  - proof appears to be tactic-automation-only or skeletal
  - `863:     arithmeticShapeMellin ∅ counts s = 0 := by`
- L870: **SOFT** `skeletal-proof` in `theorem arithmeticPrimePartition_empty`
  - proof appears to be tactic-automation-only or skeletal
  - `868:       = Finset.sum A (fun n => realVonMangoldt n * primitiveMellinKernel n s) := by`
- L1002: **SOFT** `skeletal-proof` in `theorem primitiveFinset_empty`
  - proof appears to be tactic-automation-only or skeletal
  - `1000:   intro a ha`
- L1209: **SOFT** `skeletal-proof` in `theorem primitiveDivisorFiber_eq_filter`
  - proof appears to be tactic-automation-only or skeletal
  - `1207:     refine ⟨d, Finset.mem_filter.mpr ⟨hdA, dvd_rfl⟩, ?_⟩`
- L1213: **SOFT** `skeletal-proof` in `theorem primitiveDivisorQuotient_eq_image_fiber`
  - proof appears to be tactic-automation-only or skeletal
  - `1211:     primitiveDivisorFiber A d = A.filter (fun a => d ∣ a) := by`
- L818: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `816: `
- L2217: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `2215: `

## `InfoGeometry.Arithmetic.PrimitiveSouriauPipeline`
- path: `lean/InfoGeometry/Arithmetic/PrimitiveSouriauPipeline.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L95: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `93: `

## `InfoGeometry.Arithmetic.PrimitiveSouriauZeta`
- path: `lean/InfoGeometry/Arithmetic/PrimitiveSouriauZeta.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L60: **SOFT** `skeletal-proof` in `theorem primitiveFiniteZetaPartition_eq_arithmeticPartition_unit`
  - proof appears to be tactic-automation-only or skeletal
  - `58:     primitiveFiniteZetaPartition ({n} : Finset ℕ) β = primitiveMellinKernel n β := by`
- L258: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `256: `

## `InfoGeometry.Arithmetic.ProjectiveEntropy`
- path: `lean/InfoGeometry/Arithmetic/ProjectiveEntropy.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L60: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `58: `
- L118: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `116: `

## `InfoGeometry.Arithmetic.ProjectivePrimePartition`
- path: `lean/InfoGeometry/Arithmetic/ProjectivePrimePartition.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L33: **SOFT** `skeletal-proof` in `theorem projectivePrimePartition_eq_restricted`
  - proof appears to be tactic-automation-only or skeletal
  - `31: def projectivePrimePartition (A : Finset ℕ) (u : ℝ) : ℝ :=`
- L79: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `77: `

## `InfoGeometry.Arithmetic.ProjectiveRelativeEntropy`
- path: `lean/InfoGeometry/Arithmetic/ProjectiveRelativeEntropy.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L54: **SOFT** `skeletal-proof` in `theorem primitiveToPrimeProjectiveKL_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `52:     (arithmeticPrimeInvertedPartitionDensity reference u)`
- L64: **SOFT** `skeletal-proof` in `theorem primeToPrimitiveProjectiveKL_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `62:             arithmeticPrimeInvertedPartitionDensity reference u) :=`
- L120: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `118: `
- L184: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `182: `
- L245: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `243: `

## `InfoGeometry.Arithmetic.ProjectiveWeylGauge`
- path: `lean/InfoGeometry/Arithmetic/ProjectiveWeylGauge.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L38: **SOFT** `skeletal-proof` in `theorem projectiveWeylThermalMass_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `36:     (counts : CountProfile) (support : Finset ℕ) (u : ℝ) : CountProfile :=`
- L45: **SOFT** `skeletal-proof` in `theorem projectiveArithmeticShape_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `43:       finiteArithmeticPartition counts support (betaInvert u) := by`
- L80: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `78: `
- L118: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `116: `
- L233: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `231: `
- L314: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `312: `

## `InfoGeometry.Arithmetic.WeylArithmeticDivergence`
- path: `lean/InfoGeometry/Arithmetic/WeylArithmeticDivergence.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L35: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `33: `
- L72: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `70: `
- L104: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `102: `
- L132: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `130: `
- L248: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `246: `

## `InfoGeometry.Arithmetic.ZetaTraceSpecialization`
- path: `lean/InfoGeometry/Arithmetic/ZetaTraceSpecialization.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L104: **SOFT** `skeletal-proof` in `theorem finitePrimeGasPartition_eq_denominator_inv`
  - proof appears to be tactic-automation-only or skeletal
  - `102: `

## `InfoGeometry.Arithmetic.ZetaTraceVielbeinSpecialization`
- path: `lean/InfoGeometry/Arithmetic/ZetaTraceVielbeinSpecialization.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L65: **SOFT** `skeletal-proof` in `theorem primeLocalEffectiveAction_def`
  - proof appears to be tactic-automation-only or skeletal
  - `63: `
- L136: **SOFT** `skeletal-proof` in `theorem canonicalPrimeVielbein_eulerSupervolume`
  - proof appears to be tactic-automation-only or skeletal
  - `134: `
- L140: **SOFT** `skeletal-proof` in `theorem canonicalPrimeVielbein_traceLogSupervolume_eq_riemannZeta`
  - proof appears to be tactic-automation-only or skeletal
  - `138:     canonicalPrimeVielbein.eulerSupervolume s = zetaTraceEulerSupervolume s :=`
- L146: **SOFT** `skeletal-proof` in `theorem canonicalPrimeVielbein_eulerSupervolume_eq_riemannZeta`
  - proof appears to be tactic-automation-only or skeletal
  - `144:     canonicalPrimeVielbein.traceLogSupervolume s = riemannZeta s := by`

## `InfoGeometry.Automorphic.AutomorphicKreinBridge`
- path: `lean/InfoGeometry/Automorphic/AutomorphicKreinBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L49: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `47: `

## `InfoGeometry.Automorphic.HeckePurification`
- path: `lean/InfoGeometry/Automorphic/HeckePurification.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L131: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `129:     {charge_eval : Charge → ℂ}`

## `InfoGeometry.Automorphic.LFunctionResonance`
- path: `lean/InfoGeometry/Automorphic/LFunctionResonance.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L64: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `62: `
- L202: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `200: `
- L312: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `310: `

## `InfoGeometry.Automorphic.LanglandsPrimeResonance`
- path: `lean/InfoGeometry/Automorphic/LanglandsPrimeResonance.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L83: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `81:     {Scalar : Type uScalar}`
- L132: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `130:     {Scalar : Type uScalar}`

## `InfoGeometry.Automorphic.LanglandsSugawaraBridge`
- path: `lean/InfoGeometry/Automorphic/LanglandsSugawaraBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L89: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `87:     [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]`

## `InfoGeometry.Automorphic.ProjectedLFunction`
- path: `lean/InfoGeometry/Automorphic/ProjectedLFunction.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L219: **SOFT** `skeletal-proof` in `theorem mem_automorphicResonanceSet_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `217: `
- L86: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `84: variable [AddCommGroup Bulk] [Module ℝ Bulk]`
- L87: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `85: variable [AddCommGroup Boundary] [Module ℝ Boundary]`
- L359: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `357: `
- L398: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `396: `
- L443: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `441:     {W : SiegelEisensteinWitness Bulk Boundary}`

## `InfoGeometry.Automorphic.RoelckeSelbergSpectral`
- path: `lean/InfoGeometry/Automorphic/RoelckeSelbergSpectral.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L377: **SOFT** `skeletal-proof` in `theorem potential_eq_zero_of_abs_eq_one`
  - proof appears to be tactic-automation-only or skeletal
  - `375: `
- L203: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `201: variable {W : SiegelEisensteinWitness Bulk Boundary}`
- L364: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `362: `

## `InfoGeometry.Automorphic.SiegelArithmeticResonanceOperator`
- path: `lean/InfoGeometry/Automorphic/SiegelArithmeticResonanceOperator.lean`
- findings: 10 (hard=0, soft=10, advisory=0)

- L283: **SOFT** `skeletal-proof` in `theorem cubicNorm_boundaryLift_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `281:     (t : ℝ) : ℝ :=`
- L68: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `66: variable [AddCommGroup Bulk] [Module ℝ Bulk]`
- L170: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `168: variable [AddCommGroup Readout] [Module ℝ Readout]`
- L227: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `225: variable {L : FormalPrimeRootLattice}`
- L276: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `274: `
- L342: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `340: `
- L383: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `381: variable [AddCommGroup Boundary] [Module ℝ Boundary]`
- L434: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `432: `
- L478: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `476: `
- L535: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `533:     [AddCommGroup Bulk] [Module ℝ Bulk]`

## `InfoGeometry.Automorphic.SiegelResonance`
- path: `lean/InfoGeometry/Automorphic/SiegelResonance.lean`
- findings: 7 (hard=0, soft=7, advisory=0)

- L117: **SOFT** `skeletal-proof` in `theorem cuspidalProjector_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `115: `
- L202: **SOFT** `skeletal-proof` in `theorem siegel_cuspidalProjector_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `200:   intro F`
- L345: **SOFT** `skeletal-proof` in `theorem boundaryProjector_eisenstein`
  - proof appears to be tactic-automation-only or skeletal
  - `343:   · intro h`
- L352: **SOFT** `skeletal-proof` in `theorem cuspidalProjector_eisenstein`
  - proof appears to be tactic-automation-only or skeletal
  - `350:     W.boundaryProjector (W.eisenstein b) = W.eisenstein b := by`
- L359: **SOFT** `skeletal-proof` in `theorem bulk_decomposition`
  - proof appears to be tactic-automation-only or skeletal
  - `357:     W.cuspidalProjector (W.eisenstein b) = 0 := by`
- L434: **SOFT** `skeletal-proof` in `theorem mem_globalCuspidalSubspace_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `432:     Submodule ℝ Bulk :=`
- L60: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `58: variable [AddCommGroup Bulk] [Module ℝ Bulk]`

## `InfoGeometry.Automorphic.SiegelWeilKudlaRallisBridge`
- path: `lean/InfoGeometry/Automorphic/SiegelWeilKudlaRallisBridge.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L93: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `91: `
- L169: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `167: `
- L226: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `224: `
- L263: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `261: `
- L305: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `303: `
- L365: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `363:     {P : ProjectedAutomorphicLFunctionWitness W}`

## `InfoGeometry.Automorphic.ZetaPotentialSign`
- path: `lean/InfoGeometry/Automorphic/ZetaPotentialSign.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L48: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `46: `
- L111: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `109: `

## `InfoGeometry.Canonical.AQFTOperatorSignatures`
- path: `lean/InfoGeometry/Canonical/AQFTOperatorSignatures.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L15: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `13: `

## `InfoGeometry.Canonical.Algebra`
- path: `lean/InfoGeometry/Canonical/Algebra.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L64: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `62: `

## `InfoGeometry.Canonical.AlgebraicStateFunctionalBridge`
- path: `lean/InfoGeometry/Canonical/AlgebraicStateFunctionalBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L49: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `47: `
- L118: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `116: `

## `InfoGeometry.Canonical.AnalyticalIndexCapstone`
- path: `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L23: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `21: `
- L66: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `64: `
- L130: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `128: `

## `InfoGeometry.Canonical.AnalyticalIndexCoupled`
- path: `lean/InfoGeometry/Canonical/AnalyticalIndexCoupled.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L24: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `22: `

## `InfoGeometry.Canonical.AnomalyDilationBridge`
- path: `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L28: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `26: `

## `InfoGeometry.Canonical.AnomalyOwnerMap`
- path: `lean/InfoGeometry/Canonical/AnomalyOwnerMap.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L36: **SOFT** `skeletal-proof` in `theorem drazin_dilation_anomaly_corridor`
  - proof appears to be tactic-automation-only or skeletal
  - `34: variable {E : Type}`

## `InfoGeometry.Canonical.ArakiConnesHaagerupBridge`
- path: `lean/InfoGeometry/Canonical/ArakiConnesHaagerupBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L72: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `70: `
- L153: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `151: `

## `InfoGeometry.Canonical.Arithmetic.ZetaEulerProductBridge`
- path: `lean/InfoGeometry/Canonical/Arithmetic/ZetaEulerProductBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L34: **SOFT** `skeletal-proof` in `theorem finiteEulerProduct_empty`
  - proof appears to be tactic-automation-only or skeletal
  - `32: `
- L66: **SOFT** `skeletal-proof` in `theorem zeta_euler_product_bridge`
  - proof appears to be tactic-automation-only or skeletal
  - `64:   eulerProduct_eq_prime_tprod :`

## `InfoGeometry.Canonical.BKMDriftMetric`
- path: `lean/InfoGeometry/Canonical/BKMDriftMetric.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L86: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `84: `
- L165: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `163: variable {Weight Tangent State : Type*}`
- L230: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `228: `

## `InfoGeometry.Canonical.BekensteinBound`
- path: `lean/InfoGeometry/Canonical/BekensteinBound.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L21: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `19: `
- L51: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `49: `
- L869: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `867: `

## `InfoGeometry.Canonical.BeliefAlgebra`
- path: `lean/InfoGeometry/Canonical/BeliefAlgebra.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L18: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `16: `

## `InfoGeometry.Canonical.BerryDrazin`
- path: `lean/InfoGeometry/Canonical/BerryDrazin.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L59: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `57: `
- L60: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `58: variable {Op : Type*} [Ring Op]`
- L134: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `132: `
- L169: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `167: `

## `InfoGeometry.Canonical.BerryPhase`
- path: `lean/InfoGeometry/Canonical/BerryPhase.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L63: **SOFT** `skeletal-proof` in `theorem informationBerryPhase_eq_loopLength_mul_chiralAnomalyIndex`
  - proof appears to be tactic-automation-only or skeletal
  - `61: noncomputable def informationBerryPhase (L : BayesianLoop E) (CST : ChiralSpectralTriple E) : ℝ :=`
- L69: **SOFT** `skeletal-proof` in `theorem informationBerryPhase_eq_loopLength_mul_epsilon_mul_rank`
  - proof appears to be tactic-automation-only or skeletal
  - `67:     informationBerryPhase L CST = (L.N : ℝ) * chiralAnomalyIndex CST := by`

## `InfoGeometry.Canonical.BogoliubovCartanEigenOperator`
- path: `lean/InfoGeometry/Canonical/BogoliubovCartanEigenOperator.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L516: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `514: `
- L563: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `561: `

## `InfoGeometry.Canonical.BogoliubovCartanFrameInterpretation`
- path: `lean/InfoGeometry/Canonical/BogoliubovCartanFrameInterpretation.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L37: **SOFT** `skeletal-proof` in `theorem bogoliubovFrameAction_eq_conjugate`
  - proof appears to be tactic-automation-only or skeletal
  - `35: variable {E : Type*}`
- L204: **SOFT** `skeletal-proof` in `theorem primitive_operator_owner`
  - proof appears to be tactic-automation-only or skeletal
  - `202: `
- L119: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `117: `
- L202: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `200: `

## `InfoGeometry.Canonical.BogoliubovHomologyFrameEquiv`
- path: `lean/InfoGeometry/Canonical/BogoliubovHomologyFrameEquiv.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L89: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `87: `

## `InfoGeometry.Canonical.BogoliubovWeightedKMSCertification`
- path: `lean/InfoGeometry/Canonical/BogoliubovWeightedKMSCertification.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L169: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `167: `

## `InfoGeometry.Canonical.BottStabilizedFrameEquiv`
- path: `lean/InfoGeometry/Canonical/BottStabilizedFrameEquiv.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L97: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `95: `
- L280: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `278: `

## `InfoGeometry.Canonical.BoundedKMSConditionBridge`
- path: `lean/InfoGeometry/Canonical/BoundedKMSConditionBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L79: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `77: `

## `InfoGeometry.Canonical.BoundedKMSErgodicFixedPointBridge`
- path: `lean/InfoGeometry/Canonical/BoundedKMSErgodicFixedPointBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L105: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `103: `

## `InfoGeometry.Canonical.BoundedModularFlowCalibration`
- path: `lean/InfoGeometry/Canonical/BoundedModularFlowCalibration.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L102: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `100: `

## `InfoGeometry.Canonical.BoundedModularKMSBridge`
- path: `lean/InfoGeometry/Canonical/BoundedModularKMSBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L84: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `82: `

## `InfoGeometry.Canonical.BulkBoundaryTomitaTransportBridge`
- path: `lean/InfoGeometry/Canonical/BulkBoundaryTomitaTransportBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L71: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `69: `

## `InfoGeometry.Canonical.CalabiYauMetricRicci`
- path: `lean/InfoGeometry/Canonical/CalabiYauMetricRicci.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L92: **SOFT** `skeletal-proof` in `lemma isRicciFlat_of_isEinsteinKaehlerAtWith_zero`
  - proof appears to be tactic-automation-only or skeletal
  - `90: `

## `InfoGeometry.Canonical.CalabiYauSingularBridge`
- path: `lean/InfoGeometry/Canonical/CalabiYauSingularBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L49: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `47: `

## `InfoGeometry.Canonical.CantorCliffordFiniteRepresentation`
- path: `lean/InfoGeometry/Canonical/CantorCliffordFiniteRepresentation.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L86: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `84: `
- L363: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `361: `

## `InfoGeometry.Canonical.CantorCliffordFunctionModel`
- path: `lean/InfoGeometry/Canonical/CantorCliffordFunctionModel.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L35: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `33: `
- L196: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `194: `

## `InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge`
- path: `lean/InfoGeometry/Canonical/CantorTiltSwitchCliffordBridge.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L82: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `80: `
- L136: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `134: `
- L178: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `176: `
- L293: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `291: `

## `InfoGeometry.Canonical.CartanDecomposition`
- path: `lean/InfoGeometry/Canonical/CartanDecomposition.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L34: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `32: `
- L356: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `354: variable [NormedAlgebra ℚ S] [NormedAlgebra ℝ S] [CompleteSpace S]`

## `InfoGeometry.Canonical.CartanInfinitesimalExponentialBridge`
- path: `lean/InfoGeometry/Canonical/CartanInfinitesimalExponentialBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L119: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `117: `
- L188: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `186: `

## `InfoGeometry.Canonical.CauchyResidueReadback`
- path: `lean/InfoGeometry/Canonical/CauchyResidueReadback.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L34: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `32: variable {Chain Cochain : Type*}`
- L36: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `34: `

## `InfoGeometry.Canonical.CertifiedInverseKernel`
- path: `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L108: **SOFT** `skeletal-proof` in `theorem chiralScale_eq_zero_iff_chiralAnomaly_eq_zero`
  - proof appears to be tactic-automation-only or skeletal
  - `106:     (InfoGeometry.Canonical.MoorePenrose.projectorMismatch_eq_zero_iff`
- L113: **SOFT** `skeletal-proof` in `theorem rightChiralAnomaly_eq_chiralAnomaly_of_projectorAgreement`
  - proof appears to be tactic-automation-only or skeletal
  - `111:     IK.chiralScale = 0 ↔ IK.chiralAnomaly = 0 := by`
- L56: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `54: `
- L153: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `151: `

## `InfoGeometry.Canonical.CertifiedModularReduction`
- path: `lean/InfoGeometry/Canonical/CertifiedModularReduction.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L114: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `112: `

## `InfoGeometry.Canonical.ChiralAnomaly`
- path: `lean/InfoGeometry/Canonical/ChiralAnomaly.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L130: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `128: `

## `InfoGeometry.Canonical.ChiralDiracHomologyBridge`
- path: `lean/InfoGeometry/Canonical/ChiralDiracHomologyBridge.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L55: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `53: variable {Cplus Cminus : Type*}`
- L139: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `137: variable {Cplus Cminus : Type*}`
- L205: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `203: variable {Cplus Cminus : Type*}`

## `InfoGeometry.Canonical.ChiralDiracHomologyCalibration`
- path: `lean/InfoGeometry/Canonical/ChiralDiracHomologyCalibration.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L52: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `50: `

## `InfoGeometry.Canonical.ChiralGravity`
- path: `lean/InfoGeometry/Canonical/ChiralGravity.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L102: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `100: `

## `InfoGeometry.Canonical.ChiralNullSpaceBridge`
- path: `lean/InfoGeometry/Canonical/ChiralNullSpaceBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L48: **SOFT** `skeletal-proof` in `theorem excitedStateSector_eq_orthogonal`
  - proof appears to be tactic-automation-only or skeletal
  - `46: `
- L51: **SOFT** `skeletal-proof` in `theorem regulatedHeatKernel_eq_subtract_one`
  - proof appears to be tactic-automation-only or skeletal
  - `49: theorem excitedStateSector_eq_orthogonal (Q : EndH) :`

## `InfoGeometry.Canonical.ChiralRadiationCones`
- path: `lean/InfoGeometry/Canonical/ChiralRadiationCones.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L43: **SOFT** `skeletal-proof` in `theorem constructive_mass_eq_flipRate`
  - proof appears to be tactic-automation-only or skeletal
  - `41:   massParameter := M.flipRate`

## `InfoGeometry.Canonical.CliffordBridge`
- path: `lean/InfoGeometry/Canonical/CliffordBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L7: **SOFT** `skeletal-proof` in `theorem q_agrees_with_Gauge_quad`
  - proof appears to be tactic-automation-only or skeletal
  - `5: `

## `InfoGeometry.Canonical.ClosureDrazinBridge`
- path: `lean/InfoGeometry/Canonical/ClosureDrazinBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L34: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `32: `

## `InfoGeometry.Canonical.CoarseGraining`
- path: `lean/InfoGeometry/Canonical/CoarseGraining.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L33: **SOFT** `skeletal-proof` in `theorem totalWeight_eq_sum_fiberWeight`
  - proof appears to be tactic-automation-only or skeletal
  - `31: def totalWeight (w : X → R) : R :=`

## `InfoGeometry.Canonical.ConformalAlgebra`
- path: `lean/InfoGeometry/Canonical/ConformalAlgebra.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L100: **SOFT** `skeletal-proof` in `theorem generatorCartanDecomposition_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `98: def GeneratorCartanDecomposition : Prop :=`
- L37: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `35: `

## `InfoGeometry.Canonical.ConformalAnomalyDegenerate`
- path: `lean/InfoGeometry/Canonical/ConformalAnomalyDegenerate.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L11: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `9: `

## `InfoGeometry.Canonical.ConformalAnomalyOperator`
- path: `lean/InfoGeometry/Canonical/ConformalAnomalyOperator.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L11: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `9: `

## `InfoGeometry.Canonical.ConformalAnomalyReadout`
- path: `lean/InfoGeometry/Canonical/ConformalAnomalyReadout.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L9: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `7: `

## `InfoGeometry.Canonical.ConformalAnomalySource`
- path: `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`
- findings: 9 (hard=0, soft=9, advisory=0)

- L141: **SOFT** `skeletal-proof` in `theorem obstructionScale_eq_projectorObstruction_nnnorm`
  - proof appears to be tactic-automation-only or skeletal
  - `139:           - CI.metricChiralProjector * CI.spectralChiralProjector‖₊ := by`
- L146: **SOFT** `skeletal-proof` in `theorem projectorObstruction_nnnorm_eq_obstructionScale`
  - proof appears to be tactic-automation-only or skeletal
  - `144:     CI.obstructionScale = ‖CI.projectorObstruction‖₊ := by`
- L151: **SOFT** `skeletal-proof` in `theorem chiralScale_eq_obstructionScale`
  - proof appears to be tactic-automation-only or skeletal
  - `149:     ‖CI.projectorObstruction‖₊ = CI.obstructionScale := by`
- L156: **SOFT** `skeletal-proof` in `theorem epsilon_eq_obstructionScale`
  - proof appears to be tactic-automation-only or skeletal
  - `154:     CI.chiralScale = CI.obstructionScale := by`
- L195: **SOFT** `skeletal-proof` in `theorem projectorObstructionSquashCoeff_eq_squashedObstructionScale_div_obstructionScale`
  - proof appears to be tactic-automation-only or skeletal
  - `193:     CI.projectorObstructionSquashCoeff = 0 := by`
- L714: **SOFT** `skeletal-proof` in `theorem unitOfAction_eq_obstructionScale`
  - proof appears to be tactic-automation-only or skeletal
  - `712: `
- L15: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `13: `
- L794: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `792: `
- L820: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `818: `

## `InfoGeometry.Canonical.ConformalProjectorCore`
- path: `lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- findings: 13 (hard=0, soft=13, advisory=0)

- L423: **SOFT** `skeletal-proof` in `theorem specialConformal_eq_modularInversion_translation`
  - proof appears to be tactic-automation-only or skeletal
  - `421: `
- L458: **SOFT** `skeletal-proof` in `theorem dilation_eq_half_sub_mp_projectors`
  - proof appears to be tactic-automation-only or skeletal
  - `456: noncomputable def D : E →L[ℝ] E :=`
- L667: **SOFT** `skeletal-proof` in `theorem singularEinsteinAnomaly_eq_neg_rightChiralAnomaly`
  - proof appears to be tactic-automation-only or skeletal
  - `665:   unfold IsDrazinInverse.projection IsMoorePenroseInverse.rightProjector`
- L778: **SOFT** `skeletal-proof` in `theorem rightProjector_commute_of_projectorAgreement_of_metricProjector_commute`
  - proof appears to be tactic-automation-only or skeletal
  - `776:   simpa [leftChiralAnomalyOperator] using`
- L829: **SOFT** `skeletal-proof` in `theorem chiral_commutation_link`
  - proof appears to be tactic-automation-only or skeletal
  - `827:     CI.spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralAnomaly_eq_zero`
- L841: **SOFT** `skeletal-proof` in `theorem chiralAnomalyOperator_eq_zero_iff_projectors_commute`
  - proof appears to be tactic-automation-only or skeletal
  - `839:         = CI.metricChiralProjector * CI.spectralChiralProjector := by`
- L848: **SOFT** `skeletal-proof` in `theorem leftChiralAnomalyOperator_eq_zero_iff_projectors_commute`
  - proof appears to be tactic-automation-only or skeletal
  - `846:         = CI.metricChiralProjector * CI.spectralChiralProjector := by`
- L68: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `66: `
- L87: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `85: `
- L248: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `246: `
- L276: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `274: `
- L305: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `303: `
- L407: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `405: `

## `InfoGeometry.Canonical.CoordinatelessSouriauCocycleFisherBridge`
- path: `lean/InfoGeometry/Canonical/CoordinatelessSouriauCocycleFisherBridge.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L104: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `102: variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]`
- L122: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `120: `
- L184: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `182: `

## `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- path: `lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- findings: 18 (hard=0, soft=18, advisory=0)

- L51: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `49: `
- L79: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `77: `
- L113: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `111: `
- L130: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `128: `
- L170: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `168: `
- L201: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `199: `
- L220: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `218: `
- L260: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `258: `
- L298: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `296: `
- L327: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `325: `
- L353: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `351: `
- L379: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `377: `
- L411: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `409: `
- L480: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `478: `
- L577: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `575: `
- L665: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `663: `
- L759: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `757: `
- L833: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `831: `

## `InfoGeometry.Canonical.CountPositiveCoupling`
- path: `lean/InfoGeometry/Canonical/CountPositiveCoupling.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L9: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `7: `
- L11: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `9: `

## `InfoGeometry.Canonical.CountSinkhornFlow`
- path: `lean/InfoGeometry/Canonical/CountSinkhornFlow.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L9: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `7: `
- L11: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `9: `

## `InfoGeometry.Canonical.DIIIDrazinEntropyBridge`
- path: `lean/InfoGeometry/Canonical/DIIIDrazinEntropyBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L84: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `82: variable {P0 : KPolarization (S := S) M}`

## `InfoGeometry.Canonical.DIIIModularEntropyFlowBridge`
- path: `lean/InfoGeometry/Canonical/DIIIModularEntropyFlowBridge.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L67: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `65: variable {Op State Time : Type*}`
- L120: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `118: variable {P0 : KPolarization (S := S) M}`
- L51: **SOFT** `witness-field-projection` in `structure-field entropyTransport_valid`
  - witness field `entropyTransport_valid : entropyTransportLaw`
  - `49: `

## `InfoGeometry.Canonical.DeterminantPhaseVolumeBridge`
- path: `lean/InfoGeometry/Canonical/DeterminantPhaseVolumeBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L62: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `60: `
- L113: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `111: `

## `InfoGeometry.Canonical.DiracRicciBridge`
- path: `lean/InfoGeometry/Canonical/DiracRicciBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L115: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `113: `

## `InfoGeometry.Canonical.DiracSouriauOperator`
- path: `lean/InfoGeometry/Canonical/DiracSouriauOperator.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L74: **SOFT** `skeletal-proof` in `theorem toMatrix_eq_fromBlocks`
  - proof appears to be tactic-automation-only or skeletal
  - `72: `

## `InfoGeometry.Canonical.DiscreteModularSpectrum`
- path: `lean/InfoGeometry/Canonical/DiscreteModularSpectrum.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L120: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `118: variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]`

## `InfoGeometry.Canonical.DrazinCentralizerErlangen`
- path: `lean/InfoGeometry/Canonical/DrazinCentralizerErlangen.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L109: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `107: `
- L315: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `313: `
- L390: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `388: `

## `InfoGeometry.Canonical.DrazinCliffordMatrixUnitBridge`
- path: `lean/InfoGeometry/Canonical/DrazinCliffordMatrixUnitBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L55: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `53: `

## `InfoGeometry.Canonical.DrazinCoreFlow`
- path: `lean/InfoGeometry/Canonical/DrazinCoreFlow.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L231: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `229: `

## `InfoGeometry.Canonical.DrazinDescriptorSystems`
- path: `lean/InfoGeometry/Canonical/DrazinDescriptorSystems.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L40: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `38: `

## `InfoGeometry.Canonical.DrazinFierzBridge`
- path: `lean/InfoGeometry/Canonical/DrazinFierzBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L86: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `84: `

## `InfoGeometry.Canonical.DrazinGreen`
- path: `lean/InfoGeometry/Canonical/DrazinGreen.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L158: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `156: `

## `InfoGeometry.Canonical.DrazinGreenHorizonEnvelope`
- path: `lean/InfoGeometry/Canonical/DrazinGreenHorizonEnvelope.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L60: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `58: `

## `InfoGeometry.Canonical.DrazinHodgeChiralBridge`
- path: `lean/InfoGeometry/Canonical/DrazinHodgeChiralBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L66: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `64: `

## `InfoGeometry.Canonical.DrazinHodgeFierzBridge`
- path: `lean/InfoGeometry/Canonical/DrazinHodgeFierzBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L77: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `75: `

## `InfoGeometry.Canonical.DrazinHodgeResidueBridge`
- path: `lean/InfoGeometry/Canonical/DrazinHodgeResidueBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L66: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `64: `

## `InfoGeometry.Canonical.DrazinLightConeDictionary`
- path: `lean/InfoGeometry/Canonical/DrazinLightConeDictionary.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L47: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `45: `
- L229: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `227: `

## `InfoGeometry.Canonical.DrazinMPChiralHodgeConeBridge`
- path: `lean/InfoGeometry/Canonical/DrazinMPChiralHodgeConeBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L164: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `162: `

## `InfoGeometry.Canonical.DrazinModularPersistence`
- path: `lean/InfoGeometry/Canonical/DrazinModularPersistence.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L59: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `57: `
- L357: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `355: variable {Obs : Type*} [Ring Obs] [Star Obs]`

## `InfoGeometry.Canonical.DrazinPenroseDilationAlgebra`
- path: `lean/InfoGeometry/Canonical/DrazinPenroseDilationAlgebra.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L29: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `27: `

## `InfoGeometry.Canonical.DrazinPenroseDilationKKT`
- path: `lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L46: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `44: `

## `InfoGeometry.Canonical.DrazinSum`
- path: `lean/InfoGeometry/Canonical/DrazinSum.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L217: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `215: `
- L257: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `255: `

## `InfoGeometry.Canonical.DrazinSupercharge`
- path: `lean/InfoGeometry/Canonical/DrazinSupercharge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L205: **SOFT** `skeletal-proof` in `theorem supercharge_is_oddK`
  - proof appears to be tactic-automation-only or skeletal
  - `203: `
- L56: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `54: `

## `InfoGeometry.Canonical.DrazinSupergradedWeylSocket`
- path: `lean/InfoGeometry/Canonical/DrazinSupergradedWeylSocket.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L210: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `208: variable {νH : Measure ℝ}`
- L344: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `342: `

## `InfoGeometry.Canonical.DunfordTaylor`
- path: `lean/InfoGeometry/Canonical/DunfordTaylor.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L76: **SOFT** `skeletal-proof` in `theorem mem_resolventSet_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `74: `
- L134: **SOFT** `skeletal-proof` in `theorem dunfordTaylorIntegral_const_contour`
  - proof appears to be tactic-automation-only or skeletal
  - `132: `
- L151: **SOFT** `skeletal-proof` in `theorem rieszProjection_const_contour`
  - proof appears to be tactic-automation-only or skeletal
  - `149: `
- L224: **SOFT** `skeletal-proof` in `theorem rangeInvariantStatement_const_contour`
  - proof appears to be tactic-automation-only or skeletal
  - `222: `

## `InfoGeometry.Canonical.EPAndGroupInverse`
- path: `lean/InfoGeometry/Canonical/EPAndGroupInverse.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L20: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `18: `
- L116: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `114: `

## `InfoGeometry.Canonical.EPDefectAlgebra`
- path: `lean/InfoGeometry/Canonical/EPDefectAlgebra.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L24: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `22: `

## `InfoGeometry.Canonical.EinsteinAnomalyOperator`
- path: `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L162: **SOFT** `skeletal-proof` in `theorem liftedRightChiralAnomalyOperator_ne_zero_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `160:     CCI.leftChiralAnomalyOperator ≠ 0 := by`
- L16: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `14: `
- L725: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `723: `

## `InfoGeometry.Canonical.ErgodicFixedPointBridge`
- path: `lean/InfoGeometry/Canonical/ErgodicFixedPointBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L96: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `94: `
- L213: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `211: `

## `InfoGeometry.Canonical.FierzStressProjectionBridge`
- path: `lean/InfoGeometry/Canonical/FierzStressProjectionBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L66: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `64: `

## `InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge`
- path: `lean/InfoGeometry/Canonical/FiniteCantorPauliMatrixBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L34: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `32: `

## `InfoGeometry.Canonical.FractalFockEquivalenceBridge`
- path: `lean/InfoGeometry/Canonical/FractalFockEquivalenceBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L29: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `27: `

## `InfoGeometry.Canonical.GenerativeInferenceCore`
- path: `lean/InfoGeometry/Canonical/GenerativeInferenceCore.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L318: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `316: variable {S : Type*}`
- L319: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `317: variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S] [FiniteDimensional ℝ S]`

## `InfoGeometry.Canonical.GeometricCalculusFreudenthalBridge`
- path: `lean/InfoGeometry/Canonical/GeometricCalculusFreudenthalBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L327: **SOFT** `skeletal-proof` in `theorem horizonOperator_eq_projector`
  - proof appears to be tactic-automation-only or skeletal
  - `325:     (W : OperatorFreudenthalBoundaryFluxBridge D) : RealEnd E :=`

## `InfoGeometry.Canonical.GeometricCalculusSTUBridge`
- path: `lean/InfoGeometry/Canonical/GeometricCalculusSTUBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L63: **SOFT** `skeletal-proof` in `theorem stuFreudenthalChargeGeometry_I4`
  - proof appears to be tactic-automation-only or skeletal
  - `61: `
- L90: **SOFT** `skeletal-proof` in `theorem stuQubitChargeGeometry_I4`
  - proof appears to be tactic-automation-only or skeletal
  - `88: `

## `InfoGeometry.Canonical.GrandCanonicalExperts`
- path: `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L351: **SOFT** `skeletal-proof` in `lemma diracAction_add_right`
  - proof appears to be tactic-automation-only or skeletal
  - `349:     diracEulerStep 0 D ψ = ψ := by`

## `InfoGeometry.Canonical.GrandCanonicalGaussianScaleShape`
- path: `lean/InfoGeometry/Canonical/GrandCanonicalGaussianScaleShape.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L146: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `144: `

## `InfoGeometry.Canonical.GrandSynthesis`
- path: `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L21: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `19: `

## `InfoGeometry.Canonical.GrandSynthesisGeometry`
- path: `lean/InfoGeometry/Canonical/GrandSynthesisGeometry.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L185: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `183: `

## `InfoGeometry.Canonical.GrandSynthesisThermo`
- path: `lean/InfoGeometry/Canonical/GrandSynthesisThermo.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L35: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `33: `
- L78: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `76: `

## `InfoGeometry.Canonical.HeadTrialityCore`
- path: `lean/InfoGeometry/Canonical/HeadTrialityCore.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L170: **SOFT** `vacuous-prop-constant` in `theorem blocked128_dimension`
  - theorem/lemma is closed by an uninformative constant
  - `168: `

## `InfoGeometry.Canonical.HestenesCohomology`
- path: `lean/InfoGeometry/Canonical/HestenesCohomology.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L150: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `148: `

## `InfoGeometry.Canonical.HestenesKreinAnalyticFlowBridge`
- path: `lean/InfoGeometry/Canonical/HestenesKreinAnalyticFlowBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L66: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `64: `
- L108: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `106: `

## `InfoGeometry.Canonical.HestenesQVandermondeShadow`
- path: `lean/InfoGeometry/Canonical/HestenesQVandermondeShadow.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L38: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `36: `
- L110: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `108: `

## `InfoGeometry.Canonical.HestenesRealStructures`
- path: `lean/InfoGeometry/Canonical/HestenesRealStructures.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L154: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `152: `
- L216: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `214: `

## `InfoGeometry.Canonical.HolographicEmergence`
- path: `lean/InfoGeometry/Canonical/HolographicEmergence.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L32: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `30: `

## `InfoGeometry.Canonical.HorizonStringDiagram`
- path: `lean/InfoGeometry/Canonical/HorizonStringDiagram.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L66: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `64: `
- L114: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `112: `
- L149: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `147: `

## `InfoGeometry.Canonical.HorizonZeroModeFierz`
- path: `lean/InfoGeometry/Canonical/HorizonZeroModeFierz.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L148: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `146: `

## `InfoGeometry.Canonical.HorizonZitterModes`
- path: `lean/InfoGeometry/Canonical/HorizonZitterModes.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L124: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `122: `
- L229: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `227: variable {Obs : Type*}`
- L276: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `274: variable {Obs : Type*}`

## `InfoGeometry.Canonical.IBFiniteMonotonicity`
- path: `lean/InfoGeometry/Canonical/IBFiniteMonotonicity.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L36: **SOFT** `skeletal-proof` in `lemma finiteSliceJaynes_fullSupportPrior`
  - proof appears to be tactic-automation-only or skeletal
  - `34:     (probMeasureToPMF q_n)`

## `InfoGeometry.Canonical.IBFreeEnergy`
- path: `lean/InfoGeometry/Canonical/IBFreeEnergy.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L38: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `36: variable {X : Type*} [MeasurableSpace X] [Nonempty T]`

## `InfoGeometry.Canonical.IBFunctional`
- path: `lean/InfoGeometry/Canonical/IBFunctional.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L13: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `11: `
- L15: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `13: `
- L16: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `14: variable (pX : ProbabilityMeasure X)`
- L33: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `31: `
- L35: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `33: `

## `InfoGeometry.Canonical.IBIteration`
- path: `lean/InfoGeometry/Canonical/IBIteration.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L19: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `17: `
- L21: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `19: `
- L22: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `20: variable (pX : ProbabilityMeasure X)`
- L23: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `21: variable (qT : ProbabilityMeasure T)`
- L29: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `27:   fun x => IBGibbsProb (qT := (qT : Measure T)) β D x <| by`

## `InfoGeometry.Canonical.IBMeasure`
- path: `lean/InfoGeometry/Canonical/IBMeasure.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L81: **SOFT** `skeletal-proof` in `theorem IBNormalize_toMeasure_eq_inv_mass_smul_of_nonzero`
  - proof appears to be tactic-automation-only or skeletal
  - `79: noncomputable def IBNormalize (μ : FiniteMeasure T) : ProbabilityMeasure T :=`
- L115: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `113: `

## `InfoGeometry.Canonical.IBTopological`
- path: `lean/InfoGeometry/Canonical/IBTopological.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L14: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `12: variable {X T : Type*} [MeasurableSpace X] [MeasurableSpace T] [Nonempty T]`

## `InfoGeometry.Canonical.InverseKernelAlgebra`
- path: `lean/InfoGeometry/Canonical/InverseKernelAlgebra.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L40: **SOFT** `skeletal-proof` in `theorem spectralProjector_add_spectralComplementaryProjector`
  - proof appears to be tactic-automation-only or skeletal
  - `38: def rightProjectorMismatch : E →L[ℝ] E :=`
- L45: **SOFT** `skeletal-proof` in `theorem mpRangeProjector_add_mpRangeComplementaryProjector`
  - proof appears to be tactic-automation-only or skeletal
  - `43:     IK.spectralProjector + IK.spectralComplementaryProjector = (1 : E →L[ℝ] E) := by`
- L50: **SOFT** `skeletal-proof` in `theorem metricProjector_add_metricComplementaryProjector`
  - proof appears to be tactic-automation-only or skeletal
  - `48:     IK.mpRangeProjector + IK.mpRangeComplementaryProjector = (1 : E →L[ℝ] E) := by`
- L22: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `20: `
- L107: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `105: `

## `InfoGeometry.Canonical.InverseKernelCartanCore`
- path: `lean/InfoGeometry/Canonical/InverseKernelCartanCore.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L69: **SOFT** `skeletal-proof` in `theorem GammaS_eq_two_mul_spectralProjector_sub_one`
  - proof appears to be tactic-automation-only or skeletal
  - `67: noncomputable abbrev spectralGradingFlow (t : ℝ) : EndH :=`
- L31: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `29: `

## `InfoGeometry.Canonical.InverseKernelNormalForm`
- path: `lean/InfoGeometry/Canonical/InverseKernelNormalForm.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L31: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `29: `
- L81: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `79: `

## `InfoGeometry.Canonical.JaynesRNModularBridge`
- path: `lean/InfoGeometry/Canonical/JaynesRNModularBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L29: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `27: `

## `InfoGeometry.Canonical.KKTConformalChiralContext`
- path: `lean/InfoGeometry/Canonical/KKTConformalChiralContext.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L71: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `69: `

## `InfoGeometry.Canonical.KLinearRepresentation`
- path: `lean/InfoGeometry/Canonical/KLinearRepresentation.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L108: **SOFT** `skeletal-proof` in `lemma neg_kConjugate_comp_K`
  - proof appears to be tactic-automation-only or skeletal
  - `106:     _ = -(f.comp X.K) := by`
- L113: **SOFT** `skeletal-proof` in `lemma neg_K_comp_kConjugate`
  - proof appears to be tactic-automation-only or skeletal
  - `111:     -((kConjugate X f).comp X.K) = X.K.comp f := by`

## `InfoGeometry.Canonical.KMSCocycleGeneratorBridge`
- path: `lean/InfoGeometry/Canonical/KMSCocycleGeneratorBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L22: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `20: `

## `InfoGeometry.Canonical.KMSConditionBridge`
- path: `lean/InfoGeometry/Canonical/KMSConditionBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L125: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `123: `

## `InfoGeometry.Canonical.KMSSinkhornWeightedTransport`
- path: `lean/InfoGeometry/Canonical/KMSSinkhornWeightedTransport.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L20: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `18: `

## `InfoGeometry.Canonical.KaehlerGeometry`
- path: `lean/InfoGeometry/Canonical/KaehlerGeometry.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L35: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `33: `

## `InfoGeometry.Canonical.KramersMajoranaCompatibility`
- path: `lean/InfoGeometry/Canonical/KramersMajoranaCompatibility.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L42: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `40: `

## `InfoGeometry.Canonical.KreinDoubledAtom`
- path: `lean/InfoGeometry/Canonical/KreinDoubledAtom.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L29: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `27: `
- L69: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `67: `

## `InfoGeometry.Canonical.KreinLadder`
- path: `lean/InfoGeometry/Canonical/KreinLadder.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L37: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `35: `

## `InfoGeometry.Canonical.LightConeCARFockBridge`
- path: `lean/InfoGeometry/Canonical/LightConeCARFockBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L48: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `46: `
- L117: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `115: variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]`

## `InfoGeometry.Canonical.LiteratureGrandCanonicalWeylTKK`
- path: `lean/InfoGeometry/Canonical/LiteratureGrandCanonicalWeylTKK.lean`
- findings: 7 (hard=0, soft=7, advisory=0)

- L63: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `61: `
- L93: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `91: `
- L144: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `142: `
- L251: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `249: `
- L341: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `339: `
- L382: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `380: `
- L694: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `692: `

## `InfoGeometry.Canonical.LiteratureTwistorHodgePalatial`
- path: `lean/InfoGeometry/Canonical/LiteratureTwistorHodgePalatial.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L89: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `87: `
- L119: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `117: `
- L160: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `158: `
- L191: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `189: `

## `InfoGeometry.Canonical.MajoranaJKOErgoBridge`
- path: `lean/InfoGeometry/Canonical/MajoranaJKOErgoBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L520: **SOFT** `skeletal-proof` in `theorem one_add_tau_pos`
  - proof appears to be tactic-automation-only or skeletal
  - `518:     P.tau ≠ 0 :=`
- L513: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `511: `

## `InfoGeometry.Canonical.MassieuPlanckWeylScalarBridge`
- path: `lean/InfoGeometry/Canonical/MassieuPlanckWeylScalarBridge.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L67: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `65: `
- L152: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `150: `
- L208: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `206: `

## `InfoGeometry.Canonical.MasterSynthesis`
- path: `lean/InfoGeometry/Canonical/MasterSynthesis.lean`
- findings: 11 (hard=0, soft=11, advisory=0)

- L358: **SOFT** `placeholder-naming` in `theorem bridge_zpe_gravity`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `356:       W.hBoundaryOnZeroModes W.hCentral W.hBoundary`
- L376: **SOFT** `placeholder-naming` in `theorem bridge_zpe_gravity_of_witness`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `374:   ⟨zero_point_energy_topological_obstruction S hRankPos,`
- L395: **SOFT** `placeholder-naming` in `theorem bridge_zpe_gravity_of_certifiedInverseKernel`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `393:       (anomalyStressEnergyAt Kgeo x CI.chiralScale) :=`
- L420: **SOFT** `placeholder-naming` in `theorem bridge_fluid_helicity`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `418:     CI.einsteinEquation_of_projectorObstruction_source c R Kgeo x Λ κ hEin`
- L449: **SOFT** `placeholder-naming` in `theorem bridge_fluid_helicity_of_matchedWitness`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `447:       simpa [hState.1] using hResidualEin`
- L545: **SOFT** `placeholder-naming` in `theorem bridge_fluid_helicity_of_regularizationWitness`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `543:   anomalySkew_of_regularization (A := A) (B_mp := B_mp) (B_dr := B_dr)`
- L566: **SOFT** `placeholder-naming` in `theorem bridge_fluid_helicity_of_productionWitness`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `564:     anomalySkew_of_regularizationWitness (E := E) A B_mp B_dr hReg`
- L583: **SOFT** `placeholder-naming` in `theorem bridge_fluid_helicity_of_canonicalDrazinProductionWitness`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `581:   bridge_fluid_helicity_of_regularizationWitness`
- L604: **SOFT** `placeholder-naming` in `theorem bridge_fluid_helicity_of_regularization`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `602:     (DrazinInfiniteCore.canonicalDrazinInverse_endCLM (E := E) A)`
- L627: **SOFT** `placeholder-naming` in `theorem bridge_fluid_helicity_of_regularization_of_finiteDimensional`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `625:     { h_mp := h_mp, k := k, h_drazin := h_dr, h_star := h_dr_star }`
- L673: **SOFT** `placeholder-naming` in `theorem bridge_thermal_bott_of_witness`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `671:   InformationalLichnerowiczBottBridge.lichnerowiczBalancedCl11_of_operatorialTransport`

## `InfoGeometry.Canonical.ModularCartanCantorSystem`
- path: `lean/InfoGeometry/Canonical/ModularCartanCantorSystem.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L295: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `293: `
- L372: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `370: `
- L449: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `447: `
- L542: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `540: `

## `InfoGeometry.Canonical.ModularHamiltonianSignum`
- path: `lean/InfoGeometry/Canonical/ModularHamiltonianSignum.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L67: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `65: `
- L68: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `66: variable {J S : DoubledSpace E →L[ℝ] DoubledSpace E}`
- L69: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `67: variable (hJ : J * J = (1 : DoubledSpace E →L[ℝ] DoubledSpace E))`
- L314: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `312: `
- L315: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `313: variable {J S p : DoubledSpace E →L[ℝ] DoubledSpace E}`
- L316: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `314: variable (hJ : J * J = (1 : DoubledSpace E →L[ℝ] DoubledSpace E))`

## `InfoGeometry.Canonical.ModularHamiltonianSurrogateCalibration`
- path: `lean/InfoGeometry/Canonical/ModularHamiltonianSurrogateCalibration.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L61: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `59: `

## `InfoGeometry.Canonical.ModularSpectralWedge`
- path: `lean/InfoGeometry/Canonical/ModularSpectralWedge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L57: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `55: `

## `InfoGeometry.Canonical.ModularSuperchargeClosure`
- path: `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L281: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `279: `
- L499: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `497: `
- L1828: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1826: `
- L1949: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1947: `

## `InfoGeometry.Canonical.ModularSurprisalThermoPacket`
- path: `lean/InfoGeometry/Canonical/ModularSurprisalThermoPacket.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L149: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `147: `

## `InfoGeometry.Canonical.MoebiusClosureBridge`
- path: `lean/InfoGeometry/Canonical/MoebiusClosureBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L78: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `76: `

## `InfoGeometry.Canonical.MongeAmpereCramerRao`
- path: `lean/InfoGeometry/Canonical/MongeAmpereCramerRao.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L62: **SOFT** `skeletal-proof` in `theorem absDet_cramerRaoMetric_eq_one_of_incompressible`
  - proof appears to be tactic-automation-only or skeletal
  - `60:       = -Real.log (|LinearMap.det (cramerRaoMetricOp H x).toLinearMap|) := by`

## `InfoGeometry.Canonical.NavierStokesSnapBridge`
- path: `lean/InfoGeometry/Canonical/NavierStokesSnapBridge.lean`
- findings: 7 (hard=0, soft=7, advisory=0)

- L69: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `67: `
- L101: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `99: `
- L140: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `138: `
- L203: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `201:     {G : DualFlatOperatorGeometry Op}`
- L265: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `263:     {G : DualFlatOperatorGeometry Op}`
- L309: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `307: `
- L369: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `367:     {G : FiveGrading L}`

## `InfoGeometry.Canonical.NoncommutativeOperatorAlgebra`
- path: `lean/InfoGeometry/Canonical/NoncommutativeOperatorAlgebra.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L109: **SOFT** `skeletal-proof` in `theorem typeIII_baseIntegral_eq_modularWeight_integral`
  - proof appears to be tactic-automation-only or skeletal
  - `107:     ∃ a b : A, a * b ≠ b * a :=`

## `InfoGeometry.Canonical.OpenProblemFormalization`
- path: `lean/InfoGeometry/Canonical/OpenProblemFormalization.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L148: **SOFT** `skeletal-proof` in `theorem projectedStress_fierz_identity`
  - proof appears to be tactic-automation-only or skeletal
  - `146:   jaynes : PrimeGasJaynesConjecture gas`
- L150: **SOFT** `skeletal-proof` in `theorem projectedStress_majorana_identity`
  - proof appears to be tactic-automation-only or skeletal
  - `148: `
- L166: **SOFT** `skeletal-proof` in `theorem onsager_projectedStress_fierz_identity`
  - proof appears to be tactic-automation-only or skeletal
  - `164:   eulerProductHypothesis : Prop`
- L175: **SOFT** `skeletal-proof` in `theorem toSuperGeometricTemperature_zero_odd`
  - proof appears to be tactic-automation-only or skeletal
  - `173: `
- L177: **SOFT** `skeletal-proof` in `theorem kms_target_projectedStress_fierz_identity`
  - proof appears to be tactic-automation-only or skeletal
  - `175: `
- L195: **SOFT** `skeletal-proof` in `theorem higher_order_projectedStress_fierz_identity`
  - proof appears to be tactic-automation-only or skeletal
  - `193:   entropyProduction_nonneg : Prop`

## `InfoGeometry.Canonical.OperatorAlgebraAQFTPackage`
- path: `lean/InfoGeometry/Canonical/OperatorAlgebraAQFTPackage.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L25: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `23: `
- L80: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `78: `

## `InfoGeometry.Canonical.OperatorErlangenFierzKlein`
- path: `lean/InfoGeometry/Canonical/OperatorErlangenFierzKlein.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L136: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `134: variable {Obs : Type*}`

## `InfoGeometry.Canonical.OperatorInformationGeometryBridge`
- path: `lean/InfoGeometry/Canonical/OperatorInformationGeometryBridge.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L47: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `45: `
- L85: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `83: `
- L112: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `110: `
- L141: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `139: `
- L167: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `165: `

## `InfoGeometry.Canonical.OperatorJKOStep`
- path: `lean/InfoGeometry/Canonical/OperatorJKOStep.lean`
- findings: 7 (hard=0, soft=7, advisory=0)

- L117: **SOFT** `skeletal-proof` in `theorem objective_le_previous_energy`
  - proof appears to be tactic-automation-only or skeletal
  - `115: `
- L60: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `58: `
- L115: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `113: variable {Weight : Type*}`
- L189: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `187: variable {Weight : Type*}`
- L249: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `247: variable {Weight Evidence : Type*}`
- L315: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `313: variable {Weight Noise : Type*}`
- L354: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `352: variable {Weight FlowReadout : Type*}`

## `InfoGeometry.Canonical.OperatorModularTemperatureDuality`
- path: `lean/InfoGeometry/Canonical/OperatorModularTemperatureDuality.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L64: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `62: `
- L147: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `145: `
- L224: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `222: variable {H Op : Type*}`

## `InfoGeometry.Canonical.OperatorSurgery`
- path: `lean/InfoGeometry/Canonical/OperatorSurgery.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L337: **SOFT** `skeletal-proof` in `theorem identitySplit_projector_nil`
  - proof appears to be tactic-automation-only or skeletal
  - `335: `
- L61: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `59: `

## `InfoGeometry.Canonical.OperatorThermodynamics`
- path: `lean/InfoGeometry/Canonical/OperatorThermodynamics.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L226: **SOFT** `skeletal-proof` in `theorem partitionPotential_eq_freeEnergy`
  - proof appears to be tactic-automation-only or skeletal
  - `224: `

## `InfoGeometry.Canonical.OperatorValuedSouriauFamily`
- path: `lean/InfoGeometry/Canonical/OperatorValuedSouriauFamily.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L131: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `129: `

## `InfoGeometry.Canonical.OptimalMetricGraphEmbeddingBridge`
- path: `lean/InfoGeometry/Canonical/OptimalMetricGraphEmbeddingBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L27: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `25: `

## `InfoGeometry.Canonical.PSLDescent`
- path: `lean/InfoGeometry/Canonical/PSLDescent.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L47: **SOFT** `skeletal-proof` in `theorem sl2z_neg_smul`
  - proof appears to be tactic-automation-only or skeletal
  - `45:     simp`

## `InfoGeometry.Canonical.PauliHestenesSpinMomentum`
- path: `lean/InfoGeometry/Canonical/PauliHestenesSpinMomentum.lean`
- findings: 15 (hard=0, soft=15, advisory=0)

- L75: **SOFT** `skeletal-proof` in `theorem trace_pauliMatrix_eq_two_energy`
  - proof appears to be tactic-automation-only or skeletal
  - `73:   rw [Complex.I_sq]`
- L231: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `229: `
- L310: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `308: variable {SpinGroup V Herm2 : Type*}`
- L392: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `390: variable {Spinor V Herm2 : Type*}`
- L440: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `438: `
- L484: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `482: `
- L548: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `546: `
- L588: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `586: `
- L650: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `648: `
- L713: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `711: `
- L749: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `747: variable {Spinor Momentum SpinPlane : Type*}`
- L798: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `796: `
- L848: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `846: `
- L899: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `897: variable {Spinor Rotor Bivector SpinInvariant : Type*}`
- L946: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `944: variable {Spinor Rotor Bivector : Type*}`

## `InfoGeometry.Canonical.PedersenTakesakiRNInterface`
- path: `lean/InfoGeometry/Canonical/PedersenTakesakiRNInterface.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L60: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `58: `

## `InfoGeometry.Canonical.PerelmanWCore`
- path: `lean/InfoGeometry/Canonical/PerelmanWCore.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L31: **SOFT** `skeletal-proof` in `lemma deriv_WFunctional_eq_of_law`
  - proof appears to be tactic-automation-only or skeletal
  - `29:     (flow : ScalarRicciFlow E) (τ f diss : ℝ → ℝ) : Prop :=`

## `InfoGeometry.Canonical.PfaffianPathDeterminantBridge`
- path: `lean/InfoGeometry/Canonical/PfaffianPathDeterminantBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L104: **SOFT** `skeletal-proof` in `theorem pathDeterminantVolume_eq_pfaffian_sq`
  - proof appears to be tactic-automation-only or skeletal
  - `102: `

## `InfoGeometry.Canonical.PhaseSpaceRecompositionExample`
- path: `lean/InfoGeometry/Canonical/PhaseSpaceRecompositionExample.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L123: **SOFT** `skeletal-proof` in `theorem trivialCocycle_isCocycle`
  - proof appears to be tactic-automation-only or skeletal
  - `121:     intro s A`

## `InfoGeometry.Canonical.PhysicsOfInformationCore`
- path: `lean/InfoGeometry/Canonical/PhysicsOfInformationCore.lean`
- findings: 9 (hard=0, soft=9, advisory=0)

- L110: **SOFT** `skeletal-proof` in `theorem bridge_totalMass_preserved`
  - proof appears to be tactic-automation-only or skeletal
  - `108:     (canonicalCliffordState P).1 + (canonicalCliffordState P).2 = 1 := by`
- L110: **SOFT** `placeholder-naming` in `theorem bridge_totalMass_preserved`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `108:     (canonicalCliffordState P).1 + (canonicalCliffordState P).2 = 1 := by`
- L118: **SOFT** `skeletal-proof` in `theorem bridge_modeEntropy_preserved`
  - proof appears to be tactic-automation-only or skeletal
  - `116:     cliffordTotalMass (toCliffordPresentation P) = permutationTotalMass P := by`
- L118: **SOFT** `placeholder-naming` in `theorem bridge_modeEntropy_preserved`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `116:     cliffordTotalMass (toCliffordPresentation P) = permutationTotalMass P := by`
- L126: **SOFT** `skeletal-proof` in `theorem bridge_parityEntropy_preserved`
  - proof appears to be tactic-automation-only or skeletal
  - `124:     cliffordModeEntropy (toCliffordPresentation P) = permutationModeEntropy P := by`
- L126: **SOFT** `placeholder-naming` in `theorem bridge_parityEntropy_preserved`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `124:     cliffordModeEntropy (toCliffordPresentation P) = permutationModeEntropy P := by`
- L134: **SOFT** `skeletal-proof` in `theorem bridge_semanticState_eq_canonical`
  - proof appears to be tactic-automation-only or skeletal
  - `132:     cliffordParityEntropy (toCliffordPresentation P) = permutationParityEntropy P := by`
- L134: **SOFT** `placeholder-naming` in `theorem bridge_semanticState_eq_canonical`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `132:     cliffordParityEntropy (toCliffordPresentation P) = permutationParityEntropy P := by`
- L142: **SOFT** `placeholder-naming` in `theorem bridge_semanticState_coord_sum_eq_totalMass`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `140:     (toCliffordPresentation P).semanticState = canonicalCliffordState P := by`

## `InfoGeometry.Canonical.PositiveMeasureSpectrum`
- path: `lean/InfoGeometry/Canonical/PositiveMeasureSpectrum.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L13: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `11: variable {H₂ : Type*}`

## `InfoGeometry.Canonical.PrimeGasMaxEnt`
- path: `lean/InfoGeometry/Canonical/PrimeGasMaxEnt.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L66: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `64: `

## `InfoGeometry.Canonical.PrimeGasSuperKMSBridge`
- path: `lean/InfoGeometry/Canonical/PrimeGasSuperKMSBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L80: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `78: `

## `InfoGeometry.Canonical.PrimeGasWeylCharacterBridge`
- path: `lean/InfoGeometry/Canonical/PrimeGasWeylCharacterBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L58: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `56: `

## `InfoGeometry.Canonical.ProjectiveCCR`
- path: `lean/InfoGeometry/Canonical/ProjectiveCCR.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L51: **SOFT** `skeletal-proof` in `theorem excitedStateSector_eq_orthogonal`
  - proof appears to be tactic-automation-only or skeletal
  - `49: `

## `InfoGeometry.Canonical.ProjectiveCountsModularBridge`
- path: `lean/InfoGeometry/Canonical/ProjectiveCountsModularBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L113: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `111: `
- L188: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `186: `

## `InfoGeometry.Canonical.ProjectiveFoundation`
- path: `lean/InfoGeometry/Canonical/ProjectiveFoundation.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L70: **SOFT** `skeletal-proof` in `theorem baseAction_is_genuine`
  - proof appears to be tactic-automation-only or skeletal
  - `68:     [Group Γ] [MulAction Γ X] [Group R] :=`

## `InfoGeometry.Canonical.ProjectorNoncommutativityDilationClosure`
- path: `lean/InfoGeometry/Canonical/ProjectorNoncommutativityDilationClosure.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L163: **SOFT** `skeletal-proof` in `theorem dilation_isGZero`
  - proof appears to be tactic-automation-only or skeletal
  - `161:     (dilation_witness_of_source CI hSource hSourceCertified).sourceWitness :=`

## `InfoGeometry.Canonical.QVandermondePhaseLockShadow`
- path: `lean/InfoGeometry/Canonical/QVandermondePhaseLockShadow.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L35: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `33: `
- L94: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `92: `

## `InfoGeometry.Canonical.QuantumGeometryDualSheetBridge`
- path: `lean/InfoGeometry/Canonical/QuantumGeometryDualSheetBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L18: **SOFT** `skeletal-proof` in `theorem cramerRaoMetricOp_eq_quantumGeometryOp`
  - proof appears to be tactic-automation-only or skeletal
  - `16: noncomputable def quantumGeometryOp (H : HessianGeometry E) (x : E) : E →L[ℝ] E :=`

## `InfoGeometry.Canonical.RadioactivePoissonBitStream`
- path: `lean/InfoGeometry/Canonical/RadioactivePoissonBitStream.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L118: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `116: `

## `InfoGeometry.Canonical.RealBerryRotorBridge`
- path: `lean/InfoGeometry/Canonical/RealBerryRotorBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L173: **SOFT** `skeletal-proof` in `theorem realModularBerryRotorBridge_tendsto`
  - proof appears to be tactic-automation-only or skeletal
  - `171:       D.R_cusp * D.R_orbifold_i * D.R_orbifold_rho :=`

## `InfoGeometry.Canonical.RealHestenesKreinHomology`
- path: `lean/InfoGeometry/Canonical/RealHestenesKreinHomology.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L54: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `52: variable {C : Type*}`
- L148: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `146: `
- L194: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `192: variable {C : Type*}`
- L289: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `287: variable {C : Type*}`

## `InfoGeometry.Canonical.RealHestenesKreinPipelineCapstone`
- path: `lean/InfoGeometry/Canonical/RealHestenesKreinPipelineCapstone.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L46: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `44: `
- L93: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `91: `
- L174: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `172: `

## `InfoGeometry.Canonical.RealHomologyCohomologyDictionary`
- path: `lean/InfoGeometry/Canonical/RealHomologyCohomologyDictionary.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L55: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `53: variable {C : Type*}`
- L147: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `145: `
- L187: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `185: variable {Chain Cochain : Type*}`
- L236: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `234: variable {Chain Cochain : Type*}`
- L527: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `525: `

## `InfoGeometry.Canonical.RealIncidenceHomology`
- path: `lean/InfoGeometry/Canonical/RealIncidenceHomology.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L47: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `45: `
- L98: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `96: `
- L234: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `232: `

## `InfoGeometry.Canonical.RealIncidenceHomologyBridge`
- path: `lean/InfoGeometry/Canonical/RealIncidenceHomologyBridge.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L48: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `46: `
- L93: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `91: `
- L152: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `150: `
- L241: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `239: `

## `InfoGeometry.Canonical.RealTomitaCore`
- path: `lean/InfoGeometry/Canonical/RealTomitaCore.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L67: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `65: `

## `InfoGeometry.Canonical.RelativeModularBerezinianBridge`
- path: `lean/InfoGeometry/Canonical/RelativeModularBerezinianBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L400: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `398: `

## `InfoGeometry.Canonical.RelativePotentialCountBridge`
- path: `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L31: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `29: `

## `InfoGeometry.Canonical.RicciMongeAmpere`
- path: `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L144: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `142: `

## `InfoGeometry.Canonical.RindlerWedgeCartanBridge`
- path: `lean/InfoGeometry/Canonical/RindlerWedgeCartanBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L62: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `60: `
- L110: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `108: `

## `InfoGeometry.Canonical.RobustThermodynamicRegression`
- path: `lean/InfoGeometry/Canonical/RobustThermodynamicRegression.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L57: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `55: noncomputable def gibbsWeights (E : Data → Theta → ℝ) (θ : Theta) (ε : ℝ) (i : Data) : ℝ :=`

## `InfoGeometry.Canonical.SUSYBayes`
- path: `lean/InfoGeometry/Canonical/SUSYBayes.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L82: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `80: `
- L83: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `81: variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]`
- L84: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `82: variable (R : RicciTensor E)`
- L85: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `83: variable (K : KaehlerInformationGeometry E) (x : E)`

## `InfoGeometry.Canonical.SYKTwoCopyInterface`
- path: `lean/InfoGeometry/Canonical/SYKTwoCopyInterface.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L107: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `105: `

## `InfoGeometry.Canonical.SemilinearPaperLean4`
- path: `lean/InfoGeometry/Canonical/SemilinearPaperLean4.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L14: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `12: `
- L40: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `38: `
- L60: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `58: `
- L73: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `71: `

## `InfoGeometry.Canonical.SingularBoundaryCorrection`
- path: `lean/InfoGeometry/Canonical/SingularBoundaryCorrection.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L107: **SOFT** `skeletal-proof` in `theorem boundaryGenerator_eq_projector_commutator`
  - proof appears to be tactic-automation-only or skeletal
  - `105: abbrev dilationOperator : E →L[ℝ] E :=`
- L113: **SOFT** `skeletal-proof` in `theorem rightBoundaryGenerator_eq_projector_commutator`
  - proof appears to be tactic-automation-only or skeletal
  - `111:       S.spectralProjector * S.leftProjector - S.leftProjector * S.spectralProjector := by`
- L77: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `75: `

## `InfoGeometry.Canonical.SingularTransportSystem`
- path: `lean/InfoGeometry/Canonical/SingularTransportSystem.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L54: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `52: `

## `InfoGeometry.Canonical.SinkhornFoundation`
- path: `lean/InfoGeometry/Canonical/SinkhornFoundation.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L155: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `153: `
- L348: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `346: `
- L620: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `618: `

## `InfoGeometry.Canonical.SinkhornGaugeThermodynamicsBridge`
- path: `lean/InfoGeometry/Canonical/SinkhornGaugeThermodynamicsBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L29: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `27: `
- L116: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `114: `

## `InfoGeometry.Canonical.SinkhornKMSCore`
- path: `lean/InfoGeometry/Canonical/SinkhornKMSCore.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L109: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `107: `

## `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- path: `lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L86: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `84: `
- L169: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `167: `

## `InfoGeometry.Canonical.SouriauConformalKKTContext`
- path: `lean/InfoGeometry/Canonical/SouriauConformalKKTContext.lean`
- findings: 10 (hard=0, soft=10, advisory=0)

- L66: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `64: `
- L228: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `226: `
- L399: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `397: `
- L552: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `550: `
- L698: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `696: variable {L : Type _} [LieRing L] [LieAlgebra ℝ L]`
- L787: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `785: `
- L864: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `862: `
- L1123: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1121: `
- L1168: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1166: `
- L1220: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1218: `

## `InfoGeometry.Canonical.SouriauDensityWeightContext`
- path: `lean/InfoGeometry/Canonical/SouriauDensityWeightContext.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L61: **SOFT** `skeletal-proof` in `theorem densityWeight_eq_numberWeight`
  - proof appears to be tactic-automation-only or skeletal
  - `59: `
- L41: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `39: `

## `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge`
- path: `lean/InfoGeometry/Canonical/SouriauFenchelOnsagerBridge.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L57: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `55: `
- L94: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `92: `
- L148: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `146: `

## `InfoGeometry.Canonical.SouriauKreinMetriplecticContext`
- path: `lean/InfoGeometry/Canonical/SouriauKreinMetriplecticContext.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L79: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `77: `

## `InfoGeometry.Canonical.SouriauLieThermoKKTBridge`
- path: `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L96: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `94: `
- L191: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `189: `
- L439: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `437:     (moment_in_orbit := fun x => ⟨x, rfl⟩)`
- L677: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `675: `
- L731: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `729: `

## `InfoGeometry.Canonical.SouriauMetriplecticContext`
- path: `lean/InfoGeometry/Canonical/SouriauMetriplecticContext.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L51: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `49: `

## `InfoGeometry.Canonical.SouriauModularBregmanOperator`
- path: `lean/InfoGeometry/Canonical/SouriauModularBregmanOperator.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L55: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `53: `
- L283: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `281: `
- L328: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `326: `

## `InfoGeometry.Canonical.SouriauModularHamiltonianBridge`
- path: `lean/InfoGeometry/Canonical/SouriauModularHamiltonianBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L123: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `121: `
- L322: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `320: `

## `InfoGeometry.Canonical.SouriauOperatorialLogPotential`
- path: `lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L782: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `780: `
- L880: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `878: `

## `InfoGeometry.Canonical.SouriauSurprisalKLFreeEnergyBridge`
- path: `lean/InfoGeometry/Canonical/SouriauSurprisalKLFreeEnergyBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L197: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `195: `
- L242: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `240: `

## `InfoGeometry.Canonical.SouriauTomitaModularFlowBridge`
- path: `lean/InfoGeometry/Canonical/SouriauTomitaModularFlowBridge.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L47: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `45: `
- L205: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `203: `
- L347: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `345:     kms_state_eq := hstate`
- L427: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `425: `
- L505: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `503: `

## `InfoGeometry.Canonical.SpectralGeneratorProxy`
- path: `lean/InfoGeometry/Canonical/SpectralGeneratorProxy.lean`
- findings: 8 (hard=0, soft=8, advisory=0)

- L47: **SOFT** `vacuous-prop-constant` in `theorem axis`
  - theorem/lemma is closed by an uninformative constant
  - `45:   change (T.comp K) v = (K.comp T) v`
- L86: **SOFT** `skeletal-proof` in `theorem sub`
  - proof appears to be tactic-automation-only or skeletal
  - `84:   rw [apply hT v]`
- L212: **SOFT** `skeletal-proof` in `theorem denominator_right_inverse`
  - proof appears to be tactic-automation-only or skeletal
  - `210:     PhaseLinear K R.boundedCayley := by`
- L150: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `148: `
- L265: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `263: `
- L304: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `302: `
- L367: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `365: variable {A : Type*}`
- L454: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `452: variable {K : EndR H}`

## `InfoGeometry.Canonical.SpectralInference`
- path: `lean/InfoGeometry/Canonical/SpectralInference.lean`
- findings: 7 (hard=0, soft=7, advisory=0)

- L140: **SOFT** `skeletal-proof` in `theorem spectralProjector_idempotent`
  - proof appears to be tactic-automation-only or skeletal
  - `138: `
- L63: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `61: `
- L108: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `106: `
- L122: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `120: `
- L183: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `181: `
- L201: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `199: `
- L331: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `329: `

## `InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge`
- path: `lean/InfoGeometry/Canonical/SplitCl44TKKJordanLieBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L119: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `117: `

## `InfoGeometry.Canonical.StandardFormNaturalConeBridge`
- path: `lean/InfoGeometry/Canonical/StandardFormNaturalConeBridge.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L91: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `89: `
- L172: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `170: `
- L254: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `252: `
- L561: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `559: `
- L664: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `662: `
- L750: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `748: `

## `InfoGeometry.Canonical.StandardFormOmegaVolumeBridge`
- path: `lean/InfoGeometry/Canonical/StandardFormOmegaVolumeBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L94: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `92: variable {Word : Type*}`

## `InfoGeometry.Canonical.StandardFormProjectiveGWBridge`
- path: `lean/InfoGeometry/Canonical/StandardFormProjectiveGWBridge.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L122: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `120: `
- L228: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `226: `
- L117: **SOFT** `witness-field-projection` in `structure-field standardForm_state_valid`
  - witness field `standardForm_state_valid : standardForm_state_calibration`
  - `115: `
- L223: **SOFT** `witness-field-projection` in `structure-field face_state_valid`
  - witness field `face_state_valid : face_state_calibration`
  - `221: `

## `InfoGeometry.Canonical.SuperAnomaly`
- path: `lean/InfoGeometry/Canonical/SuperAnomaly.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L69: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `67: `

## `InfoGeometry.Canonical.SuperSouriauFermionGasBridge`
- path: `lean/InfoGeometry/Canonical/SuperSouriauFermionGasBridge.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L48: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `46: `
- L112: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `110: `
- L220: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `218: `

## `InfoGeometry.Canonical.SuperUnified`
- path: `lean/InfoGeometry/Canonical/SuperUnified.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L65: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `63:   eps_sq : epsilon.comp epsilon = ContinuousLinearMap.id ℝ (DoubledSpace E)`

## `InfoGeometry.Canonical.SuperchargeModularHamiltonianBridge`
- path: `lean/InfoGeometry/Canonical/SuperchargeModularHamiltonianBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L53: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `51: `

## `InfoGeometry.Canonical.SuperchargeOddOddDecomposition`
- path: `lean/InfoGeometry/Canonical/SuperchargeOddOddDecomposition.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L62: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `60: `

## `InfoGeometry.Canonical.SupergradedRandomWalkZeroModes`
- path: `lean/InfoGeometry/Canonical/SupergradedRandomWalkZeroModes.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L279: **SOFT** `skeletal-proof` in `theorem matterEnvelope_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `277:     Matrix V V ℝ :=`

## `InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus`
- path: `lean/InfoGeometry/Canonical/ThermodynamicChiralGraphCalculus.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L614: **SOFT** `skeletal-proof` in `theorem entropyProduction_nonneg_of_pointwise`
  - proof appears to be tactic-automation-only or skeletal
  - `612:   pointwise_nonneg : ∀ e, 0 ≤ G.flow e * G.affinity e`
- L831: **SOFT** `skeletal-proof` in `theorem graph_wilsonLoop_eq_triangle`
  - proof appears to be tactic-automation-only or skeletal
  - `829: def cycle : Cycle TriangleEdge where`
- L838: **SOFT** `skeletal-proof` in `theorem detailedBalance_iff_graph_cycle_ratio_product_eq_one`
  - proof appears to be tactic-automation-only or skeletal
  - `836:   simp [DirectedThermoGraph.wilsonLoop, graph, cycle]`
- L845: **SOFT** `skeletal-proof` in `theorem graph_cycleGaugeClosed`
  - proof appears to be tactic-automation-only or skeletal
  - `843:       (T.kAB / T.kBA) * (T.kBC / T.kCB) * (T.kCA / T.kAC) = 1 := by`

## `InfoGeometry.Canonical.TimeReversalKramers`
- path: `lean/InfoGeometry/Canonical/TimeReversalKramers.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L43: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `41: `
- L104: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `102: `

## `InfoGeometry.Canonical.TomitaCliffordJordanLieBridge`
- path: `lean/InfoGeometry/Canonical/TomitaCliffordJordanLieBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L76: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `74: `

## `InfoGeometry.Canonical.TomitaTakesakiRealStandardForm`
- path: `lean/InfoGeometry/Canonical/TomitaTakesakiRealStandardForm.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L103: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `101: `

## `InfoGeometry.Canonical.TopologicalEuler`
- path: `lean/InfoGeometry/Canonical/TopologicalEuler.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L17: **SOFT** `skeletal-proof` in `theorem euler_is_invariant`
  - proof appears to be tactic-automation-only or skeletal
  - `15: noncomputable def eulerCharacteristic (IST : InfoSpectralTriple E) : ℝ :=`

## `InfoGeometry.Canonical.TransportLieDerivative`
- path: `lean/InfoGeometry/Canonical/TransportLieDerivative.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L175: **SOFT** `skeletal-proof` in `lemma hasDerivAt_expTransportEnd_at_zero`
  - proof appears to be tactic-automation-only or skeletal
  - `173: noncomputable def expTransportEnd (X A : EndN) (t : ℝ) : EndN :=`
- L181: **SOFT** `skeletal-proof` in `theorem deriv_expTransportEnd_at_zero`
  - proof appears to be tactic-automation-only or skeletal
  - `179:     HasDerivAt (fun t => expTransportEnd X A t) ⁅X, A⁆ 0 := by`
- L416: **SOFT** `skeletal-proof` in `theorem deriv_hestenesTransport_at_zero`
  - proof appears to be tactic-automation-only or skeletal
  - `414: noncomputable abbrev complexLike (A : KAxis E) (a b : ℝ) : EndN :=`

## `InfoGeometry.Canonical.TypeIIIContinuousCoreReal`
- path: `lean/InfoGeometry/Canonical/TypeIIIContinuousCoreReal.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L49: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `47: `
- L185: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `183: `

## `InfoGeometry.Canonical.TypeIIILambdaCore`
- path: `lean/InfoGeometry/Canonical/TypeIIILambdaCore.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L113: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `111: variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]`
- L195: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `193: variable {CIK : CertifiedInverseKernel (InfoGeometry.Krein.DoubledSpace E)}`

## `InfoGeometry.Canonical.TypeIIIModularCantorSystem`
- path: `lean/InfoGeometry/Canonical/TypeIIIModularCantorSystem.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L156: **SOFT** `skeletal-proof` in `theorem antiDiagonal_antiSelfDual`
  - proof appears to be tactic-automation-only or skeletal
  - `154: `
- L112: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `110: variable [AddCommGroup Left] [Module ℝ Left]`
- L185: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `183: variable [AddCommGroup Left] [Module ℝ Left]`

## `InfoGeometry.Canonical.TypeIIISouriauCalibration`
- path: `lean/InfoGeometry/Canonical/TypeIIISouriauCalibration.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L73: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `71: `

## `InfoGeometry.Canonical.UhlmannBuresHolonomy`
- path: `lean/InfoGeometry/Canonical/UhlmannBuresHolonomy.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L10: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `8: variable {H₂ : Type*}`

## `InfoGeometry.Canonical.Unification`
- path: `lean/InfoGeometry/Canonical/Unification.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L47: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `45: variable {E : Type*}`
- L116: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `114: `
- L271: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `269: `

## `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra`
- path: `lean/InfoGeometry/Canonical/UnifiedSuperchargeAlgebra.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L150: **SOFT** `skeletal-proof` in `theorem projected_supercharge_eq_sub_chiral`
  - proof appears to be tactic-automation-only or skeletal
  - `148:     (InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge_eq_two_smul_commutatorK_spectralProjector_dilationGap`
- L155: **SOFT** `skeletal-proof` in `theorem projected_left_eq_commutator_PD_PL`
  - proof appears to be tactic-automation-only or skeletal
  - `153:     QD U = QR U - QL U := by`
- L161: **SOFT** `skeletal-proof` in `theorem projected_right_eq_commutator_PD_PR`
  - proof appears to be tactic-automation-only or skeletal
  - `159:       InfoGeometry.Canonical.DrazinSupercharge.commutator (PD U) (PL U) := by`
- L53: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `51: `
- L530: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `528: `
- L619: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `617: `

## `InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge`
- path: `lean/InfoGeometry/Canonical/UnifiedSuperchargeOddOddBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L51: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `49: `

## `InfoGeometry.Canonical.UnifiedTopologicalGapBridge`
- path: `lean/InfoGeometry/Canonical/UnifiedTopologicalGapBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L55: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `53: `

## `InfoGeometry.Canonical.VandermondeExclusionBridge`
- path: `lean/InfoGeometry/Canonical/VandermondeExclusionBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L41: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `39: `
- L70: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `68: `

## `InfoGeometry.Canonical.VarlamovClifford`
- path: `lean/InfoGeometry/Canonical/VarlamovClifford.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L58: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `56: `
- L123: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `121: `
- L205: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `203: `

## `InfoGeometry.Canonical.VolumeDeformationPrinciple`
- path: `lean/InfoGeometry/Canonical/VolumeDeformationPrinciple.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L88: **SOFT** `skeletal-proof` in `theorem character_mulCommutator_eq_one`
  - proof appears to be tactic-automation-only or skeletal
  - `86:   apply add_left_cancel (a := a)`

## `InfoGeometry.Canonical.WedgeBoostModularBridge`
- path: `lean/InfoGeometry/Canonical/WedgeBoostModularBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L149: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `147: `

## `InfoGeometry.Canonical.WeylA2AlternatingDeterminantShadow`
- path: `lean/InfoGeometry/Canonical/WeylA2AlternatingDeterminantShadow.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L28: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `26: `

## `InfoGeometry.Canonical.WeylA2CancellationChart`
- path: `lean/InfoGeometry/Canonical/WeylA2CancellationChart.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L33: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `31: `

## `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow`
- path: `lean/InfoGeometry/Canonical/WeylA2ProductDivisibilityShadow.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L38: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `36: `

## `InfoGeometry.Canonical.WeylAlternatingNumeratorShadow`
- path: `lean/InfoGeometry/Canonical/WeylAlternatingNumeratorShadow.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L48: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `46: `
- L105: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `103: `

## `InfoGeometry.Canonical.WeylAntisymmetricDivisibilityShadow`
- path: `lean/InfoGeometry/Canonical/WeylAntisymmetricDivisibilityShadow.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L31: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `29: `

## `InfoGeometry.Canonical.WeylBKMDriftMassBridge`
- path: `lean/InfoGeometry/Canonical/WeylBKMDriftMassBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L115: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `113: `
- L192: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `190: `

## `InfoGeometry.Canonical.WeylCharacterEquivalence`
- path: `lean/InfoGeometry/Canonical/WeylCharacterEquivalence.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L60: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `58: `
- L93: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `91: `
- L119: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `117: `
- L245: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `243: `
- L267: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `265: `

## `InfoGeometry.Canonical.WeylCharacterVandermondeShadow`
- path: `lean/InfoGeometry/Canonical/WeylCharacterVandermondeShadow.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L48: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `46: `
- L88: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `86: `

## `InfoGeometry.Canonical.WeylEntropyShiftBridge`
- path: `lean/InfoGeometry/Canonical/WeylEntropyShiftBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L36: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `34: `

## `InfoGeometry.Canonical.WeylFiveGradeBalanceBridge`
- path: `lean/InfoGeometry/Canonical/WeylFiveGradeBalanceBridge.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L104: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `102: `
- L131: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `129: `
- L206: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `204: `

## `InfoGeometry.Canonical.WeylFiveGradePhysicalReadoutBridge`
- path: `lean/InfoGeometry/Canonical/WeylFiveGradePhysicalReadoutBridge.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L86: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `84: `
- L120: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `118: `
- L157: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `155: `
- L206: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `204: variable {E : Type}`
- L247: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `245: variable {VolumeState MassState : Type*} {E : Type}`

## `InfoGeometry.Canonical.WeylGWVolumeBridge`
- path: `lean/InfoGeometry/Canonical/WeylGWVolumeBridge.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L77: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `75: `
- L117: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `115: `
- L166: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `164: `
- L216: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `214: `
- L287: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `285: `

## `InfoGeometry.Canonical.WeylHomogeneousReadoutBridge`
- path: `lean/InfoGeometry/Canonical/WeylHomogeneousReadoutBridge.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L35: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `33: `
- L90: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `88: `
- L127: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `125: `

## `InfoGeometry.Canonical.WeylKKTAnomalyIdentity`
- path: `lean/InfoGeometry/Canonical/WeylKKTAnomalyIdentity.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L77: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `75: `
- L186: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `184: `

## `InfoGeometry.Canonical.WeylLocalCancellationShadow`
- path: `lean/InfoGeometry/Canonical/WeylLocalCancellationShadow.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L45: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `43: `

## `InfoGeometry.Canonical.WeylNormalizedCARCCRBridge`
- path: `lean/InfoGeometry/Canonical/WeylNormalizedCARCCRBridge.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L68: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `66: `
- L251: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `249: `
- L387: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `385: `
- L475: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `473: `
- L542: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `540: `

## `InfoGeometry.Canonical.WeylPathHysteresis`
- path: `lean/InfoGeometry/Canonical/WeylPathHysteresis.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L22: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `20: `
- L61: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `59: `

## `InfoGeometry.Canonical.WeylPolynomialDivisibilityShadow`
- path: `lean/InfoGeometry/Canonical/WeylPolynomialDivisibilityShadow.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L38: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `36: `

## `InfoGeometry.Canonical.WeylTwoNodeCancellationChart`
- path: `lean/InfoGeometry/Canonical/WeylTwoNodeCancellationChart.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L35: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `33: `

## `InfoGeometry.Canonical.YangMillsContinuum`
- path: `lean/InfoGeometry/Canonical/YangMillsContinuum.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L185: **SOFT** `skeletal-proof` in `theorem modularAutomorphismGroup_eq_of_time_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `183:       = commutator M.modularHamiltonian A :=`

## `InfoGeometry.Canonical.ZetaTraceBridge`
- path: `lean/InfoGeometry/Canonical/ZetaTraceBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L24: **SOFT** `skeletal-proof` in `theorem zeta_trace_bridge`
  - proof appears to be tactic-automation-only or skeletal
  - `22:   eulerProduct_eq_prime_tprod :`

## `InfoGeometry.Cartan.Involution`
- path: `lean/InfoGeometry/Cartan/Involution.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L101: **SOFT** `skeletal-proof` in `lemma Pplus_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `99:     abel_nf`
- L106: **SOFT** `skeletal-proof` in `lemma Pminus_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `104: lemma Pplus_apply (x : E) : (Pplus θ) x = (⅟(2 : 𝕜)) • (x + θ x) := by`
- L31: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `29: def IsCartanInvolution (θ : Module.End 𝕜 E) : Prop :=`

## `InfoGeometry.Clifford.CartanInstance`
- path: `lean/InfoGeometry/Clifford/CartanInstance.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L16: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `14: `

## `InfoGeometry.Clifford.Cl11Matrix`
- path: `lean/InfoGeometry/Clifford/Cl11Matrix.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L108: **SOFT** `skeletal-proof` in `lemma finrank_mat2`
  - proof appears to be tactic-automation-only or skeletal
  - `106: lemma cl11ToMat_surjective : Function.Surjective cl11ToMat :=`

## `InfoGeometry.Clifford.HestenesDirac`
- path: `lean/InfoGeometry/Clifford/HestenesDirac.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L99: **SOFT** `skeletal-proof` in `theorem current_eq_density_smul_velocityFrame`
  - proof appears to be tactic-automation-only or skeletal
  - `97: def spinAxis (ψ : DiracHestenesSpinor A) : A :=`
- L168: **SOFT** `skeletal-proof` in `theorem polar_current_eq_density_velocity`
  - proof appears to be tactic-automation-only or skeletal
  - `166: def phasePlane_of_polar (P : DiracHestenesPolarDecomposition A) : A :=`
- L173: **SOFT** `skeletal-proof` in `theorem polar_spinPlane_eq_density_spinPlane`
  - proof appears to be tactic-automation-only or skeletal
  - `171:     P.current_of_polar = P.densityScale P.density P.velocityFrameReadout := by`
- L178: **SOFT** `skeletal-proof` in `theorem yvonTakabayasiAngle_of_polar_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `176:     P.spinPlane_of_polar = P.densityScale P.density P.orientedSpinPlane := by`
- L532: **SOFT** `skeletal-proof` in `theorem concrete_det_realification_eq_interval_sq`
  - proof appears to be tactic-automation-only or skeletal
  - `530:     MinkowskiCoordinates.interval, RealMatrix4.matMul]`
- L593: **SOFT** `skeletal-proof` in `theorem concreteMajoranaBdG_det_eq_pfaffian_sq`
  - proof appears to be tactic-automation-only or skeletal
  - `591:   apply RealMatrix4.ext <;> simp [RealMatrix4.transpose, concreteMajoranaBdGMatrix,`

## `InfoGeometry.Clifford.MatrixCompat`
- path: `lean/InfoGeometry/Clifford/MatrixCompat.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L12: **SOFT** `skeletal-proof` in `lemma baseJ1_sq`
  - proof appears to be tactic-automation-only or skeletal
  - `10: `

## `InfoGeometry.Clifford.SplitQ11`
- path: `lean/InfoGeometry/Clifford/SplitQ11.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L34: **SOFT** `skeletal-proof` in `theorem splitQ11_sub`
  - proof appears to be tactic-automation-only or skeletal
  - `32:   simp only [splitQ11_apply, splitB11_apply, Prod.fst_add, Prod.snd_add]`

## `InfoGeometry.Compatibility.MathlibProjectiveDescentShadow`
- path: `lean/InfoGeometry/Compatibility/MathlibProjectiveDescentShadow.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L41: **SOFT** `skeletal-proof` in `theorem sl2z_neg_smul`
  - proof appears to be tactic-automation-only or skeletal
  - `39:     simp`

## `InfoGeometry.Compatibility.MathlibUpperHalfPlaneShadow`
- path: `lean/InfoGeometry/Compatibility/MathlibUpperHalfPlaneShadow.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L66: **SOFT** `skeletal-proof` in `theorem realToMathlibUHP_im`
  - proof appears to be tactic-automation-only or skeletal
  - `64: `
- L93: **SOFT** `skeletal-proof` in `theorem chiralToComplex_im`
  - proof appears to be tactic-automation-only or skeletal
  - `91: `
- L112: **SOFT** `skeletal-proof` in `theorem chiral_normSq_shadow`
  - proof appears to be tactic-automation-only or skeletal
  - `110:       chiralToComplex z * chiralToComplex w := by`
- L143: **SOFT** `skeletal-proof` in `theorem realDenomSq_pos`
  - proof appears to be tactic-automation-only or skeletal
  - `141: abbrev realDenomSq (g : SL2R) (τ : RealUpperHalfPlane) : ℝ :=`
- L165: **SOFT** `skeletal-proof` in `theorem denom_shadow_matrix`
  - proof appears to be tactic-automation-only or skeletal
  - `163:     simp [chiralToComplex, rawChiralDenominator,`

## `InfoGeometry.CondensedMatter.CliffordAtomsZ2n`
- path: `lean/InfoGeometry/CondensedMatter/CliffordAtomsZ2n.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L132: **SOFT** `skeletal-proof` in `theorem flipBit_other`
  - proof appears to be tactic-automation-only or skeletal
  - `130: `
- L290: **SOFT** `skeletal-proof` in `theorem local_charge_is_four_bit`
  - proof appears to be tactic-automation-only or skeletal
  - `288: `
- L74: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `72: `
- L166: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `164: `
- L220: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `218: `
- L288: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `286: `

## `InfoGeometry.Convex.Bregman`
- path: `lean/InfoGeometry/Convex/Bregman.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L21: **SOFT** `skeletal-proof` in `lemma bregmanThreePoint`
  - proof appears to be tactic-automation-only or skeletal
  - `19: noncomputable def bregmanDiv (F : ℝ → ℝ) (x y : ℝ) : ℝ :=`

## `InfoGeometry.Convex.Duality`
- path: `lean/InfoGeometry/Convex/Duality.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L27: **SOFT** `skeletal-proof` in `lemma KL_param_eq_bregman_swap`
  - proof appears to be tactic-automation-only or skeletal
  - `25: noncomputable def KL_param (A : ℝ → ℝ) (θ θ' : ℝ) : ℝ :=`
- L89: **SOFT** `skeletal-proof` in `lemma KL_param_nonneg_of_convex_at`
  - proof appears to be tactic-automation-only or skeletal
  - `87:     0 ≤ bregman f θ θ' :=`

## `InfoGeometry.Convex.FenchelConjugate`
- path: `lean/InfoGeometry/Convex/FenchelConjugate.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L58: **SOFT** `skeletal-proof` in `theorem fenchelYoung_eq_of_conj_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `56:   have h := le_fenchelConj (f := f) (y := y) (x := x) hb`

## `InfoGeometry.Convex.HessianGeometry`
- path: `lean/InfoGeometry/Convex/HessianGeometry.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L223: **SOFT** `skeletal-proof` in `theorem metric_nonneg`
  - proof appears to be tactic-automation-only or skeletal
  - `221:     simpa [real_inner_comm] using hprobe_deriv.nonneg_of_monotone hprobe_mono`
- L104: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `102: `

## `InfoGeometry.Convex.SpinFactorHessian`
- path: `lean/InfoGeometry/Convex/SpinFactorHessian.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L40: **SOFT** `skeletal-proof` in `lemma spinFactor_radon_nikodym_entropy`
  - proof appears to be tactic-automation-only or skeletal
  - `38: `

## `InfoGeometry.Core.DerivativesSmoke`
- path: `lean/InfoGeometry/Core/DerivativesSmoke.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L16: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `14: `

## `InfoGeometry.Core.Involution`
- path: `lean/InfoGeometry/Core/Involution.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L174: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `172: `
- L208: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `206: `
- L240: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `238: `

## `InfoGeometry.Core.MajoranaLiftPacket`
- path: `lean/InfoGeometry/Core/MajoranaLiftPacket.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L46: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `44: `

## `InfoGeometry.Core.SymmetricLie`
- path: `lean/InfoGeometry/Core/SymmetricLie.lean`
- findings: 15 (hard=0, soft=15, advisory=0)

- L189: **SOFT** `skeletal-proof` in `lemma mem_evenSubmodule_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `187:         _ = a • (-x) := by rw [hx]`
- L193: **SOFT** `skeletal-proof` in `lemma mem_oddSubmodule_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `191:     x ∈ S.evenSubmodule ↔ S.θ x = x := by`
- L269: **SOFT** `skeletal-proof` in `lemma even_convex`
  - proof appears to be tactic-automation-only or skeletal
  - `267:     x ∈ S.evenLieSubalgebra ↔ S.θ x = x :=`
- L274: **SOFT** `skeletal-proof` in `lemma odd_convex`
  - proof appears to be tactic-automation-only or skeletal
  - `272:     Convex ℝ (S.evenLieSubalgebra : Set L) := by`
- L413: **SOFT** `skeletal-proof` in `lemma plusPart_add`
  - proof appears to be tactic-automation-only or skeletal
  - `411:     S.P_minus x = S.minusPart x := by`
- L417: **SOFT** `skeletal-proof` in `lemma minusPart_add`
  - proof appears to be tactic-automation-only or skeletal
  - `415:     S.plusPart (x + y) = S.plusPart x + S.plusPart y := by`
- L421: **SOFT** `skeletal-proof` in `lemma plusPart_smul`
  - proof appears to be tactic-automation-only or skeletal
  - `419:     S.minusPart (x + y) = S.minusPart x + S.minusPart y := by`
- L425: **SOFT** `skeletal-proof` in `lemma minusPart_smul`
  - proof appears to be tactic-automation-only or skeletal
  - `423:     S.plusPart (a • x) = a • S.plusPart x := by`
- L441: **SOFT** `skeletal-proof` in `lemma convex_plusPart_image`
  - proof appears to be tactic-automation-only or skeletal
  - `439:   map_add' := S.minusPart_add`
- L446: **SOFT** `skeletal-proof` in `lemma convex_minusPart_image`
  - proof appears to be tactic-automation-only or skeletal
  - `444:     Convex ℝ (S.plusPart '' s) := by`
- L451: **SOFT** `skeletal-proof` in `lemma convex_plusPart_preimage`
  - proof appears to be tactic-automation-only or skeletal
  - `449:     Convex ℝ (S.minusPart '' s) := by`
- L456: **SOFT** `skeletal-proof` in `lemma convex_minusPart_preimage`
  - proof appears to be tactic-automation-only or skeletal
  - `454:     Convex ℝ (S.plusPart ⁻¹' s) := by`
- L461: **SOFT** `skeletal-proof` in `lemma decomposition`
  - proof appears to be tactic-automation-only or skeletal
  - `459:     Convex ℝ (S.minusPart ⁻¹' s) := by`
- L536: **SOFT** `skeletal-proof` in `lemma cartan_left_inverse`
  - proof appears to be tactic-automation-only or skeletal
  - `534:     intro a x`
- L704: **SOFT** `skeletal-proof` in `lemma oddLocalModel_convex`
  - proof appears to be tactic-automation-only or skeletal
  - `702: @[simp] lemma oddLocalModel_tripleSystem (S : SymmetricLieAlgebra L) :`

## `InfoGeometry.Core.SymmetricLieGeneric`
- path: `lean/InfoGeometry/Core/SymmetricLieGeneric.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L78: **SOFT** `skeletal-proof` in `lemma P_plus_fixed`
  - proof appears to be tactic-automation-only or skeletal
  - `76:     S.P_minus x = (⅟ (2 : R)) • (x - S.θ x) := by`
- L24: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `22: `
- L301: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `299: `
- L374: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `372:     extends SymmetricLieAlgebra R L where`
- L413: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `411: `

## `InfoGeometry.Core.SymmetricLieSpaces`
- path: `lean/InfoGeometry/Core/SymmetricLieSpaces.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L41: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `39: `
- L206: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `204: `

## `InfoGeometry.Dynamics.OperatorialRicciFlow`
- path: `lean/InfoGeometry/Dynamics/OperatorialRicciFlow.lean`
- findings: 8 (hard=0, soft=8, advisory=0)

- L96: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `94: variable {State Op : Type*} [AddCommGroup State] [Module ℝ State]`
- L157: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `155: variable [Ring Op] [StarRing Op]`
- L223: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `221: variable [Ring Op] [StarRing Op]`
- L276: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `274: variable {F : OperatorialRicciFlow State Op}`
- L362: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `360: `
- L430: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `428: `
- L497: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `495: `
- L561: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `559: `

## `InfoGeometry.EntropicInference`
- path: `lean/InfoGeometry/EntropicInference.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L69: **SOFT** `skeletal-proof` in `lemma cond_theta_given_x_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `67: `

## `InfoGeometry.Exceptional.Freudenthal`
- path: `lean/InfoGeometry/Exceptional/Freudenthal.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L61: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `59: `

## `InfoGeometry.ExponentialFamily.Analytic.LogSumExp`
- path: `lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L334: **SOFT** `skeletal-proof` in `lemma logSumExp_deriv_eq_mean`
  - proof appears to be tactic-automation-only or skeletal
  - `332:     _ = logSumExpMoment1 w a θ / logSumExpPartition w a θ := by`

## `InfoGeometry.ExponentialFamily.Analytic.Softmax`
- path: `lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L40: **SOFT** `skeletal-proof` in `lemma softmaxPartition_pos`
  - proof appears to be tactic-automation-only or skeletal
  - `38: `
- L45: **SOFT** `skeletal-proof` in `lemma softmaxProb_pos`
  - proof appears to be tactic-automation-only or skeletal
  - `43:     0 < softmaxPartition w a θ := by`
- L50: **SOFT** `skeletal-proof` in `lemma softmaxProb_sum_one`
  - proof appears to be tactic-automation-only or skeletal
  - `48:     0 < softmaxProb w a θ i := by`

## `InfoGeometry.ExponentialFamily.Gaussian`
- path: `lean/InfoGeometry/ExponentialFamily/Gaussian.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L26: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `24: `

## `InfoGeometry.ExponentialFamily.TwistedGaussian`
- path: `lean/InfoGeometry/ExponentialFamily/TwistedGaussian.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L58: **SOFT** `skeletal-proof` in `theorem normal_iff_commutes`
  - proof appears to be tactic-automation-only or skeletal
  - `56:           simp [TG.sigma_symm.adjoint_eq, TG.adjoint_T_eq_neg]`
- L27: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `25: `

## `InfoGeometry.External.Virasoro.AffineKacMoody`
- path: `lean/InfoGeometry/External/Virasoro/AffineKacMoody.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L31: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `29: variable (𝕜 : Type u) [CommRing 𝕜] [IsAddTorsionFree 𝕜]`
- L32: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `30: variable (𝓰 : Type u) [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]`

## `InfoGeometry.External.Virasoro.CentralChargeCalc`
- path: `lean/InfoGeometry/External/Virasoro/CentralChargeCalc.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L175: **SOFT** `skeletal-proof` in `lemma zMonomialF_zero_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `173:         simp [sub_add, prod_range_succ']`
- L179: **SOFT** `skeletal-proof` in `lemma zMonomialF_one_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `177:     zMonomialF R 0 n = 1 := by`
- L183: **SOFT** `skeletal-proof` in `lemma zMonomialF_two_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `181:     zMonomialF R 1 n = n := by`
- L187: **SOFT** `skeletal-proof` in `lemma zMonomialF_three_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `185:     zMonomialF R 2 n = n * (n - 1) / 2 := by`
- L191: **SOFT** `skeletal-proof` in `lemma zMonomialF_four_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `189:     zMonomialF R 3 n = n * (n - 1) * (n - 2) / 6 := by`
- L195: **SOFT** `skeletal-proof` in `lemma zMonomialF_five_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `193:     zMonomialF R 4 n = n * (n - 1) * (n - 2) * (n - 3) / 24 := by`

## `InfoGeometry.External.Virasoro.CentralExtension`
- path: `lean/InfoGeometry/External/Virasoro/CentralExtension.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L121: **SOFT** `skeletal-proof` in `lemma bracket_smul`
  - proof appears to be tactic-automation-only or skeletal
  - `119:     γ.bracket Z Z = 0 := by`
- L163: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `161: `

## `InfoGeometry.External.Virasoro.Commutator`
- path: `lean/InfoGeometry/External/Virasoro/Commutator.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L32: **SOFT** `skeletal-proof` in `lemma commutator_comm`
  - proof appears to be tactic-automation-only or skeletal
  - `30: def commutator (A B : V →ₗ[𝕜] V) : V →ₗ[𝕜] V :=`
- L37: **SOFT** `skeletal-proof` in `lemma mul_eq_mul_add_commutator`
  - proof appears to be tactic-automation-only or skeletal
  - `35:     A.commutator B = - B.commutator A := by`
- L112: **SOFT** `skeletal-proof` in `lemma algebraCommutator'_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `110:     rw [smul_sub]`

## `InfoGeometry.External.Virasoro.CyclicTripleSum`
- path: `lean/InfoGeometry/External/Virasoro/CyclicTripleSum.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L71: **SOFT** `skeletal-proof` in `lemma cyclicTripleSum_map_add_fst_of_map_add`
  - proof appears to be tactic-automation-only or skeletal
  - `69:     cyclicTripleSum β φ x y z = cyclicTripleSum β φ z x y := by`
- L78: **SOFT** `skeletal-proof` in `lemma cyclicTripleSum_map_add_snd_of_map_add`
  - proof appears to be tactic-automation-only or skeletal
  - `76:       = cyclicTripleSum β φ x₁ y z + cyclicTripleSum β φ x₂ y z := by`
- L85: **SOFT** `skeletal-proof` in `lemma cyclicTripleSum_map_smul_fst_of_map_smul`
  - proof appears to be tactic-automation-only or skeletal
  - `83:       = cyclicTripleSum β φ x y₁ z + cyclicTripleSum β φ x y₂ z := by`
- L129: **SOFT** `skeletal-proof` in `lemma cyclicTripleSum_map_smul_of_bilin`
  - proof appears to be tactic-automation-only or skeletal
  - `127: variable {𝕜} [CommSemiring 𝕜]`

## `InfoGeometry.External.Virasoro.FockSpace`
- path: `lean/InfoGeometry/External/Virasoro/FockSpace.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L160: **SOFT** `skeletal-proof` in `lemma heisenbergTri_kgen_mem_cartan`
  - proof appears to be tactic-automation-only or skeletal
  - `158:           ⟨some 0, Set.mem_insert_of_mem none rfl⟩`
- L164: **SOFT** `skeletal-proof` in `lemma heisenbergTri_jgen_zero_mem_cartan`
  - proof appears to be tactic-automation-only or skeletal
  - `162:     .kgen 𝕜 ∈ (heisenbergTri 𝕜).cartan := by`

## `InfoGeometry.External.Virasoro.HeisenbergAlgebra`
- path: `lean/InfoGeometry/External/Virasoro/HeisenbergAlgebra.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L214: **SOFT** `skeletal-proof` in `lemma add_def'`
  - proof appears to be tactic-automation-only or skeletal
  - `212:         (toAbelianLieAlgebraOn X) (toAbelianLieAlgebraOn Y) :=`
- L243: **SOFT** `skeletal-proof` in `lemma kgen_eq_ofCentral_one`
  - proof appears to be tactic-automation-only or skeletal
  - `241: `
- L245: **SOFT** `skeletal-proof` in `lemma kgen_eq'`
  - proof appears to be tactic-automation-only or skeletal
  - `243: `
- L51: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `49: `

## `InfoGeometry.External.Virasoro.IsCentralExtension`
- path: `lean/InfoGeometry/External/Virasoro/IsCentralExtension.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L73: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `71: variable {𝕜 : Type u} [CommRing 𝕜]`
- L176: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `174:          [LieRing 𝓮] [LieAlgebra 𝕜 𝓮]`

## `InfoGeometry.External.Virasoro.LieAlgebraModuleUEA`
- path: `lean/InfoGeometry/External/Virasoro/LieAlgebraModuleUEA.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L70: **SOFT** `skeletal-proof` in `lemma Algebra.scalar_smul_eq_smul_algebraMap_mul`
  - proof appears to be tactic-automation-only or skeletal
  - `68: `
- L84: **SOFT** `skeletal-proof` in `lemma moduleScalarOfModule.smul_def`
  - proof appears to be tactic-automation-only or skeletal
  - `82: def moduleScalarOfModule : Module 𝕜 V :=`
- L254: **SOFT** `skeletal-proof` in `lemma UniversalEnvelopingAlgebra.mkAlgHom_surjective`
  - proof appears to be tactic-automation-only or skeletal
  - `252: `
- L357: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `355: variable {V : Type*} [AddCommGroup V] [Module 𝕂 V] [Module 𝕜 V]`

## `InfoGeometry.External.Virasoro.LieAlgebraRepresentationOfBasis`
- path: `lean/InfoGeometry/External/Virasoro/LieAlgebraRepresentationOfBasis.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L38: **SOFT** `skeletal-proof` in `lemma Representation.apply_bracket_eq_commutator`
  - proof appears to be tactic-automation-only or skeletal
  - `36:     [SMul 𝕜 𝕂] [IsScalarTower 𝕜 𝕂 V] [SMulCommClass 𝕂 𝕜 V] :=`

## `InfoGeometry.External.Virasoro.LieCohomologySmallDegree`
- path: `lean/InfoGeometry/External/Virasoro/LieCohomologySmallDegree.lean`
- findings: 8 (hard=0, soft=8, advisory=0)

- L173: **SOFT** `skeletal-proof` in `lemma apply_add`
  - proof appears to be tactic-automation-only or skeletal
  - `171: `
- L175: **SOFT** `skeletal-proof` in `lemma apply_add`
  - proof appears to be tactic-automation-only or skeletal
  - `173: `
- L177: **SOFT** `skeletal-proof` in `lemma apply_smul`
  - proof appears to be tactic-automation-only or skeletal
  - `175: `
- L179: **SOFT** `skeletal-proof` in `lemma apply_smul`
  - proof appears to be tactic-automation-only or skeletal
  - `177: `
- L260: **SOFT** `skeletal-proof` in `lemma add_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `258:     simp only [← add_smul, neg_add_cancel, zero_smul]`
- L263: **SOFT** `skeletal-proof` in `lemma smul_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `261: lemma add_apply (γ₁ γ₂ : LieTwoCocycle 𝕜 𝓰 𝓪) (X Y : 𝓰) :`
- L316: **SOFT** `skeletal-proof` in `lemma LieOneCochain.bdry_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `314:   change LieOneCochain_bdryHom 𝕜 𝓰 𝓪 (-β) = -LieOneCochain_bdryHom 𝕜 𝓰 𝓪 β`
- L167: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `165: `

## `InfoGeometry.External.Virasoro.LieVerma`
- path: `lean/InfoGeometry/External/Virasoro/LieVerma.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L193: **SOFT** `skeletal-proof` in `lemma VermaHW.upper_smul_hwVec`
  - proof appears to be tactic-automation-only or skeletal
  - `191:     Submodule.span (𝓤 𝕜 𝓰) {VermaHW.hwVec η} = ⊤ :=`
- L197: **SOFT** `skeletal-proof` in `lemma VermaHW.cartan_smul_hwVec`
  - proof appears to be tactic-automation-only or skeletal
  - `195:     ιUEA 𝕜 E • VermaHW.hwVec η = 0 := by`
- L133: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `131: `
- L158: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `156: def VermaHW (η : weight tri) :=`

## `InfoGeometry.External.Virasoro.Sugawara`
- path: `lean/InfoGeometry/External/Virasoro/Sugawara.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L264: **SOFT** `skeletal-proof` in `lemma sugawaraGenAux_smul`
  - proof appears to be tactic-automation-only or skeletal
  - `262: variable (heiOper) in`
- L273: **SOFT** `skeletal-proof` in `lemma sugawaraGen_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `271:   map_add' v w := sugawaraGenAux_add heiTrunc n v w`
- L58: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `56: `
- L60: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `58: `

## `InfoGeometry.External.Virasoro.ToMathlib.Algebra.Lie.Basic`
- path: `lean/InfoGeometry/External/Virasoro/ToMathlib/Algebra/Lie/Basic.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L17: **SOFT** `skeletal-proof` in `lemma LieAlgebra.bracketHom_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `15: `

## `InfoGeometry.External.Virasoro.ToMathlib.Topology.Algebra.BigOperators.FinProd`
- path: `lean/InfoGeometry/External/Virasoro/ToMathlib/Topology/Algebra/BigOperators/FinProd.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L4: **SOFT** `skeletal-proof` in `lemma Finset.sum_eq_sum_support`
  - proof appears to be tactic-automation-only or skeletal
  - `2: `

## `InfoGeometry.External.Virasoro.VirasoroAlgebra`
- path: `lean/InfoGeometry/External/Virasoro/VirasoroAlgebra.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L95: **SOFT** `skeletal-proof` in `lemma add_def'`
  - proof appears to be tactic-automation-only or skeletal
  - `93: @[simp] lemma bracket_snd (X Y : VirasoroAlgebra 𝕜) :`
- L124: **SOFT** `skeletal-proof` in `lemma cgen_eq_ofCentral_one`
  - proof appears to be tactic-automation-only or skeletal
  - `122: `
- L126: **SOFT** `skeletal-proof` in `lemma cgen_eq'`
  - proof appears to be tactic-automation-only or skeletal
  - `124: `

## `InfoGeometry.External.Virasoro.VirasoroCocycle`
- path: `lean/InfoGeometry/External/Virasoro/VirasoroCocycle.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L51: **SOFT** `skeletal-proof` in `lemma virasoroCocycleBilin_apply_lgen_lgen`
  - proof appears to be tactic-automation-only or skeletal
  - `49:   (lgen 𝕜).constr 𝕜 <| fun n ↦ (lgen 𝕜).constr 𝕜 <| fun m ↦`

## `InfoGeometry.External.Virasoro.VirasoroVerma`
- path: `lean/InfoGeometry/External/Virasoro/VirasoroVerma.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L149: **SOFT** `skeletal-proof` in `lemma virasoroTri_cgen_mem_cartan`
  - proof appears to be tactic-automation-only or skeletal
  - `147:           ⟨some 0, Set.mem_insert_of_mem none rfl⟩`
- L153: **SOFT** `skeletal-proof` in `lemma virasoroTri_lgen_zero_mem_cartan`
  - proof appears to be tactic-automation-only or skeletal
  - `151:     .cgen 𝕜 ∈ (virasoroTri 𝕜).cartan := by`

## `InfoGeometry.External.Virasoro.WittAlgebra`
- path: `lean/InfoGeometry/External/Virasoro/WittAlgebra.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L65: **SOFT** `skeletal-proof` in `lemma lgen_eq_single`
  - proof appears to be tactic-automation-only or skeletal
  - `63: `
- L75: **SOFT** `skeletal-proof` in `lemma bracket_lgen_lgen'`
  - proof appears to be tactic-automation-only or skeletal
  - `73: `
- L86: **SOFT** `skeletal-proof` in `lemma bracket_antisymm`
  - proof appears to be tactic-automation-only or skeletal
  - `84: `

## `InfoGeometry.External.Virasoro.WittAlgebraCohomology`
- path: `lean/InfoGeometry/External/Virasoro/WittAlgebraCohomology.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L33: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `31: variable {𝕜 : Type*} [Field 𝕜]`

## `InfoGeometry.Fenchel`
- path: `lean/InfoGeometry/Fenchel.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L23: **SOFT** `skeletal-proof` in `lemma bregmanDiv_three_point`
  - proof appears to be tactic-automation-only or skeletal
  - `21: namespace Convex`

## `InfoGeometry.Geometry.AnomalousErlangerHeight`
- path: `lean/InfoGeometry/Geometry/AnomalousErlangerHeight.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L59: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `57: `
- L180: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `178: `

## `InfoGeometry.Geometry.BilingualAnalyticity`
- path: `lean/InfoGeometry/Geometry/BilingualAnalyticity.lean`
- findings: 10 (hard=0, soft=10, advisory=0)

- L27: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `25: variable`
- L133: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `131:     {F : X → Y}`
- L357: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `355:     {Region Point Tangent Value : Type*}`
- L437: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `435:     {I : GeometricIntegralBackend Region Point Tangent Value}`
- L570: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `568:     {Ktar : PhaseStructure Y}`
- L689: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `687:     {Fgeo : Point → Value}`
- L778: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `776: `
- L909: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `907: `
- L993: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `991:     {I : GeometricIntegralBackend Region Point Tangent Value}`
- L1200: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1198: `

## `InfoGeometry.Geometry.BilingualPoincareMetric`
- path: `lean/InfoGeometry/Geometry/BilingualPoincareMetric.lean`
- findings: 9 (hard=0, soft=9, advisory=0)

- L71: **SOFT** `skeletal-proof` in `theorem sub`
  - proof appears to be tactic-automation-only or skeletal
  - `69:   intro v`
- L160: **SOFT** `skeletal-proof` in `theorem imaginaryQuadratic_eq_kHeightQuadratic`
  - proof appears to be tactic-automation-only or skeletal
  - `158: `
- L410: **SOFT** `skeletal-proof` in `theorem zero_op`
  - proof appears to be tactic-automation-only or skeletal
  - `408: `
- L427: **SOFT** `skeletal-proof` in `theorem add_op`
  - proof appears to be tactic-automation-only or skeletal
  - `425: `
- L444: **SOFT** `skeletal-proof` in `theorem neg_op`
  - proof appears to be tactic-automation-only or skeletal
  - `442: `
- L461: **SOFT** `skeletal-proof` in `theorem sub_op`
  - proof appears to be tactic-automation-only or skeletal
  - `459: `
- L523: **SOFT** `skeletal-proof` in `theorem moebiusTangentPushForward_op`
  - proof appears to be tactic-automation-only or skeletal
  - `521: `
- L615: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `613: `
- L1070: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1068:     {H : Type*} [AddCommGroup H] [Module ℝ H]`

## `InfoGeometry.Geometry.BilingualUpperHalfPlane`
- path: `lean/InfoGeometry/Geometry/BilingualUpperHalfPlane.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L325: **SOFT** `skeletal-proof` in `theorem moebiusMap_tau`
  - proof appears to be tactic-automation-only or skeletal
  - `323: `
- L141: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `139: `

## `InfoGeometry.Geometry.ChiralTubuleBoundary`
- path: `lean/InfoGeometry/Geometry/ChiralTubuleBoundary.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L382: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `380: `

## `InfoGeometry.Geometry.ConstructiveKasparov`
- path: `lean/InfoGeometry/Geometry/ConstructiveKasparov.lean`
- findings: 12 (hard=0, soft=12, advisory=0)

- L166: **SOFT** `skeletal-proof` in `theorem kernelIndex_eq_even_count_sub_odd_count`
  - proof appears to be tactic-automation-only or skeletal
  - `164:   ((K.evenModes x).length : ℤ) -`
- L176: **SOFT** `skeletal-proof` in `theorem kernelIndex_eq_zero_of_kernelBasis_eq_nil`
  - proof appears to be tactic-automation-only or skeletal
  - `174:         ((K.oddModes x).length : ℤ) :=`
- L237: **SOFT** `skeletal-proof` in `theorem defect_eq_one_sub_square`
  - proof appears to be tactic-automation-only or skeletal
  - `235:     (x : State) : Op :=`
- L252: **SOFT** `skeletal-proof` in `theorem Pker_eq_defect_readout`
  - proof appears to be tactic-automation-only or skeletal
  - `250:     (x : State) : Projection :=`
- L283: **SOFT** `skeletal-proof` in `theorem index_eq_projected_kernel_index`
  - proof appears to be tactic-automation-only or skeletal
  - `281:     (x : State) : ℤ :=`
- L121: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `119: `
- L229: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `227: variable {State Op Projection Mode : Type*}`
- L345: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `343:     {I : GeometricIntegralBackend Region Point Tangent Value}`
- L397: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `395:     {ω : OperatorOneForm Point Tangent Value}`
- L475: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `473:     {ω : OperatorOneForm Point Tangent Value}`
- L591: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `589: variable [Ring Op]`
- L650: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `648:     {ω : OperatorOneForm Point Tangent Value}`

## `InfoGeometry.Geometry.DualFlat`
- path: `lean/InfoGeometry/Geometry/DualFlat.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L69: **SOFT** `skeletal-proof` in `lemma eGeodesic_one`
  - proof appears to be tactic-automation-only or skeletal
  - `67: `
- L143: **SOFT** `skeletal-proof` in `lemma mGeodesic_one`
  - proof appears to be tactic-automation-only or skeletal
  - `141: `
- L149: **SOFT** `skeletal-proof` in `lemma dualCoord_mGeodesic`
  - proof appears to be tactic-automation-only or skeletal
  - `147:     mGeodesic H hGrad x y 1 = y := by`
- L436: **SOFT** `skeletal-proof` in `lemma projectiveDivergence_eq_kl`
  - proof appears to be tactic-automation-only or skeletal
  - `434:     (P Q : UnnormalizedMeasure μ₀) : ENNReal :=`
- L335: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `333:   h_convex : StrictConvexOn ℝ Set.univ ψ`

## `InfoGeometry.Geometry.EntanglementGeometry`
- path: `lean/InfoGeometry/Geometry/EntanglementGeometry.lean`
- findings: 20 (hard=0, soft=20, advisory=0)

- L405: **SOFT** `skeletal-proof` in `theorem left_exterior_to_right_interior`
  - proof appears to be tactic-automation-only or skeletal
  - `403:   | ERZone.exterior Side.right, ERZone.interior Side.left  => True`
- L414: **SOFT** `skeletal-proof` in `theorem right_exterior_to_left_interior`
  - proof appears to be tactic-automation-only or skeletal
  - `412:       (ERZone.interior Side.right) := by`
- L529: **SOFT** `skeletal-proof` in `theorem bell_alice_bob`
  - proof appears to be tactic-automation-only or skeletal
  - `527:     EntanglementIncidence :=`
- L536: **SOFT** `skeletal-proof` in `theorem bell_bob_alice`
  - proof appears to be tactic-automation-only or skeletal
  - `534:     PairEntangled bellAB alice bob := by`
- L560: **SOFT** `skeletal-proof` in `theorem measurement_creates_global_knot`
  - proof appears to be tactic-automation-only or skeletal
  - `558:     ¬ PairEntangled (measureBobWithCharlie s) x y := by`
- L619: **SOFT** `skeletal-proof` in `theorem complexity_nil`
  - proof appears to be tactic-automation-only or skeletal
  - `617:     (C : QuantumCircuit Qubit) : ℕ :=`
- L626: **SOFT** `skeletal-proof` in `theorem complexity_append_gate`
  - proof appears to be tactic-automation-only or skeletal
  - `624:     complexity ([] : QuantumCircuit Qubit) = 0 :=`
- L635: **SOFT** `skeletal-proof` in `theorem complexity_append`
  - proof appears to be tactic-automation-only or skeletal
  - `633:     complexity (C ++ [g]) = complexity C + 1 := by`
- L692: **SOFT** `skeletal-proof` in `theorem bridgeLength_grow`
  - proof appears to be tactic-automation-only or skeletal
  - `690:     CircuitBridgeSlice Qubit where`
- L741: **SOFT** `skeletal-proof` in `theorem zero`
  - proof appears to be tactic-automation-only or skeletal
  - `739: variable {Qubit : Type*}`
- L748: **SOFT** `skeletal-proof` in `theorem succ`
  - proof appears to be tactic-automation-only or skeletal
  - `746:     circuitFromGateStream gates 0 = [] :=`
- L824: **SOFT** `skeletal-proof` in `theorem circuitAt_succ`
  - proof appears to be tactic-automation-only or skeletal
  - `822:     (t : ℕ) : ℕ :=`
- L924: **SOFT** `skeletal-proof` in `theorem quantumRecurrenceScale_eq_two_pow_quantumMaxComplexityScale`
  - proof appears to be tactic-automation-only or skeletal
  - `922:     (K : ℕ) : ℕ :=`
- L49: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `47: `
- L127: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `125: `
- L201: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `199: `
- L273: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `271: `
- L293: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `291: `
- L740: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `738: `
- L799: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `797: `

## `InfoGeometry.Geometry.ErlangerPhaseGeometry`
- path: `lean/InfoGeometry/Geometry/ErlangerPhaseGeometry.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L141: **SOFT** `skeletal-proof` in `theorem sub`
  - proof appears to be tactic-automation-only or skeletal
  - `139:   rw [map_K hT v]`

## `InfoGeometry.Geometry.FiniteDefectStokesModel`
- path: `lean/InfoGeometry/Geometry/FiniteDefectStokesModel.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L82: **SOFT** `skeletal-proof` in `theorem P_apply_one_one`
  - proof appears to be tactic-automation-only or skeletal
  - `80: `
- L141: **SOFT** `skeletal-proof` in `theorem geometricDerivative_ccForm_eq_defect`
  - proof appears to be tactic-automation-only or skeletal
  - `139:     intro Ω f hf`
- L147: **SOFT** `skeletal-proof` in `theorem boundaryIntegral_ccForm`
  - proof appears to be tactic-automation-only or skeletal
  - `145:     defectBackend.geometricDerivative ccForm p = boundedDirac.P :=`
- L152: **SOFT** `skeletal-proof` in `theorem volumeIntegral_defect`
  - proof appears to be tactic-automation-only or skeletal
  - `150:     defectBackend.boundaryIntegral () ccForm = P :=`

## `InfoGeometry.Geometry.FiniteMatrixResolventKernel`
- path: `lean/InfoGeometry/Geometry/FiniteMatrixResolventKernel.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L133: **SOFT** `skeletal-proof` in `theorem matrixResolventKernelOfUnit_kernel`
  - proof appears to be tactic-automation-only or skeletal
  - `131: `
- L200: **SOFT** `skeletal-proof` in `theorem scalarOneByOneResolventKernel_entry`
  - proof appears to be tactic-automation-only or skeletal
  - `198:     rw [inv_mul_cancel₀ h]`
- L55: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `53: variable`

## `InfoGeometry.Geometry.HelicalCovering`
- path: `lean/InfoGeometry/Geometry/HelicalCovering.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L66: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `64: `
- L121: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `119: variable {Base Cover : Type*}`
- L225: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `223: variable {Base Cover : Type*}`
- L289: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `287: variable {Base Cover : Type*}`
- L363: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `361: variable {Spectral Base Cover : Type*}`

## `InfoGeometry.Geometry.IndividuatedUHP`
- path: `lean/InfoGeometry/Geometry/IndividuatedUHP.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L180: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `178: `

## `InfoGeometry.Geometry.JonesTransportMetric`
- path: `lean/InfoGeometry/Geometry/JonesTransportMetric.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L106: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `104: `

## `InfoGeometry.Geometry.KreinIsotropicCone`
- path: `lean/InfoGeometry/Geometry/KreinIsotropicCone.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L68: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `66: `
- L106: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `104: `
- L206: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `204: variable [AddCommGroup H] [Module ℝ H]`

## `InfoGeometry.Geometry.LegendreHessianInverse`
- path: `lean/InfoGeometry/Geometry/LegendreHessianInverse.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L68: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `66: `
- L162: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `160: `

## `InfoGeometry.Geometry.OperatorBregmanDivergence`
- path: `lean/InfoGeometry/Geometry/OperatorBregmanDivergence.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L249: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `247: `

## `InfoGeometry.Geometry.OperatorialJonesConnection`
- path: `lean/InfoGeometry/Geometry/OperatorialJonesConnection.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L150: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `148: variable {Adj : AdjointDatum Op}`

## `InfoGeometry.Geometry.OrbitCurrentStokes`
- path: `lean/InfoGeometry/Geometry/OrbitCurrentStokes.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L49: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `47: `
- L84: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `82: `
- L134: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `132: variable {Value : Type*} [NormedRing Value] [NormedAlgebra ℝ Value]`

## `InfoGeometry.Geometry.PauliParavectorBridge`
- path: `lean/InfoGeometry/Geometry/PauliParavectorBridge.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L141: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `139: `
- L175: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `173: `
- L216: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `214: `

## `InfoGeometry.Geometry.PhaseErlanger`
- path: `lean/InfoGeometry/Geometry/PhaseErlanger.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L129: **SOFT** `skeletal-proof` in `theorem sub`
  - proof appears to be tactic-automation-only or skeletal
  - `127:     map_K hT x`

## `InfoGeometry.Geometry.RealMoebiusAction`
- path: `lean/InfoGeometry/Geometry/RealMoebiusAction.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L74: **SOFT** `skeletal-proof` in `theorem moebius_y`
  - proof appears to be tactic-automation-only or skeletal
  - `72: `
- L166: **SOFT** `skeletal-proof` in `theorem smul_def`
  - proof appears to be tactic-automation-only or skeletal
  - `164: `
- L168: **SOFT** `skeletal-proof` in `theorem one_smul_real`
  - proof appears to be tactic-automation-only or skeletal
  - `166: theorem smul_def (g : SL2R) (τ : RealUpperHalfPlane) :`

## `InfoGeometry.Geometry.RealRotorCore`
- path: `lean/InfoGeometry/Geometry/RealRotorCore.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L78: **SOFT** `skeletal-proof` in `theorem normSq_one`
  - proof appears to be tactic-automation-only or skeletal
  - `76: `

## `InfoGeometry.Geometry.SpectralDivisors`
- path: `lean/InfoGeometry/Geometry/SpectralDivisors.lean`
- findings: 10 (hard=0, soft=10, advisory=0)

- L420: **SOFT** `skeletal-proof` in `theorem phasePeriod_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `418: `
- L648: **SOFT** `skeletal-proof` in `theorem enclosedMultiplicity_eq_sum`
  - proof appears to be tactic-automation-only or skeletal
  - `646:     (Ω : Region) : ℤ :=`
- L62: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `60: `
- L227: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `225: variable {Point Value : Type*}`
- L281: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `279:     {Ktar : PhaseStructure Value}`
- L367: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `365: variable {Value : Type*}`
- L465: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `463:     {N : PhaseResidueNormalizer Value}`
- L641: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `639:     {D : SpectralDivisorDatum Point Value}`
- L749: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `747:     {ω : OperatorOneForm Point Tangent Value}`
- L855: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `853: variable {State Point Value : Type*}`

## `InfoGeometry.Geometry.VerifiedCauchyKernel`
- path: `lean/InfoGeometry/Geometry/VerifiedCauchyKernel.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L41: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `39: variable {Value : Type*} [NormedRing Value] [NormedAlgebra ℝ Value]`
- L98: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `96: variable {Value : Type*} [NormedRing Value] [NormedAlgebra ℝ Value]`

## `InfoGeometry.Geometry.WindingSnap`
- path: `lean/InfoGeometry/Geometry/WindingSnap.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L56: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `54: `
- L172: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `170:     {W : WindingNumberDatum I N ω}`
- L241: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `239:         (I := I) (N := N) (ω := ω) W Cycle}`

## `InfoGeometry.GromovWittenErlangen.CP1DrazinModel`
- path: `lean/InfoGeometry/GromovWittenErlangen/CP1DrazinModel.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L188: **SOFT** `skeletal-proof` in `theorem edgeLocalizedDrazinResidue_line`
  - proof appears to be tactic-automation-only or skeletal
  - `186:     (bridge.edgeDrazinData Edge.line).element = 1 :=`

## `InfoGeometry.GromovWittenErlangen.CP1DrazinNilpotentCountRayExample`
- path: `lean/InfoGeometry/GromovWittenErlangen/CP1DrazinNilpotentCountRayExample.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L302: **SOFT** `skeletal-proof` in `theorem edgeLocalizedDrazinResidue_line`
  - proof appears to be tactic-automation-only or skeletal
  - `300:     (bridge.edgeDrazinData Edge.line).element = (1, 2) :=`

## `InfoGeometry.GromovWittenErlangen.CP1DrazinNilpotentDefectModel`
- path: `lean/InfoGeometry/GromovWittenErlangen/CP1DrazinNilpotentDefectModel.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L134: **SOFT** `skeletal-proof` in `theorem edgeLocalizedDrazinResidue_line`
  - proof appears to be tactic-automation-only or skeletal
  - `132:     (bridge.edgeDrazinData CP1DrazinModel.Edge.line).element = (1, 2) :=`

## `InfoGeometry.GromovWittenErlangen.DrazinLocalization`
- path: `lean/InfoGeometry/GromovWittenErlangen/DrazinLocalization.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L70: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `68: `
- L154: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `152: `
- L179: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `177: `
- L208: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `206: `
- L325: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `323: variable {G T Target Coeff Algebra : Type*} [Ring Algebra]`

## `InfoGeometry.GromovWittenErlangen.Examples.DIIITopologicalCountExample`
- path: `lean/InfoGeometry/GromovWittenErlangen/Examples/DIIITopologicalCountExample.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L72: **SOFT** `skeletal-proof` in `theorem counts_zero`
  - proof appears to be tactic-automation-only or skeletal
  - `70: def referenceCounts : RelativeCounts 3 :=`
- L77: **SOFT** `skeletal-proof` in `theorem counts_one`
  - proof appears to be tactic-automation-only or skeletal
  - `75:     counts (0 : Fin 3) = 100 := by`
- L95: **SOFT** `skeletal-proof` in `theorem referenceCounts_pos`
  - proof appears to be tactic-automation-only or skeletal
  - `93:   intro i`

## `InfoGeometry.GromovWittenErlangen.GWCanonicalCountRayBridge`
- path: `lean/InfoGeometry/GromovWittenErlangen/GWCanonicalCountRayBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L83: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `81: variable {n : ℕ} [Nonempty (Fin n)]`
- L74: **SOFT** `witness-field-projection` in `structure-field finiteCarrierShadow_valid`
  - witness field `finiteCarrierShadow_valid : finiteCarrierShadowLaw`
  - `72:   finiteCarrierShadowLaw :`

## `InfoGeometry.GromovWittenErlangen.GWProjectiveCountCalibration`
- path: `lean/InfoGeometry/GromovWittenErlangen/GWProjectiveCountCalibration.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L86: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `84: `
- L78: **SOFT** `witness-field-projection` in `structure-field countShadow_valid`
  - witness field `countShadow_valid : countShadowLaw`
  - `76: `

## `InfoGeometry.GromovWittenErlangen.LocalizedDrazinFrobeniusBridge`
- path: `lean/InfoGeometry/GromovWittenErlangen/LocalizedDrazinFrobeniusBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L84: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `82: `

## `InfoGeometry.GromovWittenErlangen.ProjectiveCountBridge`
- path: `lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountBridge.lean`
- findings: 7 (hard=0, soft=7, advisory=0)

- L106: **SOFT** `skeletal-proof` in `theorem normalizedShape_scale_counts_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `104:   simpa [normalizedShape] using`
- L75: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `73: `
- L186: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `184: variable {G T Target Coeff : Type*}`
- L223: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `221: `
- L257: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `255: `
- L67: **SOFT** `witness-field-projection` in `structure-field countShadow_valid`
  - witness field `countShadow_valid : countShadowLaw`
  - `65:   countShadowLaw :`
- L178: **SOFT** `witness-field-projection` in `structure-field volumeGauge_valid`
  - witness field `volumeGauge_valid : volumeGaugeLaw`
  - `176: `

## `InfoGeometry.GromovWittenErlangen.ProjectiveCountProbabilityDrazinBridge`
- path: `lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountProbabilityDrazinBridge.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L68: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `66: variable {n : ℕ} [Nonempty (Fin n)]`
- L189: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `187: variable {n : ℕ} [Nonempty (Fin n)]`
- L59: **SOFT** `witness-field-projection` in `structure-field probabilityGauge_valid`
  - witness field `probabilityGauge_valid : probabilityGaugeLaw`
  - `57:   probabilityGaugeLaw :`
- L169: **SOFT** `witness-field-projection` in `structure-field edgeEulerWeight_eq_projectiveCountReadout_valid`
  - witness field `edgeEulerWeight_eq_projectiveCountReadout_valid : edgeEulerWeight_eq_projectiveCountReadout`
  - `167:   edgeEulerWeight_eq_projectiveCountReadout :`
- L180: **SOFT** `witness-field-projection` in `structure-field drazinResidue_eq_projectiveSingularityReadout_valid`
  - witness field `drazinResidue_eq_projectiveSingularityReadout_valid : drazinResidue_eq_projectiveSingularityReadout`
  - `178:   drazinResidue_eq_projectiveSingularityReadout :`

## `InfoGeometry.Information.Basic`
- path: `lean/InfoGeometry/Information/Basic.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L60: **SOFT** `skeletal-proof` in `lemma logLikelihood_eq_neg_logDensity`
  - proof appears to be tactic-automation-only or skeletal
  - `58:     (family : StatisticalFamily α Θ) (θ : Θ) : α → ℝ :=`

## `InfoGeometry.Jordan.LogDet`
- path: `lean/InfoGeometry/Jordan/LogDet.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L71: **SOFT** `skeletal-proof` in `lemma logdet_square_nonneg_of_posDef`
  - proof appears to be tactic-automation-only or skeletal
  - `69:   unfold logDetBregman`

## `InfoGeometry.Jordan.SPD`
- path: `lean/InfoGeometry/Jordan/SPD.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L21: **SOFT** `skeletal-proof` in `lemma SPD.transpose_eq_self`
  - proof appears to be tactic-automation-only or skeletal
  - `19: `

## `InfoGeometry.KK.CompactOperatorBridge`
- path: `lean/InfoGeometry/KK/CompactOperatorBridge.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L14: **SOFT** `skeletal-proof` in `lemma isCompactEnd_zero`
  - proof appears to be tactic-automation-only or skeletal
  - `12: variable {H : Type*}`
- L18: **SOFT** `skeletal-proof` in `lemma isCompactEnd_add`
  - proof appears to be tactic-automation-only or skeletal
  - `16:     IsCompactEnd H (0 : EndH H) := by`
- L23: **SOFT** `skeletal-proof` in `lemma isCompactEnd_smul`
  - proof appears to be tactic-automation-only or skeletal
  - `21:     IsCompactEnd H (A + B) := by`

## `InfoGeometry.KK.KasparovCompactOperator`
- path: `lean/InfoGeometry/KK/KasparovCompactOperator.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L21: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `19: variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]`

## `InfoGeometry.KK.KasparovCycle`
- path: `lean/InfoGeometry/KK/KasparovCycle.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L138: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `136: variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]`

## `InfoGeometry.KK.NonVacuousIndex`
- path: `lean/InfoGeometry/KK/NonVacuousIndex.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L12: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `10: variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]`

## `InfoGeometry.KK.RealSplitKreinBoundedTransform`
- path: `lean/InfoGeometry/KK/RealSplitKreinBoundedTransform.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L146: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `144: `

## `InfoGeometry.KK.RealSplitKreinResolvent`
- path: `lean/InfoGeometry/KK/RealSplitKreinResolvent.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L59: **SOFT** `skeletal-proof` in `lemma isCompactOperator`
  - proof appears to be tactic-automation-only or skeletal
  - `57:     R.shiftedApply ⟨R.resolvent x, R.resolvent_mem_domain x⟩ = x :=`

## `InfoGeometry.KL.EntropicInferenceTest`
- path: `lean/InfoGeometry/KL/EntropicInferenceTest.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L126: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `124: variable [MeasurableSpace X_test] [MeasurableSpace Θ_test]`
- L128: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `126: `
- L129: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `127: variable (p q : Joint X_test Θ_test)`
- L130: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `128: variable (p_x : FinProb X_test)`
- L131: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `129: variable (hposp : ∀ x : X_test, ∀ θ : Θ_test, 0 < (p (x, θ)).toReal)`

## `InfoGeometry.Krein.BoundedKMSHestenesBridge`
- path: `lean/InfoGeometry/Krein/BoundedKMSHestenesBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L89: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `87: `

## `InfoGeometry.Krein.BoundedKMSHestenesVacuumBridge`
- path: `lean/InfoGeometry/Krein/BoundedKMSHestenesVacuumBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L68: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `66: `

## `InfoGeometry.Krein.HestenesAffineO55ClosureBridge`
- path: `lean/InfoGeometry/Krein/HestenesAffineO55ClosureBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L136: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `134: `

## `InfoGeometry.Krein.HestenesAnalyticKMSBridge`
- path: `lean/InfoGeometry/Krein/HestenesAnalyticKMSBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L90: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `88: `

## `InfoGeometry.Krein.HestenesCPTONNDualityBridge`
- path: `lean/InfoGeometry/Krein/HestenesCPTONNDualityBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L135: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `133: `

## `InfoGeometry.Krein.HestenesConnesWilsonBridge`
- path: `lean/InfoGeometry/Krein/HestenesConnesWilsonBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L91: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `89: `
- L201: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `199: variable {Word : Type*}`

## `InfoGeometry.Krein.HestenesD4HurwitzBridge`
- path: `lean/InfoGeometry/Krein/HestenesD4HurwitzBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L128: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `126: variable {Op Automorphism : Type*}`
- L245: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `243: `

## `InfoGeometry.Krein.HestenesKreinNaturalConeBridge`
- path: `lean/InfoGeometry/Krein/HestenesKreinNaturalConeBridge.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L63: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `61: `
- L132: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `130: `
- L195: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `193: `
- L252: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `250: `

## `InfoGeometry.Krein.HestenesKreinRotorBoundaryBridge`
- path: `lean/InfoGeometry/Krein/HestenesKreinRotorBoundaryBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L68: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `66: `
- L147: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `145: `

## `InfoGeometry.Krein.HestenesKreinVacuumBridge`
- path: `lean/InfoGeometry/Krein/HestenesKreinVacuumBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L64: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `62: `

## `InfoGeometry.Krein.HestenesModularKMSBridge`
- path: `lean/InfoGeometry/Krein/HestenesModularKMSBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L72: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `70: `

## `InfoGeometry.Krein.HestenesMoebiusClosureBridge`
- path: `lean/InfoGeometry/Krein/HestenesMoebiusClosureBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L150: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `148: variable {Word : Type*}`

## `InfoGeometry.Krein.HestenesPhaseVolumeBridge`
- path: `lean/InfoGeometry/Krein/HestenesPhaseVolumeBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L61: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `59: variable {P : HestenesKreinKMSPacket (E := E)}`

## `InfoGeometry.Krein.HestenesStandardFormNaturalConeAdapter`
- path: `lean/InfoGeometry/Krein/HestenesStandardFormNaturalConeAdapter.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L40: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `38: `

## `InfoGeometry.Krein.HilbertBridge`
- path: `lean/InfoGeometry/Krein/HilbertBridge.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L267: **SOFT** `skeletal-proof` in `lemma fst_coe`
  - proof appears to be tactic-automation-only or skeletal
  - `265:   rfl`
- L268: **SOFT** `skeletal-proof` in `lemma snd_coe`
  - proof appears to be tactic-automation-only or skeletal
  - `266: @[simp] lemma val_toLp (v : E × E) : (toLp (E := E) v).val = WithLp.toLp 2 v := rfl`
- L269: **SOFT** `skeletal-proof` in `lemma fst_val`
  - proof appears to be tactic-automation-only or skeletal
  - `267: lemma fst_coe (u : NeutralSpace E) : WithLp.fst (u : DoubledSpace E) = u.ofLp.1 := rfl`

## `InfoGeometry.Krein.InvolutiveSelfDualCarrier`
- path: `lean/InfoGeometry/Krein/InvolutiveSelfDualCarrier.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L189: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `187: `

## `InfoGeometry.Krein.KreinSpace`
- path: `lean/InfoGeometry/Krein/KreinSpace.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L105: **SOFT** `skeletal-proof` in `lemma kreinInner_symm`
  - proof appears to be tactic-automation-only or skeletal
  - `103: @[simp] lemma kreinInner_def (u v : H) :`
- L109: **SOFT** `skeletal-proof` in `lemma kreinInner_add_left`
  - proof appears to be tactic-automation-only or skeletal
  - `107: lemma kreinInner_symm (u v : H) : kreinInner u v = kreinInner v u := by`
- L113: **SOFT** `skeletal-proof` in `lemma kreinInner_add_right`
  - proof appears to be tactic-automation-only or skeletal
  - `111:     kreinInner (u₁ + u₂) v = kreinInner u₁ v + kreinInner u₂ v := by`
- L117: **SOFT** `skeletal-proof` in `lemma kreinInner_smul_left`
  - proof appears to be tactic-automation-only or skeletal
  - `115:     kreinInner u (v₁ + v₂) = kreinInner u v₁ + kreinInner u v₂ := by`
- L121: **SOFT** `skeletal-proof` in `lemma kreinInner_smul_right`
  - proof appears to be tactic-automation-only or skeletal
  - `119:     kreinInner (c • u) v = c * kreinInner u v := by`
- L393: **SOFT** `skeletal-proof` in `lemma signFlipMap_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `391: `

## `InfoGeometry.Krein.PolarizedSector`
- path: `lean/InfoGeometry/Krein/PolarizedSector.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L101: **SOFT** `skeletal-proof` in `theorem spectralProj_decomposition`
  - proof appears to be tactic-automation-only or skeletal
  - `99:   simpa [ContinuousLinearMap.comp_apply] using`

## `InfoGeometry.Krein.Thermal`
- path: `lean/InfoGeometry/Krein/Thermal.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L120: **SOFT** `skeletal-proof` in `lemma modular_shift_add`
  - proof appears to be tactic-automation-only or skeletal
  - `118:     modular_shift K 0 B = B := by`

## `InfoGeometry.LLM.KreinAttentionEnergy`
- path: `lean/InfoGeometry/LLM/KreinAttentionEnergy.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L21: **SOFT** `skeletal-proof` in `theorem kreinInteractionEnergy_eq_neg_splitB11`
  - proof appears to be tactic-automation-only or skeletal
  - `19: `

## `InfoGeometry.LLM.RouterFreeEnergyBridge`
- path: `lean/InfoGeometry/LLM/RouterFreeEnergyBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L32: **SOFT** `skeletal-proof` in `theorem normalizedWeights_eq_finite_gibbsWeight`
  - proof appears to be tactic-automation-only or skeletal
  - `30: `

## `InfoGeometry.LLM.SinkhornDefectFlow`
- path: `lean/InfoGeometry/LLM/SinkhornDefectFlow.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L582: **SOFT** `skeletal-proof` in `theorem dissipatedHeatRN_nonneg`
  - proof appears to be tactic-automation-only or skeletal
  - `580:   unfold availableWorkRN`
- L775: **SOFT** `skeletal-proof` in `theorem unitCounts_pos`
  - proof appears to be tactic-automation-only or skeletal
  - `773: noncomputable def unitCounts (n : Nat) : RelativeCounts n :=`
- L780: **SOFT** `skeletal-proof` in `theorem countMass_unitCounts`
  - proof appears to be tactic-automation-only or skeletal
  - `778:   intro i`

## `InfoGeometry.Lint.Pauli`
- path: `lean/InfoGeometry/Lint/Pauli.lean`
- findings: 1 (hard=0, soft=0, advisory=1)

- L23: **ADVISORY** `kernel-placeholder-reference` in `def pauliLinter`
  - declaration references sorryAx/admitAx as kernel identifiers (not a proof hole)
  - `21: private def isCanonical (declName : Name) : Bool :=`

## `InfoGeometry.MaxEnt.Core`
- path: `lean/InfoGeometry/MaxEnt/Core.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L85: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `83: `

## `InfoGeometry.MaxEnt.JaynesInfoStatMech`
- path: `lean/InfoGeometry/MaxEnt/JaynesInfoStatMech.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L286: **SOFT** `skeletal-proof` in `lemma logDensityMatrix_diag_affine`
  - proof appears to be tactic-automation-only or skeletal
  - `284:     logDensityMatrix H β i i = Real.log (gibbsProb H β i) := by`
- L392: **SOFT** `skeletal-proof` in `lemma modularConj_diag_entry`
  - proof appears to be tactic-automation-only or skeletal
  - `390: `

## `InfoGeometry.MaxEnt.JaynesRNMaxEnt`
- path: `lean/InfoGeometry/MaxEnt/JaynesRNMaxEnt.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L83: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `81: `

## `InfoGeometry.Meta.GromovErgostructureBridge`
- path: `lean/InfoGeometry/Meta/GromovErgostructureBridge.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L52: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `50: `
- L93: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `91:     [NormedAddCommGroup V] [NormedSpace ℝ V]`
- L127: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `125:     {E : Type}`
- L146: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `144:     {S : Type*}`

## `InfoGeometry.Meta.Trust`
- path: `lean/InfoGeometry/Meta/Trust.lean`
- findings: 1 (hard=0, soft=0, advisory=1)

- L84: **ADVISORY** `kernel-placeholder-reference` in `def collectHardEvidence`
  - declaration references sorryAx/admitAx as kernel identifiers (not a proof hole)
  - `82:     (info : ConstantInfo) : Bool :=`

## `InfoGeometry.OperatorAlgebra.AffineCl44CardyEntropy`
- path: `lean/InfoGeometry/OperatorAlgebra/AffineCl44CardyEntropy.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L38: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `36:     [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]`
- L80: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `78: `
- L121: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `119:     [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]`
- L112: **SOFT** `witness-field-projection` in `structure-field entropyAgreement_valid`
  - witness field `entropyAgreement_valid : entropyAgreementLaw`
  - `110:     CardyEntropyCalibration`

## `InfoGeometry.OperatorAlgebra.AffineVirasoroBridge`
- path: `lean/InfoGeometry/OperatorAlgebra/AffineVirasoroBridge.lean`
- findings: 7 (hard=0, soft=7, advisory=0)

- L89: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `87: `
- L128: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `126:     {Alg : Type*}`
- L193: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `191: `
- L272: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `270:     [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]`
- L371: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `369:     [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]`
- L506: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `504:     [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]`
- L577: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `575:     [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]`

## `InfoGeometry.OperatorAlgebra.AffineVirasoroExceptionalBridge`
- path: `lean/InfoGeometry/OperatorAlgebra/AffineVirasoroExceptionalBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L86: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `84:     [AddCommGroup State] [Module ℝ State]`

## `InfoGeometry.OperatorAlgebra.AndreevBoundary`
- path: `lean/InfoGeometry/OperatorAlgebra/AndreevBoundary.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L426: **SOFT** `skeletal-proof` in `theorem diagonal_fixed_of_boundary_witness`
  - proof appears to be tactic-automation-only or skeletal
  - `424:     L.boundary.electron + L.boundary.hole ∈ L.boundary.closure.Fixed :=`
- L205: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `203: variable`
- L329: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `327: variable`
- L404: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `402:     [AddCommGroup V] [Module ℝ V]`

## `InfoGeometry.OperatorAlgebra.AndreevHorizonBridge`
- path: `lean/InfoGeometry/OperatorAlgebra/AndreevHorizonBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L53: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `51:     {V HorizonData : Type*}`

## `InfoGeometry.OperatorAlgebra.AndreevLedger`
- path: `lean/InfoGeometry/OperatorAlgebra/AndreevLedger.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L52: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `50: `
- L89: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `87: variable {V : Type*} [AddCommGroup V] [Module ℝ V]`
- L166: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `164: `
- L290: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `288:     [AddCommGroup V] [Module ℝ V]`

## `InfoGeometry.OperatorAlgebra.AnomalousFlowStabilization`
- path: `lean/InfoGeometry/OperatorAlgebra/AnomalousFlowStabilization.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L62: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `60: `

## `InfoGeometry.OperatorAlgebra.AnomalyTubuleStability`
- path: `lean/InfoGeometry/OperatorAlgebra/AnomalyTubuleStability.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L45: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `43: `
- L98: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `96: `
- L244: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `242: `

## `InfoGeometry.OperatorAlgebra.BaryonAsymmetryWitness`
- path: `lean/InfoGeometry/OperatorAlgebra/BaryonAsymmetryWitness.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L71: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `69:     [AddCommGroup V] [Module ℝ V]`

## `InfoGeometry.OperatorAlgebra.BoundedTransformSpectralTriple`
- path: `lean/InfoGeometry/OperatorAlgebra/BoundedTransformSpectralTriple.lean`
- findings: 7 (hard=0, soft=7, advisory=0)

- L122: **SOFT** `skeletal-proof` in `theorem phaseLinear_self`
  - proof appears to be tactic-automation-only or skeletal
  - `120: `
- L252: **SOFT** `skeletal-proof` in `theorem formula`
  - proof appears to be tactic-automation-only or skeletal
  - `250:     C.denomInv.comp (C.D + K.K) = ContinuousLinearMap.id ℝ H :=`
- L113: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `111:     {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]`
- L193: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `191:     {K : PhaseAxis H}`
- L232: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `230:     {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]`
- L314: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `312:     {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]`
- L407: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `405:     [Ring A] [Star A]`

## `InfoGeometry.OperatorAlgebra.BrewsterDrazinIntersection`
- path: `lean/InfoGeometry/OperatorAlgebra/BrewsterDrazinIntersection.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L95: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `93: `
- L152: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `150: `
- L245: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `243: variable {C : BrewsterDrazinCalibration Op}`
- L310: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `308: `

## `InfoGeometry.OperatorAlgebra.CPTChiralBranch`
- path: `lean/InfoGeometry/OperatorAlgebra/CPTChiralBranch.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L63: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `61: `

## `InfoGeometry.OperatorAlgebra.CPTSymmetryBranch`
- path: `lean/InfoGeometry/OperatorAlgebra/CPTSymmetryBranch.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L37: **SOFT** `skeletal-proof` in `theorem chiralSignToReal_flips`
  - proof appears to be tactic-automation-only or skeletal
  - `35: `
- L103: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `101: variable`
- L251: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `249: variable`
- L432: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `430: `
- L589: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `587: `
- L693: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `691: variable`

## `InfoGeometry.OperatorAlgebra.CasimirInvariance`
- path: `lean/InfoGeometry/OperatorAlgebra/CasimirInvariance.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L98: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `96: `

## `InfoGeometry.OperatorAlgebra.ChiralLightconeStinespring`
- path: `lean/InfoGeometry/OperatorAlgebra/ChiralLightconeStinespring.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L59: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `57: `
- L145: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `143: `
- L244: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `242:     [AddCommGroup Joint] [Module ℝ Joint]`
- L329: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `327:     [AddCommGroup Joint] [Module ℝ Joint]`
- L574: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `572: `
- L617: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `615: `

## `InfoGeometry.OperatorAlgebra.ChiralPackingEnergy`
- path: `lean/InfoGeometry/OperatorAlgebra/ChiralPackingEnergy.lean`
- findings: 7 (hard=0, soft=7, advisory=0)

- L262: **SOFT** `skeletal-proof` in `theorem reorient_chirality`
  - proof appears to be tactic-automation-only or skeletal
  - `260: `
- L267: **SOFT** `skeletal-proof` in `theorem sameRay_reorient`
  - proof appears to be tactic-automation-only or skeletal
  - `265:     (reorient R orientation).chirality = orientation :=`
- L276: **SOFT** `skeletal-proof` in `theorem isBenign_reorient`
  - proof appears to be tactic-automation-only or skeletal
  - `274:       R.ray :=`
- L302: **SOFT** `skeletal-proof` in `theorem supportCard_reorientAll`
  - proof appears to be tactic-automation-only or skeletal
  - `300:   rw [← hEq]`
- L96: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `94: `
- L176: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `174: `
- L358: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `356:     {C : ConformalCrossoverDatum V}`

## `InfoGeometry.OperatorAlgebra.ChiralPolarization`
- path: `lean/InfoGeometry/OperatorAlgebra/ChiralPolarization.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L247: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `245: `
- L315: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `313: variable {CA : CircularPolarization OpA}`
- L401: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `399: variable {CX : ModuleCircularPolarization X}`

## `InfoGeometry.OperatorAlgebra.ChiralProjectorFromInvolution`
- path: `lean/InfoGeometry/OperatorAlgebra/ChiralProjectorFromInvolution.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L46: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `44: `
- L236: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `234: `
- L237: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `235: variable {G Op : Type*} [Group G] [Ring Op] [Algebra ℝ Op]`

## `InfoGeometry.OperatorAlgebra.ChiralResidueAudit`
- path: `lean/InfoGeometry/OperatorAlgebra/ChiralResidueAudit.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L101: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `99: variable`
- L171: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `169: variable`
- L173: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `171: `
- L248: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `246: `
- L298: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `296: variable`

## `InfoGeometry.OperatorAlgebra.ChiralTubuleBoundary`
- path: `lean/InfoGeometry/OperatorAlgebra/ChiralTubuleBoundary.lean`
- findings: 8 (hard=0, soft=8, advisory=0)

- L93: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `91: `
- L140: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `138: `
- L181: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `179: `
- L409: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `407: `
- L443: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `441: `
- L485: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `483:     [NormedAddCommGroup Env] [NormedSpace ℝ Env]`
- L555: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `553:     {C : ModuleCircularPolarization H}`
- L614: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `612: `

## `InfoGeometry.OperatorAlgebra.CliffordAtomsZ2n`
- path: `lean/InfoGeometry/OperatorAlgebra/CliffordAtomsZ2n.lean`
- findings: 8 (hard=0, soft=8, advisory=0)

- L176: **SOFT** `skeletal-proof` in `theorem flip_ne`
  - proof appears to be tactic-automation-only or skeletal
  - `174: `
- L214: **SOFT** `skeletal-proof` in `theorem flipCharge_self`
  - proof appears to be tactic-automation-only or skeletal
  - `212: `
- L219: **SOFT** `skeletal-proof` in `theorem flipCharge_of_ne`
  - proof appears to be tactic-automation-only or skeletal
  - `217:     flipCharge i c i = !c i := by`
- L261: **SOFT** `skeletal-proof` in `theorem sectorSign_flip_of_ne`
  - proof appears to be tactic-automation-only or skeletal
  - `259:     sectorSign (flipCharge i eps) i = -sectorSign eps i := by`
- L49: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `47: `
- L132: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `130: `
- L468: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `466: `
- L513: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `511: `

## `InfoGeometry.OperatorAlgebra.ClosureInvolution`
- path: `lean/InfoGeometry/OperatorAlgebra/ClosureInvolution.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L431: **SOFT** `skeletal-proof` in `theorem antiProjection_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `429: `
- L495: **SOFT** `skeletal-proof` in `theorem fixedProjection_theta`
  - proof appears to be tactic-automation-only or skeletal
  - `493:     C.theta (C.antiProjection x) = -C.antiProjection x :=`
- L501: **SOFT** `skeletal-proof` in `theorem antiProjection_theta`
  - proof appears to be tactic-automation-only or skeletal
  - `499:     C.fixedProjection (C.theta x) = C.fixedProjection x := by`
- L45: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `43: variable`

## `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.Basic`
- path: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/Basic.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L44: **SOFT** `skeletal-proof` in `theorem apply_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `42: `
- L58: **SOFT** `skeletal-proof` in `theorem id_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `56: `
- L111: **SOFT** `skeletal-proof` in `theorem smul_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `109: `

## `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix`
- path: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/CblinfunMatrix.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L38: **SOFT** `skeletal-proof` in `theorem matrixOfOp_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `36: `
- L167: **SOFT** `skeletal-proof` in `theorem finiteKet_inner_eq_dotProduct`
  - proof appears to be tactic-automation-only or skeletal
  - `165:     matrixOp (M * N) = (matrixOp M).comp (matrixOp N) := by`

## `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ComplexVectorSpaces`
- path: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ComplexVectorSpaces.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L50: **SOFT** `skeletal-proof` in `theorem neg_one_smul`
  - proof appears to be tactic-automation-only or skeletal
  - `48: `
- L59: **SOFT** `skeletal-proof` in `theorem half_smul_double`
  - proof appears to be tactic-automation-only or skeletal
  - `57: `
- L78: **SOFT** `skeletal-proof` in `theorem mem_complex_span_singleton_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `76:     ‖restrictScalarsReal T‖ = ‖T‖ :=`

## `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraGeneral`
- path: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ExtraGeneral.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L77: **SOFT** `skeletal-proof` in `theorem complex_star_mul_self_eq_normSq`
  - proof appears to be tactic-automation-only or skeletal
  - `75:     exact hfg y hy`

## `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm`
- path: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ExtraJordanNormalForm.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L25: **SOFT** `skeletal-proof` in `theorem matrix_entry_explicit`
  - proof appears to be tactic-automation-only or skeletal
  - `23: `
- L70: **SOFT** `skeletal-proof` in `theorem list_map_add_vec`
  - proof appears to be tactic-automation-only or skeletal
  - `68:   have hij := congrFun (h (ketPi j)) i`

## `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraOrderedFields`
- path: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ExtraOrderedFields.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L60: **SOFT** `skeletal-proof` in `theorem divide_eq_eq_one_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `58: `
- L87: **SOFT** `skeletal-proof` in `theorem nonzero_abs_inverse`
  - proof appears to be tactic-automation-only or skeletal
  - `85:     x / z < y / w :=`
- L91: **SOFT** `skeletal-proof` in `theorem nonzero_abs_divide`
  - proof appears to be tactic-automation-only or skeletal
  - `89:     |a⁻¹| = (|a|)⁻¹ := by`

## `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix`
- path: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/FiniteMatrix.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L38: **SOFT** `skeletal-proof` in `theorem ketPi_apply_self`
  - proof appears to be tactic-automation-only or skeletal
  - `36: `
- L41: **SOFT** `skeletal-proof` in `theorem ketPi_apply_of_ne`
  - proof appears to be tactic-automation-only or skeletal
  - `39:     ketPi i i = 1 := by`
- L60: **SOFT** `skeletal-proof` in `theorem matrixOp_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `58: `
- L64: **SOFT** `skeletal-proof` in `theorem matrixOp_apply_ket`
  - proof appears to be tactic-automation-only or skeletal
  - `62:     matrixOp M v = M *ᵥ v :=`
- L102: **SOFT** `skeletal-proof` in `theorem conjTranspose_apply_entry`
  - proof appears to be tactic-automation-only or skeletal
  - `100: `
- L105: **SOFT** `skeletal-proof` in `theorem matrixOp_conjTranspose_apply_ket`
  - proof appears to be tactic-automation-only or skeletal
  - `103:     Mᴴ i j = star (M j i) :=`

## `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.InnerProduct`
- path: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/InnerProduct.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L23: **SOFT** `skeletal-proof` in `theorem cinner_commute`
  - proof appears to be tactic-automation-only or skeletal
  - `21: variable {E : Type*}`
- L45: **SOFT** `skeletal-proof` in `theorem cinner_diff_left`
  - proof appears to be tactic-automation-only or skeletal
  - `43:     ⟪x, c • y⟫_ℂ = c * ⟪x, y⟫_ℂ :=`
- L49: **SOFT** `skeletal-proof` in `theorem cinner_diff_right`
  - proof appears to be tactic-automation-only or skeletal
  - `47:     ⟪x - y, z⟫_ℂ = ⟪x, z⟫_ℂ - ⟪y, z⟫_ℂ := by`
- L64: **SOFT** `skeletal-proof` in `theorem cinner_smul_real_left`
  - proof appears to be tactic-automation-only or skeletal
  - `62:     Complex.im ⟪x, x⟫_ℂ = 0 :=`
- L68: **SOFT** `skeletal-proof` in `theorem cinner_smul_real_right`
  - proof appears to be tactic-automation-only or skeletal
  - `66:     ⟪r • x, y⟫_ℂ = (r : ℂ) * ⟪x, y⟫_ℂ := by`
- L138: **SOFT** `skeletal-proof` in `theorem sum_cinner`
  - proof appears to be tactic-automation-only or skeletal
  - `136:   rw [polar_identity, hxy]`

## `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.Ket`
- path: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/Ket.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L51: **SOFT** `skeletal-proof` in `theorem ket_apply_self`
  - proof appears to be tactic-automation-only or skeletal
  - `49: `

## `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.OrthogonalProjection`
- path: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/OrthogonalProjection.lean`
- findings: 8 (hard=0, soft=8, advisory=0)

- L85: **SOFT** `skeletal-proof` in `theorem projectionToSubmodule_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `83: `
- L88: **SOFT** `skeletal-proof` in `theorem projection_mem`
  - proof appears to be tactic-automation-only or skeletal
  - `86:     projectionToSubmodule K x = K.orthogonalProjection x :=`
- L92: **SOFT** `skeletal-proof` in `theorem projection_eq_self_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `90:     projection K x ∈ K := by`
- L96: **SOFT** `skeletal-proof` in `theorem projection_minimal`
  - proof appears to be tactic-automation-only or skeletal
  - `94:     projection K x = x ↔ x ∈ K := by`
- L101: **SOFT** `skeletal-proof` in `theorem projection_range`
  - proof appears to be tactic-automation-only or skeletal
  - `99:     ‖x - projection K x‖ = ⨅ y : K, ‖x - y‖ := by`
- L105: **SOFT** `skeletal-proof` in `theorem projection_ker`
  - proof appears to be tactic-automation-only or skeletal
  - `103:     (projection K).range = K := by`
- L109: **SOFT** `skeletal-proof` in `theorem projection_idempotent`
  - proof appears to be tactic-automation-only or skeletal
  - `107:     (projection K).ker = Kᗮ := by`
- L113: **SOFT** `skeletal-proof` in `theorem projection_norm_le`
  - proof appears to be tactic-automation-only or skeletal
  - `111:     IsIdempotentElem (projection K) := by`

## `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.RieszAdjoint`
- path: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RieszAdjoint.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L56: **SOFT** `skeletal-proof` in `theorem cadjoint_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `54: `
- L84: **SOFT** `skeletal-proof` in `theorem norm_cadjoint`
  - proof appears to be tactic-automation-only or skeletal
  - `82: `
- L87: **SOFT** `skeletal-proof` in `theorem cadjoint_eq_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `85:     ‖cadjoint T‖ = ‖T‖ := by`
- L91: **SOFT** `skeletal-proof` in `theorem star_eq_cadjoint`
  - proof appears to be tactic-automation-only or skeletal
  - `89:     S = cadjoint T ↔ ∀ x y, ⟪S x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by`
- L95: **SOFT** `skeletal-proof` in `theorem isSelfAdjoint_iff_cadjoint_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `93:     star T = cadjoint T := by`
- L99: **SOFT** `skeletal-proof` in `theorem isSelfAdjoint.cadjoint_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `97:     IsSelfAdjoint T ↔ cadjoint T = T := by`

## `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.RieszRepresentation`
- path: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RieszRepresentation.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L50: **SOFT** `skeletal-proof` in `theorem integral_realRieszMeasure`
  - proof appears to be tactic-automation-only or skeletal
  - `48: `
- L80: **SOFT** `skeletal-proof` in `theorem integralPositiveLinearMap_realRieszMeasure`
  - proof appears to be tactic-automation-only or skeletal
  - `78: `

## `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ScalarMultiplication`
- path: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ScalarMultiplication.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L50: **SOFT** `skeletal-proof` in `theorem leftMul_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `48: `
- L63: **SOFT** `skeletal-proof` in `theorem rightMul_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `61: `

## `InfoGeometry.OperatorAlgebra.CondensateSaturationAudit`
- path: `lean/InfoGeometry/OperatorAlgebra/CondensateSaturationAudit.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L45: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `43: `
- L102: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `100: `
- L160: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `158: `
- L188: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `186: `
- L222: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `220: `

## `InfoGeometry.OperatorAlgebra.ConformalCrossover`
- path: `lean/InfoGeometry/OperatorAlgebra/ConformalCrossover.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L111: **SOFT** `skeletal-proof` in `theorem sameRay_refl`
  - proof appears to be tactic-automation-only or skeletal
  - `109:     (P Q : ProjectiveNullRay C) : Prop :=`
- L198: **SOFT** `skeletal-proof` in `theorem crossover_generator`
  - proof appears to be tactic-automation-only or skeletal
  - `196: `
- L55: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `53: `
- L100: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `98: variable {V : Type*} [AddCommGroup V] [Module ℝ V]`
- L196: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `194: variable {V : Type*} [AddCommGroup V] [Module ℝ V]`

## `InfoGeometry.OperatorAlgebra.ConformalLedgerBridge`
- path: `lean/InfoGeometry/OperatorAlgebra/ConformalLedgerBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L118: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `116:     {D : StinespringTomitaDilation Sys Comm C}`
- L318: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `316:     {D : StinespringTomitaDilation Sys Comm C}`

## `InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative`
- path: `lean/InfoGeometry/OperatorAlgebra/ConnesSpatialDerivative.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L72: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `70: `
- L112: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `110: `
- L181: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `179: `
- L241: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `239: `
- L318: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `316: `

## `InfoGeometry.OperatorAlgebra.ConstructiveCasimir`
- path: `lean/InfoGeometry/OperatorAlgebra/ConstructiveCasimir.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L67: **SOFT** `skeletal-proof` in `theorem assocCommutator_zero_right`
  - proof appears to be tactic-automation-only or skeletal
  - `65: `
- L193: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `191: `

## `InfoGeometry.OperatorAlgebra.ConstructiveCayley`
- path: `lean/InfoGeometry/OperatorAlgebra/ConstructiveCayley.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L49: **SOFT** `skeletal-proof` in `theorem self`
  - proof appears to be tactic-automation-only or skeletal
  - `47:   change (T.comp K) x = (K.comp T) x`
- L81: **SOFT** `skeletal-proof` in `theorem sub`
  - proof appears to be tactic-automation-only or skeletal
  - `79:   rw [apply hT x]`
- L200: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `198:     {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]`

## `InfoGeometry.OperatorAlgebra.ConstructiveKasparovBoundary`
- path: `lean/InfoGeometry/OperatorAlgebra/ConstructiveKasparovBoundary.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L80: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `78: `
- L180: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `178: `
- L230: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `228:     [AddCommGroup Value] [Module ℝ Value]`
- L304: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `302:     [AddCommGroup Value] [Module ℝ Value]`

## `InfoGeometry.OperatorAlgebra.CosmicAndreevCrossover`
- path: `lean/InfoGeometry/OperatorAlgebra/CosmicAndreevCrossover.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L64: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `62: variable`

## `InfoGeometry.OperatorAlgebra.CrossoverResidue`
- path: `lean/InfoGeometry/OperatorAlgebra/CrossoverResidue.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L103: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `101:     {V : Type*} [AddCommGroup V] [Module ℝ V]`
- L167: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `165:     {V : Type*} [AddCommGroup V] [Module ℝ V]`
- L308: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `306:     {Orientation : NewState → Chirality}`
- L375: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `373: `
- L395: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `393:     {Smooth : NewState → Prop}`
- L398: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `396: variable`

## `InfoGeometry.OperatorAlgebra.DIIICosmicCrossoverBridge`
- path: `lean/InfoGeometry/OperatorAlgebra/DIIICosmicCrossoverBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L32: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `30: `

## `InfoGeometry.OperatorAlgebra.DIIISuperfluid`
- path: `lean/InfoGeometry/OperatorAlgebra/DIIISuperfluid.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L80: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `78: `

## `InfoGeometry.OperatorAlgebra.DIIISuperfluidBranch`
- path: `lean/InfoGeometry/OperatorAlgebra/DIIISuperfluidBranch.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L79: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `77: `
- L146: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `144: `

## `InfoGeometry.OperatorAlgebra.DrazinEntropyFunctional`
- path: `lean/InfoGeometry/OperatorAlgebra/DrazinEntropyFunctional.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L108: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `106: `
- L167: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `165: `
- L214: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `212: `
- L258: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `256: `
- L295: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `293: `

## `InfoGeometry.OperatorAlgebra.DrazinLaplacianLocalization`
- path: `lean/InfoGeometry/OperatorAlgebra/DrazinLaplacianLocalization.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L53: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `51: `
- L145: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `143: `

## `InfoGeometry.OperatorAlgebra.DrazinProjectionLocalization`
- path: `lean/InfoGeometry/OperatorAlgebra/DrazinProjectionLocalization.lean`
- findings: 9 (hard=0, soft=9, advisory=0)

- L33: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `31: `
- L54: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `52: `
- L94: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `92: `
- L154: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `152: variable {A : Type*} [Ring A]`
- L204: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `202: `
- L297: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `295: `
- L317: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `315: `
- L339: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `337: `
- L366: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `364: `

## `InfoGeometry.OperatorAlgebra.DrazinRepresentedSplit`
- path: `lean/InfoGeometry/OperatorAlgebra/DrazinRepresentedSplit.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L53: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `51: `
- L225: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `223: `
- L301: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `299: `

## `InfoGeometry.OperatorAlgebra.EntanglementGeometryLedger`
- path: `lean/InfoGeometry/OperatorAlgebra/EntanglementGeometryLedger.lean`
- findings: 8 (hard=0, soft=8, advisory=0)

- L412: **SOFT** `placeholder-naming` in `theorem bridge_growth_changes_of_complexity_growth`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `410: variable {C : ComplexityLedger State Time Quantity}`
- L63: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `61: `
- L124: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `122: variable {System : Type*}`
- L194: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `192: variable {System Geometry : Type*}`
- L250: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `248: `
- L314: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `312: variable {System : Type*}`
- L369: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `367: variable {State Time Quantity : Type*}`
- L411: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `409: variable {State Time Quantity : Type*}`

## `InfoGeometry.OperatorAlgebra.ErlangenNet`
- path: `lean/InfoGeometry/OperatorAlgebra/ErlangenNet.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L52: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `50: `
- L73: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `71: `
- L100: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `98: `
- L145: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `143: `
- L190: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `188: `
- L242: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `240: `

## `InfoGeometry.OperatorAlgebra.ExceptionalVirasoroBridge`
- path: `lean/InfoGeometry/OperatorAlgebra/ExceptionalVirasoroBridge.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L109: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `107:     {A : FiveGradeProjectedAccounting J L Obs G}`
- L207: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `205:     {H : HorizonKMSFiveGradeBridge J L Obs Memory A}`
- L333: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `331:     {G : FiveGrading L}`
- L482: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `480:     {H : HorizonKMSFiveGradeBridge J L Obs Memory A}`
- L572: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `570:     {A : FiveGradeProjectedAccounting J L Obs G}`

## `InfoGeometry.OperatorAlgebra.FierzNoetherBridge`
- path: `lean/InfoGeometry/OperatorAlgebra/FierzNoetherBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L57: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `55: `

## `InfoGeometry.OperatorAlgebra.FiniteJonesOptics`
- path: `lean/InfoGeometry/OperatorAlgebra/FiniteJonesOptics.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L114: **SOFT** `skeletal-proof` in `theorem det2_diagJones`
  - proof appears to be tactic-automation-only or skeletal
  - `112: def det2 (M : JonesMat) : ℂ :=`

## `InfoGeometry.OperatorAlgebra.FiveGradeClosureSymmetry`
- path: `lean/InfoGeometry/OperatorAlgebra/FiveGradeClosureSymmetry.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L62: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `60: variable`

## `InfoGeometry.OperatorAlgebra.FiveGradedDefectAbsorption`
- path: `lean/InfoGeometry/OperatorAlgebra/FiveGradedDefectAbsorption.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L121: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `119:     {G : FiveGrading L}`
- L172: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `170:     {R : TKKRicciFluxDatum L State Geometry}`
- L253: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `251:     {Visible Hidden Memory : Type*}`
- L295: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `293: `
- L372: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `370: `

## `InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger`
- path: `lean/InfoGeometry/OperatorAlgebra/FiveGradedInformationLedger.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L78: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `76: `
- L180: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `178:     [AddCommGroup Obs] [Module ℝ Obs]`
- L314: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `312:     {G : FiveGrading L}`
- L392: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `390: `
- L479: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `477:     [AddCommGroup Center] [Module ℝ Center]`

## `InfoGeometry.OperatorAlgebra.FresnelJonesReflection`
- path: `lean/InfoGeometry/OperatorAlgebra/FresnelJonesReflection.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L155: **SOFT** `skeletal-proof` in `theorem fresnelRP_eq_zero_of_num_zero`
  - proof appears to be tactic-automation-only or skeletal
  - `153:   (n₂ * Real.cos θᵢ - n₁ * Real.cos θₜ) /`
- L228: **SOFT** `skeletal-proof` in `theorem circularReflection_brewster_apply_left`
  - proof appears to be tactic-automation-only or skeletal
  - `226:   ext C i`
- L236: **SOFT** `skeletal-proof` in `theorem circularReflection_brewster_apply_right`
  - proof appears to be tactic-automation-only or skeletal
  - `234:       (r_s / 2) * (C 0 + C 1) := by`

## `InfoGeometry.OperatorAlgebra.HelicalDivisorStinespring`
- path: `lean/InfoGeometry/OperatorAlgebra/HelicalDivisorStinespring.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L209: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `207: `
- L267: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `265:     [AddCommGroup Joint] [Module ℝ Joint]`
- L323: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `321: `

## `InfoGeometry.OperatorAlgebra.HelicalTimeStinespring`
- path: `lean/InfoGeometry/OperatorAlgebra/HelicalTimeStinespring.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L52: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `50: `
- L101: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `99: `
- L144: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `142:     {H : HelicalTimeDatum State}`
- L215: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `213:     {C : DissipativeChannel Sys}`
- L267: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `265: `

## `InfoGeometry.OperatorAlgebra.HorizonAttractorMicrostateLedger`
- path: `lean/InfoGeometry/OperatorAlgebra/HorizonAttractorMicrostateLedger.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L87: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `85: variable`
- L130: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `128:     {State Charge Scalar Memory : Type*}`
- L169: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `167: variable`

## `InfoGeometry.OperatorAlgebra.HorizonEschaton`
- path: `lean/InfoGeometry/OperatorAlgebra/HorizonEschaton.lean`
- findings: 10 (hard=0, soft=10, advisory=0)

- L86: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `84: `
- L112: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `110: `
- L152: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `150: `
- L190: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `188: variable {Event Obs Memory : Type*}`
- L253: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `251: variable {Event Obs Memory : Type*}`
- L336: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `334: `
- L406: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `404: variable {Event Obs Memory : Type*}`
- L505: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `503: `
- L553: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `551: `
- L625: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `623: `

## `InfoGeometry.OperatorAlgebra.HorizonKMS`
- path: `lean/InfoGeometry/OperatorAlgebra/HorizonKMS.lean`
- findings: 9 (hard=0, soft=9, advisory=0)

- L84: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `82: variable`
- L133: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `131: variable`
- L221: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `219: `
- L387: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `385:     {A : FiveGradeProjectedAccounting J L Obs G}`
- L476: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `474:     {G : FiveGrading L}`
- L672: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `670:     {A : FiveGradeProjectedAccounting J L Obs G}`
- L771: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `769:     {A : FiveGradeProjectedAccounting J L Obs G}`
- L865: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `863:     {G : FiveGrading L}`
- L1088: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1086:     {A : FiveGradeProjectedAccounting J L Obs G}`

## `InfoGeometry.OperatorAlgebra.IndividuatedBoundedTransform`
- path: `lean/InfoGeometry/OperatorAlgebra/IndividuatedBoundedTransform.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L151: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `149: `

## `InfoGeometry.OperatorAlgebra.IndividuatedCasimir`
- path: `lean/InfoGeometry/OperatorAlgebra/IndividuatedCasimir.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L87: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `85: `
- L173: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `171:     [Fintype ι] [DecidableEq ι]`

## `InfoGeometry.OperatorAlgebra.IndividuatedCayley`
- path: `lean/InfoGeometry/OperatorAlgebra/IndividuatedCayley.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L44: **SOFT** `skeletal-proof` in `theorem self`
  - proof appears to be tactic-automation-only or skeletal
  - `42: `
- L164: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `162:     PhaseLinear K (D + K) :=`
- L345: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `343:   ]`
- L485: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `483: `

## `InfoGeometry.OperatorAlgebra.IndividuatedCl44Casimir`
- path: `lean/InfoGeometry/OperatorAlgebra/IndividuatedCl44Casimir.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L123: **SOFT** `skeletal-proof` in `theorem diracSouriauCasimir_eq_trace_identity`
  - proof appears to be tactic-automation-only or skeletal
  - `121:     dsimp [DiracSouriauCoreTrace.constructCasimirElement]`
- L72: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `70: `
- L156: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `154: `

## `InfoGeometry.OperatorAlgebra.JUnitaryTopologicalCharge`
- path: `lean/InfoGeometry/OperatorAlgebra/JUnitaryTopologicalCharge.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L372: **SOFT** `skeletal-proof` in `theorem topologicalCharge_eq_one_of_det_eq_one`
  - proof appears to be tactic-automation-only or skeletal
  - `370:     (U : JUnitaryUnit Adj J) : Z2Charge :=`
- L380: **SOFT** `skeletal-proof` in `theorem topologicalCharge_eq_neg_one_of_det_eq_neg_one`
  - proof appears to be tactic-automation-only or skeletal
  - `378:     topologicalCharge Det U = 1 := by`
- L81: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `79: variable {Op : Type*} [Monoid Op]`
- L530: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `528:     {Adj : AdjointDatum Op}`

## `InfoGeometry.OperatorAlgebra.JonesCalibration`
- path: `lean/InfoGeometry/OperatorAlgebra/JonesCalibration.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L192: **SOFT** `skeletal-proof` in `theorem jones_apply_offdiag_one_zero`
  - proof appears to be tactic-automation-only or skeletal
  - `190: `

## `InfoGeometry.OperatorAlgebra.KapustinWittenDualitySocket`
- path: `lean/InfoGeometry/OperatorAlgebra/KapustinWittenDualitySocket.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L113: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `111: variable`

## `InfoGeometry.OperatorAlgebra.KleinianReturn`
- path: `lean/InfoGeometry/OperatorAlgebra/KleinianReturn.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L44: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `42:     {Op : Type*} [Ring Op]`

## `InfoGeometry.OperatorAlgebra.KleinianTwist`
- path: `lean/InfoGeometry/OperatorAlgebra/KleinianTwist.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L71: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `69:     {T : TomitaCommutantDatum Op}`
- L130: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `128:     {T : TomitaCommutantDatum Op}`

## `InfoGeometry.OperatorAlgebra.KreinIsotropicCone`
- path: `lean/InfoGeometry/OperatorAlgebra/KreinIsotropicCone.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L41: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `39: `
- L174: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `172: `
- L198: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `196: `
- L250: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `248: `

## `InfoGeometry.OperatorAlgebra.LightConeAffineCurrentBridge`
- path: `lean/InfoGeometry/OperatorAlgebra/LightConeAffineCurrentBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L65: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `63:     [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]`

## `InfoGeometry.OperatorAlgebra.MobiusClosure`
- path: `lean/InfoGeometry/OperatorAlgebra/MobiusClosure.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L48: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `46: variable`

## `InfoGeometry.OperatorAlgebra.MobiusClosureFixedPoints`
- path: `lean/InfoGeometry/OperatorAlgebra/MobiusClosureFixedPoints.lean`
- findings: 8 (hard=0, soft=8, advisory=0)

- L44: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `42: `
- L90: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `88: variable`
- L172: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `170: `
- L242: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `240: variable {Op : Type*}`
- L306: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `304: `
- L396: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `394: variable {L : Type*}`
- L471: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `469: variable {X Charge : Type*}`
- L519: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `517: `

## `InfoGeometry.OperatorAlgebra.ModularChiralMirror`
- path: `lean/InfoGeometry/OperatorAlgebra/ModularChiralMirror.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L115: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `113: `
- L342: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `340: variable`
- L503: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `501: variable`
- L761: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `759: `

## `InfoGeometry.OperatorAlgebra.ModularMirrorBoundary`
- path: `lean/InfoGeometry/OperatorAlgebra/ModularMirrorBoundary.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L68: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `66: variable`
- L213: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `211:     [AddCommGroup V] [Module ℝ V]`
- L265: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `263: variable`
- L317: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `315:     {V : Type*} [AddCommGroup V] [Module ℝ V]`
- L358: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `356: variable`

## `InfoGeometry.OperatorAlgebra.ModularSignCPT`
- path: `lean/InfoGeometry/OperatorAlgebra/ModularSignCPT.lean`
- findings: 13 (hard=0, soft=13, advisory=0)

- L74: **SOFT** `skeletal-proof` in `theorem Kmod_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `72: def Kmod : EndR H :=`
- L200: **SOFT** `skeletal-proof` in `theorem Kmod_square_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `198:     M.Kmod = M.J.comp M.eps :=`
- L213: **SOFT** `skeletal-proof` in `theorem complexStructure_square`
  - proof appears to be tactic-automation-only or skeletal
  - `211:     M.Kmod.comp M.Kmod = -(1 : EndR H) := by`
- L323: **SOFT** `skeletal-proof` in `theorem Kmod_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `321: def Kmod : EndR H :=`
- L504: **SOFT** `skeletal-proof` in `theorem Kmod_square_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `502:     M.Kmod = M.J.comp M.eps :=`
- L516: **SOFT** `skeletal-proof` in `theorem partialComplexStructure_square`
  - proof appears to be tactic-automation-only or skeletal
  - `514:     M.Kmod.comp M.Kmod = -M.support := by`
- L68: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `66: variable`
- L155: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `153: variable`
- L175: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `173: variable`
- L311: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `309: variable`
- L460: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `458: variable`
- L488: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `486: variable`
- L607: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `605: variable`

## `InfoGeometry.OperatorAlgebra.ModularWeightTrace`
- path: `lean/InfoGeometry/OperatorAlgebra/ModularWeightTrace.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L117: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `115: `
- L130: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `128: `
- L175: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `173: `
- L216: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `214: `
- L251: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `249: `
- L316: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `314: `

## `InfoGeometry.OperatorAlgebra.MoorePenroseDivisionRank`
- path: `lean/InfoGeometry/OperatorAlgebra/MoorePenroseDivisionRank.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L51: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `49: `
- L106: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `104: `
- L147: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `145: `
- L200: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `198: `
- L242: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `240: `

## `InfoGeometry.OperatorAlgebra.NoetherModularFlow`
- path: `lean/InfoGeometry/OperatorAlgebra/NoetherModularFlow.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L35: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `33: `
- L72: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `70: `
- L107: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `105: `
- L161: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `159: `
- L223: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `221: `

## `InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift`
- path: `lean/InfoGeometry/OperatorAlgebra/NoncommutativeBogoliubovKANLift.lean`
- findings: 8 (hard=0, soft=8, advisory=0)

- L101: **SOFT** `skeletal-proof` in `theorem connesCocycle_same_weight`
  - proof appears to be tactic-automation-only or skeletal
  - `99: `
- L142: **SOFT** `skeletal-proof` in `theorem typeIII_baseIntegral_eq_modularWeight_integral`
  - proof appears to be tactic-automation-only or skeletal
  - `140:     ∃ a b : A, a * b ≠ b * a :=`
- L152: **SOFT** `skeletal-proof` in `theorem typeIII_coreTraceOfBase_eq_coreTrace_traceOfEmbedded`
  - proof appears to be tactic-automation-only or skeletal
  - `150:       P.typeIIIIntegration.modularWeight.integral x :=`
- L345: **SOFT** `skeletal-proof` in `theorem diagonal_shadow_available`
  - proof appears to be tactic-automation-only or skeletal
  - `343:     NoncommutativeModularToBogoliubovKANPacket.modularCore P = P.modularCore := by`
- L361: **SOFT** `placeholder-naming` in `theorem bridge_typeIII_baseIntegral_eq_modularWeight_integral`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `359:     ∃ a b : A, a * b ≠ b * a :=`
- L368: **SOFT** `placeholder-naming` in `theorem bridge_typeIII_coreTraceOfBase_eq_coreTrace_traceOfEmbedded`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `366:       P.modularCore.typeIIIIntegration.modularWeight.integral x :=`
- L89: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `87: variable {A Weight Deriv Ham Phase Core : Type*}`
- L219: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `217:   [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]`

## `InfoGeometry.OperatorAlgebra.O44PinCPTReflectionBridge`
- path: `lean/InfoGeometry/OperatorAlgebra/O44PinCPTReflectionBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L93: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `91:     {Q : SplitQuadratic44 V}`

## `InfoGeometry.OperatorAlgebra.O44PinMobiusProjective`
- path: `lean/InfoGeometry/OperatorAlgebra/O44PinMobiusProjective.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L626: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `624:     [AddCommGroup V] [Module ℝ V]`
- L785: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `783:     [AddCommGroup W] [Module ℝ W]`
- L826: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `824:     [AddCommGroup W] [Module ℝ W]`

## `InfoGeometry.OperatorAlgebra.OperatorChiralLightcone`
- path: `lean/InfoGeometry/OperatorAlgebra/OperatorChiralLightcone.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L50: **SOFT** `skeletal-proof` in `theorem opposite_right`
  - proof appears to be tactic-automation-only or skeletal
  - `48: `
- L170: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `168: `
- L311: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `309: variable {Q : KreinIsotropicCone.KreinQuadraticDatum H}`
- L396: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `394:     {Q : KreinIsotropicCone.KreinQuadraticDatum H}`

## `InfoGeometry.OperatorAlgebra.OperatorErlangenLegendre`
- path: `lean/InfoGeometry/OperatorAlgebra/OperatorErlangenLegendre.lean`
- findings: 8 (hard=0, soft=8, advisory=0)

- L135: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `133:     [Ring Obs]`
- L268: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `266: `
- L76: **SOFT** `witness-field-projection` in `structure-field modularDerivation_valid`
  - witness field `modularDerivation_valid : modularDerivation_law`
  - `74:   modularDerivation_law :`
- L92: **SOFT** `witness-field-projection` in `structure-field stabilizer_valid`
  - witness field `stabilizer_valid : stabilizer_law`
  - `90:   stabilizer_law :`
- L108: **SOFT** `witness-field-projection` in `structure-field exponentialLegendre_valid`
  - witness field `exponentialLegendre_valid : exponentialLegendre_law`
  - `106:   exponentialLegendre_law :`
- L235: **SOFT** `witness-field-projection` in `structure-field selfAdjoint_valid`
  - witness field `selfAdjoint_valid : selfAdjointWitness`
  - `233:   selfAdjointWitness :`
- L243: **SOFT** `witness-field-projection` in `structure-field determinant_valid`
  - witness field `determinant_valid : determinantWitness`
  - `241:   determinantWitness :`
- L262: **SOFT** `witness-field-projection` in `structure-field functionalEquation_valid`
  - witness field `functionalEquation_valid : functionalEquationSymmetry`
  - `260:   functionalEquationSymmetry :`

## `InfoGeometry.OperatorAlgebra.OperatorThermodynamics`
- path: `lean/InfoGeometry/OperatorAlgebra/OperatorThermodynamics.lean`
- findings: 22 (hard=0, soft=22, advisory=0)

- L1043: **SOFT** `skeletal-proof` in `theorem toKMSState_eval`
  - proof appears to be tactic-automation-only or skeletal
  - `1041: `
- L72: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `70: `
- L128: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `126: variable {σ : OperatorFlow Op}`
- L172: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `170: `
- L261: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `259: variable {Op : Type*} [Ring Op]`
- L314: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `312: variable {σ : OperatorFlow Op}`
- L406: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `404: variable {σ : OperatorFlow Op}`
- L510: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `508: `
- L613: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `611: variable {Op : Type*} [Ring Op]`
- L657: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `655: variable {Op : Type*} [Ring Op]`
- L824: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `822: `
- L865: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `863: `
- L958: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `956: `
- L1033: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1031: `
- L1085: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1083: `
- L1140: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1138: variable {Op : Type*} [Ring Op]`
- L1195: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1193: variable {σ : ModularFlow Op}`
- L1290: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1288: variable {σ : ModularFlow Op}`
- L1352: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1350: `
- L1415: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1413: `
- L252: **SOFT** `witness-field-projection` in `structure-field reduction_backend_valid`
  - witness field `reduction_backend_valid : reduction_backend_law`
  - `250: `
- L1131: **SOFT** `witness-field-projection` in `structure-field reduction_backend_valid`
  - witness field `reduction_backend_valid : reduction_backend_law`
  - `1129: `

## `InfoGeometry.OperatorAlgebra.PO55ConformalClosure`
- path: `lean/InfoGeometry/OperatorAlgebra/PO55ConformalClosure.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L138: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `136: `
- L191: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `189:     {W : Type*} [AddCommGroup W] [Module ℝ W]`
- L235: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `233:     {Q : SplitQuadratic55 W}`
- L664: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `662:     [AddCommGroup W] [Module ℝ W]`

## `InfoGeometry.OperatorAlgebra.PoincareAndreev`
- path: `lean/InfoGeometry/OperatorAlgebra/PoincareAndreev.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L71: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `69: variable`

## `InfoGeometry.OperatorAlgebra.ProjectiveJonesGeometry`
- path: `lean/InfoGeometry/OperatorAlgebra/ProjectiveJonesGeometry.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L36: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `34: `
- L116: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `114: variable {Op : Type*} [Ring Op] [Module ℝ Op]`

## `InfoGeometry.OperatorAlgebra.RenormalizedTrace`
- path: `lean/InfoGeometry/OperatorAlgebra/RenormalizedTrace.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L64: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `62: `
- L129: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `127: `

## `InfoGeometry.OperatorAlgebra.SelfDualChiralConeBoundary`
- path: `lean/InfoGeometry/OperatorAlgebra/SelfDualChiralConeBoundary.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L87: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `85: variable`

## `InfoGeometry.OperatorAlgebra.SpectralGeneratorProxy`
- path: `lean/InfoGeometry/OperatorAlgebra/SpectralGeneratorProxy.lean`
- findings: 7 (hard=0, soft=7, advisory=0)

- L60: **SOFT** `skeletal-proof` in `theorem self`
  - proof appears to be tactic-automation-only or skeletal
  - `58:   have h := congrArg (fun A : EndR H => A x) hT`
- L92: **SOFT** `skeletal-proof` in `theorem sub`
  - proof appears to be tactic-automation-only or skeletal
  - `90:   rw [apply hT x]`
- L164: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `162: variable`
- L242: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `240: variable`
- L285: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `283:     [Ring A] [Module ℝ A]`
- L359: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `357: variable`
- L441: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `439:     [Ring A] [Module ℝ A]`

## `InfoGeometry.OperatorAlgebra.SpinBogoliubovFrame`
- path: `lean/InfoGeometry/OperatorAlgebra/SpinBogoliubovFrame.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L131: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `129:     [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]`
- L229: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `227:     [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]`
- L313: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `311:     [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]`

## `InfoGeometry.OperatorAlgebra.SpinBogoliubovStinespring`
- path: `lean/InfoGeometry/OperatorAlgebra/SpinBogoliubovStinespring.lean`
- findings: 18 (hard=0, soft=18, advisory=0)

- L55: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `53: `
- L89: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `87: `
- L126: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `124: `
- L295: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `293: `
- L362: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `360: variable {Base Frame Mode State : Type*} [AddCommGroup State] [Module ℝ State]`
- L418: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `416: variable {Base Frame Mode State : Type*} [AddCommGroup State] [Module ℝ State]`
- L467: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `465: variable [AddCommGroup Joint] [Module ℝ Joint]`
- L538: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `536: `
- L592: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `590: variable {C : SpinFrameBogoliubovCalibration Base Frame Mode State}`
- L645: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `643: `
- L685: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `683: `
- L742: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `740: `
- L805: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `803: variable [AddCommGroup GlobalOp] [Module ℝ GlobalOp]`
- L850: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `848: variable [AddCommGroup GlobalOp] [Module ℝ GlobalOp]`
- L851: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `849: variable {Φ : LocalChannel Op}`
- L919: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `917: variable [AddCommGroup GlobalOp] [Module ℝ GlobalOp]`
- L975: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `973: variable [AddCommGroup GlobalOp] [Module ℝ GlobalOp]`
- L1030: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1028: `

## `InfoGeometry.OperatorAlgebra.SpinUnruhCalibration`
- path: `lean/InfoGeometry/OperatorAlgebra/SpinUnruhCalibration.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L64: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `62: `
- L115: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `113: `
- L180: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `178: `
- L251: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `249: variable {σ : OperatorFlow Op}`

## `InfoGeometry.OperatorAlgebra.SplitCliffordRealForms`
- path: `lean/InfoGeometry/OperatorAlgebra/SplitCliffordRealForms.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L342: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `340: `

## `InfoGeometry.OperatorAlgebra.SplitCliffordZ2Four`
- path: `lean/InfoGeometry/OperatorAlgebra/SplitCliffordZ2Four.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L74: **SOFT** `skeletal-proof` in `theorem chargeSign_flip_ne`
  - proof appears to be tactic-automation-only or skeletal
  - `72:     chargeSign (flipBit i q) i = -chargeSign q i := by`
- L207: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `205: `

## `InfoGeometry.OperatorAlgebra.StinespringDilation`
- path: `lean/InfoGeometry/OperatorAlgebra/StinespringDilation.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L139: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `137:     [AddCommGroup Joint] [Module ℝ Joint]`
- L382: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `380:     [AddCommGroup Env] [Module ℝ Env]`
- L796: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `794:     [NormedAddCommGroup Dilated] [NormedSpace ℝ Dilated]`
- L858: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `856: `
- L907: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `905: `

## `InfoGeometry.OperatorAlgebra.StinespringTomitaLightcone`
- path: `lean/InfoGeometry/OperatorAlgebra/StinespringTomitaLightcone.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L58: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `56: `
- L154: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `152:     [Ring GlobalOp] [Module ℝ GlobalOp]`
- L249: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `247:     {C : ModuleCircularPolarization H}`
- L329: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `327:     {C : ModuleCircularPolarization H}`

## `InfoGeometry.OperatorAlgebra.SugawaraAffineBridge`
- path: `lean/InfoGeometry/OperatorAlgebra/SugawaraAffineBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L25: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `23: variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]`
- L26: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `24: variable (𝓰 : Type*) [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]`

## `InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure`
- path: `lean/InfoGeometry/OperatorAlgebra/SuperTKKConformalClosure.lean`
- findings: 8 (hard=0, soft=8, advisory=0)

- L111: **SOFT** `skeletal-proof` in `theorem recompose_coordinates`
  - proof appears to be tactic-automation-only or skeletal
  - `109:     ((((G.gNegTwo × G.gNegOne) × G.gZero) × G.gPosOne) × G.gPosTwo) :=`
- L117: **SOFT** `skeletal-proof` in `theorem coordinates_recompose`
  - proof appears to be tactic-automation-only or skeletal
  - `115:     G.decomposition.symm (G.coordinates X) = X := by`
- L572: **SOFT** `skeletal-proof` in `theorem energy_nonneg`
  - proof appears to be tactic-automation-only or skeletal
  - `570:     (s : State) : Prop :=`
- L104: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `102: `
- L292: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `290:     [AddCommGroup Odd] [Module ℝ Odd]`
- L425: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `423:     [AddCommGroup Geometry] [Module ℝ Geometry]`
- L566: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `564: `
- L653: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `651:     {A : SuperTKKDefectAbsorption L Odd State Geometry R}`

## `InfoGeometry.OperatorAlgebra.SuperVirasoroExtension`
- path: `lean/InfoGeometry/OperatorAlgebra/SuperVirasoroExtension.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L57: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `55: variable`
- L159: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `157:     [AddCommGroup State] [Module ℝ State]`

## `InfoGeometry.OperatorAlgebra.SusceptibilityHessian`
- path: `lean/InfoGeometry/OperatorAlgebra/SusceptibilityHessian.lean`
- findings: 20 (hard=0, soft=20, advisory=0)

- L1631: **SOFT** `skeletal-proof` in `theorem event_coeff0_eq_fresnel_s`
  - proof appears to be tactic-automation-only or skeletal
  - `1629:   coherence_law := C.coherence_law s omega theta`
- L1643: **SOFT** `skeletal-proof` in `theorem event_coeff1_eq_fresnel_p`
  - proof appears to be tactic-automation-only or skeletal
  - `1641:       C.response.fresnel.coeff_s s omega theta :=`
- L54: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `52: `
- L110: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `108: `
- L148: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `146: variable {H : HessianResponseDatum State}`
- L189: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `187: `
- L231: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `229: `
- L388: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `386: variable {M : MaterialResponseModel State}`
- L465: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `463: `
- L576: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `574: variable {M : MaterialResponseModel State}`
- L763: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `761: `
- L803: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `801: `
- L971: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `969: `
- L1029: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1027: `
- L1185: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1183:     {C : DissipativeChannel Sys}`
- L1250: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1248:     {C : DissipativeChannel Sys}`
- L1357: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1355: `
- L1553: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1551:     {State Tangent Freq Angle : Type*}`
- L1614: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1612:     {State Tangent Freq Angle : Type*}`
- L1725: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1723:     {State Tangent Freq Angle : Type*}`

## `InfoGeometry.OperatorAlgebra.SymmetryInvariants`
- path: `lean/InfoGeometry/OperatorAlgebra/SymmetryInvariants.lean`
- findings: 18 (hard=0, soft=18, advisory=0)

- L104: **SOFT** `skeletal-proof` in `theorem act_mul_op`
  - proof appears to be tactic-automation-only or skeletal
  - `102: `
- L151: **SOFT** `skeletal-proof` in `theorem zero`
  - proof appears to be tactic-automation-only or skeletal
  - `149: variable {G Op : Type*} [Group G] [Ring Op]`
- L157: **SOFT** `skeletal-proof` in `theorem one`
  - proof appears to be tactic-automation-only or skeletal
  - `155:   intro g`
- L163: **SOFT** `skeletal-proof` in `theorem add`
  - proof appears to be tactic-automation-only or skeletal
  - `161:   intro g`
- L172: **SOFT** `skeletal-proof` in `theorem neg`
  - proof appears to be tactic-automation-only or skeletal
  - `170:   intro g`
- L180: **SOFT** `skeletal-proof` in `theorem sub`
  - proof appears to be tactic-automation-only or skeletal
  - `178:   intro g`
- L267: **SOFT** `skeletal-proof` in `theorem one_isProjector`
  - proof appears to be tactic-automation-only or skeletal
  - `265: variable {G Op : Type*} [Group G] [Ring Op]`
- L271: **SOFT** `skeletal-proof` in `theorem zero_isProjector`
  - proof appears to be tactic-automation-only or skeletal
  - `269:     IsProjector (1 : Op) := by`
- L760: **SOFT** `skeletal-proof` in `theorem act_map_zero`
  - proof appears to be tactic-automation-only or skeletal
  - `758: `
- L896: **SOFT** `skeletal-proof` in `theorem commutator_self`
  - proof appears to be tactic-automation-only or skeletal
  - `894: omit [Module ℝ Op] in`
- L55: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `53: `
- L150: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `148: `
- L266: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `264: `
- L744: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `742:     {G : Type uG} {Op : Type uOp}`
- L948: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `946: variable`
- L1024: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1022:     [Ring Op₂] [Module ℝ Op₂]`
- L1064: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1062:     [Ring Op₂] [Module ℝ Op₂]`
- L1339: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1337: `

## `InfoGeometry.OperatorAlgebra.TKKConformalClosure`
- path: `lean/InfoGeometry/OperatorAlgebra/TKKConformalClosure.lean`
- findings: 12 (hard=0, soft=12, advisory=0)

- L78: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `76:     {V W : Type*} [AddCommGroup V] [Module ℝ V]`
- L146: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `144: `
- L249: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `247:     {J L : Type*} [AddCommGroup J] [Module ℝ J]`
- L308: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `306:     [LieRing L] [LieAlgebra ℝ L]`
- L349: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `347:     [LieRing L] [LieAlgebra ℝ L]`
- L436: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `434:     [LieRing L] [LieAlgebra ℝ L]`
- L496: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `494:     (s : State) : Prop :=`
- L528: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `526:     {State Geometry : Type*} [AddCommGroup State] [Module ℝ State]`
- L565: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `563:     [AddCommGroup State] [Module ℝ State]`
- L619: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `617:     [AddCommGroup State] [Module ℝ State]`
- L744: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `742:     [AddCommGroup State] [Module ℝ State]`
- L814: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `812:     [AddCommGroup State] [Module ℝ State]`

## `InfoGeometry.OperatorAlgebra.TomitaCartanChiralClosure`
- path: `lean/InfoGeometry/OperatorAlgebra/TomitaCartanChiralClosure.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L62: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `60:     {Op : Type uOp} [Ring Op] [Algebra ℝ Op]`

## `InfoGeometry.OperatorAlgebra.TomitaCartanDynamics`
- path: `lean/InfoGeometry/OperatorAlgebra/TomitaCartanDynamics.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L128: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `126:     {Op : Type uOp} [Ring Op] [SMul ℝ Op]`
- L220: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `218:     {T : TomitaCommutantDatum Op}`
- L293: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `291:     {Op : Type uOp} [Ring Op] [SMul ℝ Op]`

## `InfoGeometry.OperatorAlgebra.TomitaCartanSplit`
- path: `lean/InfoGeometry/OperatorAlgebra/TomitaCartanSplit.lean`
- findings: 22 (hard=0, soft=22, advisory=0)

- L65: **SOFT** `skeletal-proof` in `theorem map_sub`
  - proof appears to be tactic-automation-only or skeletal
  - `63: variable {Op : Type uOp} [Ring Op]`
- L286: **SOFT** `skeletal-proof` in `theorem zero_mem_isotropicCone`
  - proof appears to be tactic-automation-only or skeletal
  - `284: `
- L664: **SOFT** `skeletal-proof` in `theorem globalFrom_noncompact`
  - proof appears to be tactic-automation-only or skeletal
  - `662: `
- L776: **SOFT** `skeletal-proof` in `theorem mirrorCombination_noncompact`
  - proof appears to be tactic-automation-only or skeletal
  - `774: `
- L909: **SOFT** `skeletal-proof` in `theorem diagonal_isotropic`
  - proof appears to be tactic-automation-only or skeletal
  - `907:     (u : X × X) : ℝ :=`
- L1028: **SOFT** `skeletal-proof` in `theorem diagonal_isotropic`
  - proof appears to be tactic-automation-only or skeletal
  - `1026:     (x y : Doubled H) : ℝ :=`
- L1040: **SOFT** `skeletal-proof` in `theorem antidiagonal_isotropic`
  - proof appears to be tactic-automation-only or skeletal
  - `1038:     doubledKreinForm (v, v) (v, v) = 0 := by`
- L1118: **SOFT** `skeletal-proof` in `theorem globalGenerator_compact`
  - proof appears to be tactic-automation-only or skeletal
  - `1116:     (X : Gen) : EndR H :=`
- L1128: **SOFT** `skeletal-proof` in `theorem globalGenerator_noncompact`
  - proof appears to be tactic-automation-only or skeletal
  - `1126:     globalGenerator D X = D.localGen X + D.mirror X := by`
- L64: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `62: `
- L123: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `121: `
- L163: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `161: `
- L251: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `249: `
- L252: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `250: variable {Op : Type uOp} [Ring Op]`
- L459: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `457: `
- L517: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `515: `
- L566: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `564: `
- L738: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `736:     {Op : Type uOp} [AddCommGroup Op] [Module ℝ Op]`
- L898: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `896: variable`
- L1259: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1257: `
- L1316: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1314: variable [Ring Op]`
- L1508: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `1506: `

## `InfoGeometry.OperatorAlgebra.TopologicalSnap`
- path: `lean/InfoGeometry/OperatorAlgebra/TopologicalSnap.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L50: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `48: `

## `InfoGeometry.OperatorAlgebra.TopologicalSuperconductorEdge`
- path: `lean/InfoGeometry/OperatorAlgebra/TopologicalSuperconductorEdge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L92: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `90:     {Boundary V : Type*}`

## `InfoGeometry.OperatorAlgebra.TraceFreeSuperIntegration`
- path: `lean/InfoGeometry/OperatorAlgebra/TraceFreeSuperIntegration.lean`
- findings: 9 (hard=0, soft=9, advisory=0)

- L78: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `76: `
- L142: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `140: `
- L196: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `194: `
- L235: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `233: `
- L282: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `280: `
- L326: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `324: `
- L361: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `359: `
- L392: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `390: `
- L448: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `446: `

## `InfoGeometry.OperatorAlgebra.UnnormalizedRelativeEntropy`
- path: `lean/InfoGeometry/OperatorAlgebra/UnnormalizedRelativeEntropy.lean`
- findings: 7 (hard=0, soft=7, advisory=0)

- L71: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `69: `
- L158: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `156: `
- L228: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `226: `
- L303: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `301: `
- L370: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `368: `
- L423: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `421: `
- L479: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `477: `

## `InfoGeometry.OperatorAlgebra.VerifiedDeterminant`
- path: `lean/InfoGeometry/OperatorAlgebra/VerifiedDeterminant.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L90: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `88: `

## `InfoGeometry.OperatorAlgebra.VerifiedTrace`
- path: `lean/InfoGeometry/OperatorAlgebra/VerifiedTrace.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L88: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `86: `

## `InfoGeometry.OperatorAlgebra.VirasoroProjectPin`
- path: `lean/InfoGeometry/OperatorAlgebra/VirasoroProjectPin.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L69: **SOFT** `vacuous-prop-constant` in `theorem virasoroConductiveRouteMap_nonempty`
  - theorem/lemma is closed by an uninformative constant
  - `67:       status := ExternalRouteStatus.conductiveOverlayCandidate }`
- L134: **SOFT** `vacuous-prop-constant` in `theorem virasoroIntegration_not_certified`
  - theorem/lemma is closed by an uninformative constant
  - `132: def virasoroIntegrationStatus : ExternalRouteStatus :=`

## `InfoGeometry.OperatorAlgebra.VortexPunctureRepair`
- path: `lean/InfoGeometry/OperatorAlgebra/VortexPunctureRepair.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L40: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `38: `
- L84: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `82: variable`
- L127: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `125:     {Memory : Type*} [AddCommGroup Memory] [Module ℝ Memory]`
- L180: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `178:     {Memory : Type*} [AddCommGroup Memory] [Module ℝ Memory]`
- L232: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `230: variable`

## `InfoGeometry.Optics.FiniteJonesBrewsterCollapse`
- path: `lean/InfoGeometry/Optics/FiniteJonesBrewsterCollapse.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L41: **SOFT** `skeletal-proof` in `theorem brewsterMatrix_trace`
  - proof appears to be tactic-automation-only or skeletal
  - `39:   dsimp [det2]`
- L119: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `117: `

## `InfoGeometry.Optics.FiniteJonesKasparovBoundary`
- path: `lean/InfoGeometry/Optics/FiniteJonesKasparovBoundary.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L64: **SOFT** `skeletal-proof` in `theorem kasparovDefect_eq_one_sub_square`
  - proof appears to be tactic-automation-only or skeletal
  - `62:     (D : ConstructiveJonesStinespring) : JonesMat :=`
- L154: **SOFT** `skeletal-proof` in `theorem kernelBasis_eq_modesOf_kasparovDefect`
  - proof appears to be tactic-automation-only or skeletal
  - `152:   kernelBasisOfProjection := K.modesOfDefect`
- L141: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `139: `

## `InfoGeometry.Optics.FiniteJonesModel`
- path: `lean/InfoGeometry/Optics/FiniteJonesModel.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L68: **SOFT** `skeletal-proof` in `theorem diagJones_10`
  - proof appears to be tactic-automation-only or skeletal
  - `66: `
- L116: **SOFT** `skeletal-proof` in `theorem det2_diagJones`
  - proof appears to be tactic-automation-only or skeletal
  - `114:   fin_cases i <;> fin_cases j <;>`
- L124: **SOFT** `skeletal-proof` in `theorem det2_brewsterMatrix`
  - proof appears to be tactic-automation-only or skeletal
  - `122:     det2 (diagJones a b) = a * b := by`

## `InfoGeometry.Optics.FiniteJonesStinespring`
- path: `lean/InfoGeometry/Optics/FiniteJonesStinespring.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L73: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `71: `

## `InfoGeometry.Optics.FiniteJonesStinespringConstructive`
- path: `lean/InfoGeometry/Optics/FiniteJonesStinespringConstructive.lean`
- findings: 7 (hard=0, soft=7, advisory=0)

- L188: **SOFT** `skeletal-proof` in `theorem toStinespringIsometry_V`
  - proof appears to be tactic-automation-only or skeletal
  - `186: `
- L201: **SOFT** `skeletal-proof` in `theorem visibleDefect_eq_environmentGain`
  - proof appears to be tactic-automation-only or skeletal
  - `199:         D.toStinespringIsometry.V :=`
- L291: **SOFT** `skeletal-proof` in `theorem julia_visible_visible_block`
  - proof appears to be tactic-automation-only or skeletal
  - `289: `
- L301: **SOFT** `skeletal-proof` in `theorem julia_hidden_visible_block`
  - proof appears to be tactic-automation-only or skeletal
  - `299:       D.R i j :=`
- L311: **SOFT** `skeletal-proof` in `theorem julia_visible_hidden_block`
  - proof appears to be tactic-automation-only or skeletal
  - `309:       D.V i j :=`
- L132: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `130: `
- L346: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `344: `

## `InfoGeometry.Optics.JonesCalibration`
- path: `lean/InfoGeometry/Optics/JonesCalibration.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L104: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `102: `
- L216: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `214: `
- L439: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `437: variable {Op : Type*} [Ring Op] [Algebra ℂ Op]`
- L631: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `629: `

## `InfoGeometry.Optics.OperatorialJonesCalculus`
- path: `lean/InfoGeometry/Optics/OperatorialJonesCalculus.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L158: **SOFT** `skeletal-proof` in `theorem brewsterReflector_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `156:     (r_s : ℂ) : Op :=`
- L63: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `61: `
- L303: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `301: `
- L365: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `363: `

## `InfoGeometry.Prequantum.Scaling`
- path: `lean/InfoGeometry/Prequantum/Scaling.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L56: **SOFT** `skeletal-proof` in `theorem PrequantumData.rescaleHbar_curvature`
  - proof appears to be tactic-automation-only or skeletal
  - `54:     rw [P.curvature_law]`
- L60: **SOFT** `skeletal-proof` in `theorem PrequantumData.rescaleHbar_hbar`
  - proof appears to be tactic-automation-only or skeletal
  - `58:     (P : PrequantumData) (c : ℝ) (hc : c ≠ 0) :`

## `InfoGeometry.Probability.HomologicalProbability`
- path: `lean/InfoGeometry/Probability/HomologicalProbability.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L279: **SOFT** `skeletal-proof` in `theorem regularTreePercolationThreshold_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `277: def RegularTreePercolationThreshold (d : ℕ) (_hd : 0 < d) : ℝ :=`

## `InfoGeometry.Projective.Null`
- path: `lean/InfoGeometry/Projective/Null.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L78: **SOFT** `skeletal-proof` in `lemma IsGradePlusRay_vacuum`
  - proof appears to be tactic-automation-only or skeletal
  - `76: def IsGradeNullRay (q : ProjectiveState E) : Prop :=`
- L81: **SOFT** `skeletal-proof` in `lemma IsGradeMinusRay_vacuum`
  - proof appears to be tactic-automation-only or skeletal
  - `79: lemma IsGradePlusRay_vacuum : IsGradePlusRay (vacuum E) := by`

## `InfoGeometry.Projective.ProjectiveMap`
- path: `lean/InfoGeometry/Projective/ProjectiveMap.lean`
- findings: 8 (hard=0, soft=8, advisory=0)

- L20: **SOFT** `skeletal-proof` in `lemma map_smul_gauge`
  - proof appears to be tactic-automation-only or skeletal
  - `18: `
- L47: **SOFT** `skeletal-proof` in `lemma projectiveMap_mk`
  - proof appears to be tactic-automation-only or skeletal
  - `45: `
- L52: **SOFT** `skeletal-proof` in `lemma projectiveMap_vacuum`
  - proof appears to be tactic-automation-only or skeletal
  - `50:     (v : DoubledSpace E) :`
- L58: **SOFT** `skeletal-proof` in `lemma projectiveMap_mk_gauge`
  - proof appears to be tactic-automation-only or skeletal
  - `56:     projectiveMap A (vacuum E) = vacuum E := by`
- L71: **SOFT** `skeletal-proof` in `lemma projectiveMapEven_mk`
  - proof appears to be tactic-automation-only or skeletal
  - `69:     ProjectiveState E → ProjectiveState E :=`
- L107: **SOFT** `skeletal-proof` in `lemma modular_j_gauge_equivariant`
  - proof appears to be tactic-automation-only or skeletal
  - `105:     projectiveMapEven A hA (projectivize (u • v)) = projectiveMapEven A hA (projectivize v) :=`
- L112: **SOFT** `skeletal-proof` in `lemma spectral_epsilon_gauge_equivariant`
  - proof appears to be tactic-automation-only or skeletal
  - `110:     modular_j (u • v) = u • modular_j v := by`
- L117: **SOFT** `skeletal-proof` in `lemma complex_i_gauge_equivariant`
  - proof appears to be tactic-automation-only or skeletal
  - `115:     spectral_epsilon (u • v) = u • spectral_epsilon v := by`

## `InfoGeometry.Quantum.AttentionBridge`
- path: `lean/InfoGeometry/Quantum/AttentionBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L19: **SOFT** `skeletal-proof` in `theorem split_softmax_weight_formula`
  - proof appears to be tactic-automation-only or skeletal
  - `17:     (q : Q) : ℝ :=`

## `InfoGeometry.Quantum.BulkBoundary`
- path: `lean/InfoGeometry/Quantum/BulkBoundary.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L38: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `36: `
- L325: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `323: variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]`
- L327: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `325: `
- L875: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `873:   exact hLoc.boundaryLocalized_to_dimMismatch`

## `InfoGeometry.Quantum.EntanglementMonogamy`
- path: `lean/InfoGeometry/Quantum/EntanglementMonogamy.lean`
- findings: 8 (hard=0, soft=8, advisory=0)

- L266: **SOFT** `placeholder-naming` in `theorem bridge_exists_of_entangled`
  - declaration name is marked as placeholder/bridge/hypothesis surface
  - `264: `
- L72: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `70: variable {Q : BipartiteQuantumSystem}`
- L132: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `130: variable {R : BipartiteReadout Q}`
- L176: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `174: variable {Q : BipartiteQuantumSystem}`
- L211: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `209: `
- L264: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `262: `
- L311: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `309: `
- L385: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `383: `

## `InfoGeometry.Quantum.FiniteEntanglementComplexityCore`
- path: `lean/InfoGeometry/Quantum/FiniteEntanglementComplexityCore.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L159: **SOFT** `skeletal-proof` in `theorem copyBobToCharlie_b_eq_c`
  - proof appears to be tactic-automation-only or skeletal
  - `157:   · exact (bellSame_nonzero_iff x).mp h`
- L193: **SOFT** `skeletal-proof` in `theorem hammingWeight_simpleString`
  - proof appears to be tactic-automation-only or skeletal
  - `191: `
- L246: **SOFT** `skeletal-proof` in `theorem classicalSingleFlipComplexity_simple`
  - proof appears to be tactic-automation-only or skeletal
  - `244: `
- L307: **SOFT** `skeletal-proof` in `theorem cost_singleton`
  - proof appears to be tactic-automation-only or skeletal
  - `305: `
- L311: **SOFT** `skeletal-proof` in `theorem cost_append_gate`
  - proof appears to be tactic-automation-only or skeletal
  - `309:     cost ([g] : Circuit Wire) = 1 :=`
- L320: **SOFT** `skeletal-proof` in `theorem cost_append`
  - proof appears to be tactic-automation-only or skeletal
  - `318:     cost (C ++ [g]) = cost C + 1 := by`

## `InfoGeometry.Quantum.GeometricTensorTest`
- path: `lean/InfoGeometry/Quantum/GeometricTensorTest.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L19: **SOFT** `skeletal-proof` in `theorem ofMajorana_g_eq_metric`
  - proof appears to be tactic-automation-only or skeletal
  - `17: local notation      => DoubledSpace E`

## `InfoGeometry.Quantum.HurwitzRGFlow`
- path: `lean/InfoGeometry/Quantum/HurwitzRGFlow.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L34: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `32: `

## `InfoGeometry.Quantum.KitaevChain`
- path: `lean/InfoGeometry/Quantum/KitaevChain.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L59: **SOFT** `skeletal-proof` in `theorem macroscopicVolume_eq_prod_pfaffians`
  - proof appears to be tactic-automation-only or skeletal
  - `57: noncomputable def macroscopicVolume (chain : List KitaevCell) : ℝ :=`
- L63: **SOFT** `skeletal-proof` in `theorem macroscopicVolume_append`
  - proof appears to be tactic-automation-only or skeletal
  - `61: theorem macroscopicVolume_eq_prod_pfaffians (chain : List KitaevCell) :`
- L71: **SOFT** `skeletal-proof` in `theorem macroscopicVolume_singleton`
  - proof appears to be tactic-automation-only or skeletal
  - `69:     macroscopicVolume (chain₁ ++ chain₂) = macroscopicVolume chain₁ * macroscopicVolume chain₂ := by`
- L128: **SOFT** `skeletal-proof` in `theorem hasDefect_singleton_iff_isCritical`
  - proof appears to be tactic-automation-only or skeletal
  - `126:   simpa using`

## `InfoGeometry.Quantum.ModularAnomaly`
- path: `lean/InfoGeometry/Quantum/ModularAnomaly.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L61: **SOFT** `skeletal-proof` in `lemma sigma_zero_clm`
  - proof appears to be tactic-automation-only or skeletal
  - `59: noncomputable def modularAnomalyGenerator (U : X ≃L[ℝ] X) : X →L[ℝ] X :=`
- L45: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `43: variable {X : RealMajoranaCore}`
- L90: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `88: `
- L92: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `90: `
- L125: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `123: `
- L127: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `125: `

## `InfoGeometry.Quantum.RealKCategory`
- path: `lean/InfoGeometry/Quantum/RealKCategory.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L227: **SOFT** `skeletal-proof` in `lemma roundTrip_smul_eq_smulRoundTrip`
  - proof appears to be tactic-automation-only or skeletal
  - `225: noncomputable abbrev smulRoundTrip (X : RealKVect) (r : ℝ) (x : RoundTripObj X) : RoundTripObj X :=`
- L231: **SOFT** `skeletal-proof` in `lemma smulRoundTrip_eq_smulOrig`
  - proof appears to be tactic-automation-only or skeletal
  - `229:     (r • x : RoundTripObj X) = smulRoundTrip X r x := by`

## `InfoGeometry.Quantum.RealMajorana`
- path: `lean/InfoGeometry/Quantum/RealMajorana.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L389: **SOFT** `skeletal-proof` in `lemma transportJ_apply_B`
  - proof appears to be tactic-automation-only or skeletal
  - `387:     change ((T.transportJ.toLinearMap + LinearMap.id : S →ₗ[ℝ] S) x = 0)`
- L393: **SOFT** `skeletal-proof` in `lemma Binv_apply_transportJ`
  - proof appears to be tactic-automation-only or skeletal
  - `391:     T.transportJ (T.B x) = T.B (M.J x) := by`
- L66: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `64: `
- L193: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `191: `
- L269: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `267: `
- L327: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `325: `

## `InfoGeometry.Quantum.RealMajoranaCategory`
- path: `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L177: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `175: `

## `InfoGeometry.Quantum.SplitCliffordAtom`
- path: `lean/InfoGeometry/Quantum/SplitCliffordAtom.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L63: **SOFT** `skeletal-proof` in `lemma Hom.comm_j`
  - proof appears to be tactic-automation-only or skeletal
  - `61: `
- L67: **SOFT** `skeletal-proof` in `lemma Hom.comm_eps`
  - proof appears to be tactic-automation-only or skeletal
  - `65:     f.homCore.hom.comp (jOp X) = (jOp Y).comp f.homCore.hom := by`

## `InfoGeometry.Quantum.ThermofieldDouble`
- path: `lean/InfoGeometry/Quantum/ThermofieldDouble.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L60: **SOFT** `skeletal-proof` in `theorem tfdCoeff_zero_time`
  - proof appears to be tactic-automation-only or skeletal
  - `58:         - Complex.I * ((tL + tR : ℝ) : ℂ) * (S.energy n : ℂ))`
- L77: **SOFT** `skeletal-proof` in `theorem tfdCoeffSupported_eq_zero_of_not_mem`
  - proof appears to be tactic-automation-only or skeletal
  - `75:     (S : FiniteQuantumSpectrum Level) (β tL tR : ℝ) (n : Level) : ℂ :=`
- L132: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `130: `
- L165: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `163: `
- L186: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `184: `
- L305: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `303: `

## `InfoGeometry.RegularizedKL`
- path: `lean/InfoGeometry/RegularizedKL.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L167: **SOFT** `skeletal-proof` in `lemma regTotalCount_pos`
  - proof appears to be tactic-automation-only or skeletal
  - `165:     regularizedPositiveMeasure count ε hε x = (count x : ℝ) + ε := by`

## `InfoGeometry.Renyi`
- path: `lean/InfoGeometry/Renyi.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L50: **SOFT** `skeletal-proof` in `lemma RenyiD_eq_log_Phi_shift_div`
  - proof appears to be tactic-automation-only or skeletal
  - `48:   (hQ : KL.PhiSupportFaithful N_func Q) :`

## `InfoGeometry.Singular.DrazinGreen`
- path: `lean/InfoGeometry/Singular/DrazinGreen.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L35: **SOFT** `skeletal-proof` in `theorem A_mul_Drazin_Green_eq_projector`
  - proof appears to be tactic-automation-only or skeletal
  - `33:     (A D : R) (k : ℕ) (h : IsDrazinInverse A D k) : R :=`
- L135: **SOFT** `skeletal-proof` in `theorem A_mul_drazinGreen_eq_drazinProjector`
  - proof appears to be tactic-automation-only or skeletal
  - `133: noncomputable def drazinResidueProjector (A : Module.End K V) : Module.End K V :=`

## `InfoGeometry.Singular.NaturalGradient`
- path: `lean/InfoGeometry/Singular/NaturalGradient.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L32: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `30: `
- L33: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `31: variable {n : ℕ} (J1 : Matrix (Fin 2) (Fin 2) ℝ)`

## `InfoGeometry.Singular.SchurDrazinMoorePenrose`
- path: `lean/InfoGeometry/Singular/SchurDrazinMoorePenrose.lean`
- findings: 7 (hard=0, soft=7, advisory=0)

- L158: **SOFT** `skeletal-proof` in `theorem drazinRegularProjector_idempotent`
  - proof appears to be tactic-automation-only or skeletal
  - `156:     (hD : IsDrazinInverse A D k) : R :=`
- L194: **SOFT** `skeletal-proof` in `theorem drazinRegular_add_drazinNull`
  - proof appears to be tactic-automation-only or skeletal
  - `192:       drazinNullProjector A D k hD := by`
- L239: **SOFT** `skeletal-proof` in `theorem moorePenroseRangeProjector_idempotent`
  - proof appears to be tactic-automation-only or skeletal
  - `237:     (hMP : IsMoorePenroseInverse A B) : R :=`
- L248: **SOFT** `skeletal-proof` in `theorem moorePenroseRangeProjector_self_adjoint`
  - proof appears to be tactic-automation-only or skeletal
  - `246:       moorePenroseRangeProjector A B hMP := by`
- L83: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `81: `
- L330: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `328: `
- L609: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `607: `

## `InfoGeometry.SuperMetriplectic.Axioms`
- path: `lean/InfoGeometry/SuperMetriplectic/Axioms.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L90: **SOFT** `skeletal-proof` in `theorem netOddShadow_eq_right_minus_left`
  - proof appears to be tactic-automation-only or skeletal
  - `88: abbrev defectShadow (C : ChiralSuperchargeClosure A) : A :=`
- L95: **SOFT** `skeletal-proof` in `theorem anticommutator_netOddShadow_eq_translation_add_defect`
  - proof appears to be tactic-automation-only or skeletal
  - `93:     C.netOddShadow = C.QR - C.QL := by`
- L202: **SOFT** `skeletal-proof` in `theorem effectiveEvenOnsager_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `200: noncomputable def drazinDefectProjector (B : ScalarSchurDrazinBlock) : ℝ :=`
- L212: **SOFT** `skeletal-proof` in `theorem drazinDefectProjector_eq`
  - proof appears to be tactic-automation-only or skeletal
  - `210:     B.effectiveEvenOnsager = B.LPP - B.LPΘ * B.penrose.aPlus * B.LΘP :=`

## `InfoGeometry.SuperMetriplectic.CartanBridge`
- path: `lean/InfoGeometry/SuperMetriplectic/CartanBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L75: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `73: `

## `InfoGeometry.SuperMetriplectic.ChiralBridge`
- path: `lean/InfoGeometry/SuperMetriplectic/ChiralBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L43: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `41: `

## `InfoGeometry.SuperMetriplectic.Cl44WeylD4`
- path: `lean/InfoGeometry/SuperMetriplectic/Cl44WeylD4.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L74: **SOFT** `skeletal-proof` in `theorem coordinate_i`
  - proof appears to be tactic-automation-only or skeletal
  - `72:   else`
- L127: **SOFT** `skeletal-proof` in `theorem cartan_rank_four`
  - proof appears to be tactic-automation-only or skeletal
  - `125: `

## `InfoGeometry.SuperMetriplectic.DrazinBridge`
- path: `lean/InfoGeometry/SuperMetriplectic/DrazinBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L43: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `41: `

## `InfoGeometry.SuperMetriplectic.DrazinCartanShadowBridge`
- path: `lean/InfoGeometry/SuperMetriplectic/DrazinCartanShadowBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L60: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `58: `

## `InfoGeometry.SuperMetriplectic.DrazinProjectorConstraintBridge`
- path: `lean/InfoGeometry/SuperMetriplectic/DrazinProjectorConstraintBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L66: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `64: `

## `InfoGeometry.SuperMetriplectic.MicroscopicEntropyCalibration`
- path: `lean/InfoGeometry/SuperMetriplectic/MicroscopicEntropyCalibration.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L60: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `58: `

## `InfoGeometry.SuperMetriplectic.TriadBridge`
- path: `lean/InfoGeometry/SuperMetriplectic/TriadBridge.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L69: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `67: `
- L237: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `235:              oddOddClosure := hClosure } : TriadCompatibleOddPacket) := by`

## `InfoGeometry.SuperMetriplectic.UnifiedOwnerClosureBridge`
- path: `lean/InfoGeometry/SuperMetriplectic/UnifiedOwnerClosureBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L53: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `51: `

## `InfoGeometry.SuperMetriplectic.UnifiedOwnerEntropyBridge`
- path: `lean/InfoGeometry/SuperMetriplectic/UnifiedOwnerEntropyBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L45: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `43: `

## `InfoGeometry.SuperMetriplectic.UnifiedOwnerTriadBridge`
- path: `lean/InfoGeometry/SuperMetriplectic/UnifiedOwnerTriadBridge.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L65: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `63: `

## `InfoGeometry.Tensor.DeBruijn`
- path: `lean/InfoGeometry/Tensor/DeBruijn.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L152: **SOFT** `skeletal-proof` in `theorem ofPorts_portCompatible_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `150:   · intro h`
- L211: **SOFT** `skeletal-proof` in `theorem lift_portCompatible`
  - proof appears to be tactic-automation-only or skeletal
  - `209:   rcases h with ⟨hs, ht, hb⟩`

## `InfoGeometry.Tensor.DeBruijnFin`
- path: `lean/InfoGeometry/Tensor/DeBruijnFin.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L101: **SOFT** `skeletal-proof` in `theorem ofFinPorts_portCompatible_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `99:     ofPorts_inScope_iff (TensorPort.ofFin source) (TensorPort.ofFin target) binderDepth`
- L186: **SOFT** `skeletal-proof` in `theorem ofFinPorts_portCompatible_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `184:     ofPorts_inScope_iff (TensorPort.ofFin source) (TensorPort.ofFin target) binderDepth`

## `InfoGeometry.Tensor.DeBruijnLift`
- path: `lean/InfoGeometry/Tensor/DeBruijnLift.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L66: **SOFT** `skeletal-proof` in `theorem lift_inScope`
  - proof appears to be tactic-automation-only or skeletal
  - `64:     (p.lift delta).toEdge = p.toEdge.lift delta :=`
- L83: **SOFT** `skeletal-proof` in `theorem lift_shiftSound`
  - proof appears to be tactic-automation-only or skeletal
  - `81:   simpa [Conductive] using`

## `InfoGeometry.Tensor.DeBruijnPayload`
- path: `lean/InfoGeometry/Tensor/DeBruijnPayload.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L27: **SOFT** `skeletal-proof` in `theorem source_readback`
  - proof appears to be tactic-automation-only or skeletal
  - `25: `
- L195: **SOFT** `skeletal-proof` in `theorem endpoint_source_readback`
  - proof appears to be tactic-automation-only or skeletal
  - `193:     r.Promotable ↔ r.payload.toEdge.ContractionSound :=`
- L200: **SOFT** `skeletal-proof` in `theorem endpoint_target_readback`
  - proof appears to be tactic-automation-only or skeletal
  - `198:     r.endpoints.source = r.endpoints.source :=`

## `InfoGeometry.Tensor.DeBruijnPorts`
- path: `lean/InfoGeometry/Tensor/DeBruijnPorts.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L93: **SOFT** `skeletal-proof` in `theorem ofPorts_portCompatible_iff`
  - proof appears to be tactic-automation-only or skeletal
  - `91:     DeBruijnEdge.ofPorts_inScope_iff source target binderDepth scopeDepth sourceBondDim`
- L136: **SOFT** `skeletal-proof` in `theorem lift_ofPorts`
  - proof appears to be tactic-automation-only or skeletal
  - `134:       (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).targetArity :=`

## `InfoGeometry.Thermal.FiniteMatrix`
- path: `lean/InfoGeometry/Thermal/FiniteMatrix.lean`
- findings: 5 (hard=0, soft=5, advisory=0)

- L95: **SOFT** `skeletal-proof` in `lemma partition_pos`
  - proof appears to be tactic-automation-only or skeletal
  - `93: noncomputable def logPartition (H : Hamiltonian n) (β : ℝ) : ℝ :=`
- L101: **SOFT** `skeletal-proof` in `lemma gibbsWeight_pos`
  - proof appears to be tactic-automation-only or skeletal
  - `99: lemma partition_ne_zero (H : Hamiltonian n) (β : ℝ) : H.partition β ≠ 0 :=`
- L109: **SOFT** `skeletal-proof` in `lemma gibbsWeight_sum_one`
  - proof appears to be tactic-automation-only or skeletal
  - `107:     0 ≤ H.gibbsWeight β i :=`
- L178: **SOFT** `skeletal-proof` in `lemma internalEnergy_eq_gibbsExpectation`
  - proof appears to be tactic-automation-only or skeletal
  - `176: `
- L203: **SOFT** `skeletal-proof` in `lemma thermalState_modularShift_invariant`
  - proof appears to be tactic-automation-only or skeletal
  - `201: `

## `InfoGeometry.Thermo.BuresWassersteinKMSCost`
- path: `lean/InfoGeometry/Thermo/BuresWassersteinKMSCost.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L120: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `118: `
- L190: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `188: `
- L285: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `283:     {BW : BuresWassersteinDatum State Ω}`
- L343: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `341:     {Ω : PositiveStateDomain State}`

## `InfoGeometry.Thermo.FiniteDiagonal`
- path: `lean/InfoGeometry/Thermo/FiniteDiagonal.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L136: **SOFT** `skeletal-proof` in `lemma modularShift_diag_fixed`
  - proof appears to be tactic-automation-only or skeletal
  - `134: `
- L188: **SOFT** `skeletal-proof` in `lemma gibbsDensity_diag_pos`
  - proof appears to be tactic-automation-only or skeletal
  - `186:     _ = gibbsWeight H β j * A i j := by`

## `InfoGeometry.Thermo.FiniteMatrix`
- path: `lean/InfoGeometry/Thermo/FiniteMatrix.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L43: **SOFT** `skeletal-proof` in `lemma partitionFunction_ne_zero`
  - proof appears to be tactic-automation-only or skeletal
  - `41: noncomputable def partitionFunction (M : ThermalModel n) : ℝ :=`

## `InfoGeometry.Thermo.Gibbs`
- path: `lean/InfoGeometry/Thermo/Gibbs.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L95: **SOFT** `skeletal-proof` in `lemma softMin_def`
  - proof appears to be tactic-automation-only or skeletal
  - `93: `

## `InfoGeometry.Thermo.KMSDetailedBalance`
- path: `lean/InfoGeometry/Thermo/KMSDetailedBalance.lean`
- findings: 3 (hard=0, soft=3, advisory=0)

- L57: **SOFT** `skeletal-proof` in `theorem standardKMSRegion_upperBoundary`
  - proof appears to be tactic-automation-only or skeletal
  - `55: `
- L143: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `141:     [AddCommGroup Value] [Module ℝ Value]`
- L200: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `198:     [AddCommGroup Value] [Module ℝ Value]`

## `InfoGeometry.Thermo.SusceptibilityHessian`
- path: `lean/InfoGeometry/Thermo/SusceptibilityHessian.lean`
- findings: 15 (hard=0, soft=15, advisory=0)

- L158: **SOFT** `skeletal-proof` in `theorem susceptibility_eq_hessian_response`
  - proof appears to be tactic-automation-only or skeletal
  - `156:     (C.responseFromTangent U).comp`
- L166: **SOFT** `skeletal-proof` in `theorem susceptibility_apply`
  - proof appears to be tactic-automation-only or skeletal
  - `164:         ((C.hessianResponse.hessian U).comp (C.fieldToTangent U)) :=`
- L192: **SOFT** `skeletal-proof` in `theorem toSusceptibilityDatum_susceptibility`
  - proof appears to be tactic-automation-only or skeletal
  - `190:     intro U`
- L303: **SOFT** `skeletal-proof` in `theorem toDielectricResponseDatum_epsilon`
  - proof appears to be tactic-automation-only or skeletal
  - `301:     ∀ U : Op, C.epsilon U = C.susceptibilityEpsilonReadout U`
- L308: **SOFT** `skeletal-proof` in `theorem toDielectricResponseDatum_refractiveIndex`
  - proof appears to be tactic-automation-only or skeletal
  - `306:     C.toDielectricResponseDatum.epsilon = C.epsilon :=`
- L60: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `58:     [NormedAddCommGroup Field] [NormedSpace ℝ Field]`
- L99: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `97:     [NormedAddCommGroup Field] [NormedSpace ℝ Field]`
- L145: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `143:     [NormedAddCommGroup Field] [NormedSpace ℝ Field]`
- L244: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `242: `
- L287: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `285: `
- L352: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `350: `
- L392: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `390: `
- L441: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `439:     {State Op : Type*} [Ring Op] [Algebra ℂ Op]`
- L510: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `508:     {P : SPProjectorPair Op}`
- L639: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `637:     [NormedAddCommGroup Field] [NormedSpace ℝ Field]`

## `InfoGeometry.Thermo.SusceptibilityOnsagerStress`
- path: `lean/InfoGeometry/Thermo/SusceptibilityOnsagerStress.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L70: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `68:     {Op : Type*}`
- L127: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `125:     [NormedAddCommGroup Response] [NormedSpace ℝ Response]`
- L176: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `174:     {Op Carrier : Type*}`
- L231: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `229: instance : CoeFun (ThermodynamicOperatorDerivation Op) (fun _ => Op → Op) where`
- L289: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `287:     {D : ThermodynamicOperatorDerivation Op}`
- L369: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `367:     [NormedAddCommGroup Response] [NormedSpace ℝ Response]`

## `InfoGeometry.Thermodynamics.ProjectiveTemperature`
- path: `lean/InfoGeometry/Thermodynamics/ProjectiveTemperature.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L43: **SOFT** `skeletal-proof` in `theorem betaInvert_involutive`
  - proof appears to be tactic-automation-only or skeletal
  - `41: def betaInvert (β : ℝ) : ℝ :=`
- L48: **SOFT** `skeletal-proof` in `theorem betaInvert_one`
  - proof appears to be tactic-automation-only or skeletal
  - `46:     betaInvert (betaInvert β) = β := by`
- L65: **SOFT** `skeletal-proof` in `theorem one_lt_betaInvert_of_mem_Ioo_zero_one`
  - proof appears to be tactic-automation-only or skeletal
  - `63:   · exact betaInvert_pos (lt_trans zero_lt_one hβ)`
- L82: **SOFT** `skeletal-proof` in `theorem one_isFixed_temperatureClosure`
  - proof appears to be tactic-automation-only or skeletal
  - `80:   theta := betaInvert`

## `InfoGeometry.Thermodynamics.SouriauFoliation`
- path: `lean/InfoGeometry/Thermodynamics/SouriauFoliation.lean`
- findings: 6 (hard=0, soft=6, advisory=0)

- L64: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `62: `
- L106: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `104: variable {State : Type*}`
- L150: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `148: variable {State : Type*}`
- L187: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `185: variable {State : Type*}`
- L220: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `218: variable {State : Type*}`
- L276: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `274: `

## `InfoGeometry.Thermodynamics.SouriauModularS`
- path: `lean/InfoGeometry/Thermodynamics/SouriauModularS.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L56: **SOFT** `skeletal-proof` in `theorem modularSLiftInversion_element`
  - proof appears to be tactic-automation-only or skeletal
  - `54: `

## `InfoGeometry.Thermodynamics.SouriauTemperatureProjective`
- path: `lean/InfoGeometry/Thermodynamics/SouriauTemperatureProjective.lean`
- findings: 7 (hard=0, soft=7, advisory=0)

- L191: **SOFT** `skeletal-proof` in `theorem closure_theta`
  - proof appears to be tactic-automation-only or skeletal
  - `189: `
- L244: **SOFT** `skeletal-proof` in `theorem smul_eq_self_of_stationary`
  - proof appears to be tactic-automation-only or skeletal
  - `242:     (I.closure).theta T = T :=`
- L252: **SOFT** `skeletal-proof` in `theorem read_lift`
  - proof appears to be tactic-automation-only or skeletal
  - `250:     I.element • T = T := by`
- L318: **SOFT** `skeletal-proof` in `theorem closure_theta`
  - proof appears to be tactic-automation-only or skeletal
  - `316: `
- L360: **SOFT** `skeletal-proof` in `theorem smul_eq_self_of_stationary`
  - proof appears to be tactic-automation-only or skeletal
  - `358:     (I.closure).theta T = T :=`
- L368: **SOFT** `skeletal-proof` in `theorem read_lift`
  - proof appears to be tactic-automation-only or skeletal
  - `366:     I.element • T = T := by`
- L436: **SOFT** `skeletal-proof` in `theorem closure_theta`
  - proof appears to be tactic-automation-only or skeletal
  - `434: `

## `InfoGeometry.Topology.CuntzCantorSpectralTriple`
- path: `lean/InfoGeometry/Topology/CuntzCantorSpectralTriple.lean`
- findings: 4 (hard=0, soft=4, advisory=0)

- L79: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `77: `
- L166: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `164: `
- L250: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `248: variable {Op H : Type*} [Ring Op] [StarRing Op]`
- L311: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `309: variable {Alg Frame Sym Label Op H : Type*} [Ring Op] [StarRing Op]`

## `InfoGeometry.Topology.FractalCantorFockWitness`
- path: `lean/InfoGeometry/Topology/FractalCantorFockWitness.lean`
- findings: 9 (hard=0, soft=9, advisory=0)

- L78: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `76: `
- L133: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `131: `
- L177: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `175: `
- L210: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `208: `
- L258: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `256: `
- L306: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `304: `
- L356: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `354: `
- L397: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `395: `
- L508: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `506: `

## `InfoGeometry.TransformationGroups`
- path: `lean/InfoGeometry/TransformationGroups.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L93: **SOFT** `skeletal-proof` in `lemma location_invariant_const`
  - proof appears to be tactic-automation-only or skeletal
  - `91: def location_invariant (g : ℝ → ℝ) : Prop :=`

## `InfoGeometry.Volume.DeterminantBundle`
- path: `lean/InfoGeometry/Volume/DeterminantBundle.lean`
- findings: 1 (hard=0, soft=1, advisory=0)

- L49: **SOFT** `skeletal-proof` in `theorem weylAction_eq_dilation_volumeScale`
  - proof appears to be tactic-automation-only or skeletal
  - `47: def Dilation (s : ℝ) (ω : DeterminantLine V) : DeterminantLine V :=`

