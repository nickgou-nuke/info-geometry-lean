# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:33.605456+00:00`
Root: `lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **120**
- Hard: **0**
- Soft: **44**
- Advisory: **76**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean` | `advisory` | 164 | 0 | 44 | 76 | 120 |

## Findings by file

### `lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean`
- module: `InfoGeometry.Arithmetic.PrimitiveSetsAbove`
- status: `advisory`
- debt_score: `164`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L92 [soft] `skeletal-proof` in `theorem primeFinsetIcc_primitive` — proof appears to close via minimal tactic one-liner
  - L104 [soft] `skeletal-proof` in `theorem primeFinsetIcc_supportedAbove` — proof appears to close via minimal tactic one-liner
  - L182 [advisory] `existential-packaging` in `def PrimitiveSetsAboveFiniteStatement` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L194 [advisory] `existential-packaging` in `def PrimitiveSetsAboveInfiniteStatement` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L207 [advisory] `existential-packaging` in `def PrimitiveSetsAboveBigOBound` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L257 [soft] `skeletal-proof` in `theorem PrimitiveFinset_iff` — proof appears to close via minimal tactic one-liner
  - L263 [soft] `skeletal-proof` in `theorem SupportedAboveFinset_iff` — proof appears to close via minimal tactic one-liner
  - L270 [soft] `skeletal-proof` in `theorem primitiveWeight_eq_zero_of_not_lt_two` — proof appears to close via minimal tactic one-liner
  - L299 [soft] `skeletal-proof` in `theorem realVonMangoldt_eq_if_isPrimePow` — proof appears to close via minimal tactic one-liner
  - L303 [soft] `skeletal-proof` in `theorem realVonMangoldt_one` — proof appears to close via minimal tactic one-liner
  - L312 [soft] `skeletal-proof` in `theorem realVonMangoldt_eq_zero_iff` — proof appears to close via minimal tactic one-liner
  - L316 [soft] `skeletal-proof` in `theorem realVonMangoldt_ne_zero_iff` — proof appears to close via minimal tactic one-liner
  - L320 [soft] `skeletal-proof` in `theorem realVonMangoldt_pos_iff` — proof appears to close via minimal tactic one-liner
  - L324 [soft] `skeletal-proof` in `theorem realVonMangoldt_apply_pow` — proof appears to close via minimal tactic one-liner
  - L328 [soft] `skeletal-proof` in `theorem realVonMangoldt_apply_prime` — proof appears to close via minimal tactic one-liner
  - L332 [soft] `skeletal-proof` in `theorem sum_realVonMangoldt_divisors` — proof appears to close via minimal tactic one-liner
  - L344 [advisory] `local-hypothesis-injection` in `theorem log_primitiveInverseBase` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L354 [soft] `skeletal-proof` in `theorem primitiveModularKernel_eq_mellinKernel_shift` — proof appears to close via minimal tactic one-liner
  - L375 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L377 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L378 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L384 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L386 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L388 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L389 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L502 [soft] `skeletal-proof` in `theorem primitiveWeight_mul_eq_of_right_one` — proof appears to close via minimal tactic one-liner
  - L506 [soft] `skeletal-proof` in `theorem primitiveWeight_mul_le_of_one_lt_right` — proof appears to close via minimal tactic one-liner
  - L514 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_mul_le_of_one_lt_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L516 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_mul_le_of_one_lt_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L518 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_mul_le_of_one_lt_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L520 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_mul_le_of_one_lt_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L522 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_mul_le_of_one_lt_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L523 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_mul_le_of_one_lt_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L526 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_mul_le_of_one_lt_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L529 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_mul_le_of_one_lt_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L532 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_mul_le_of_one_lt_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L535 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_mul_le_of_one_lt_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L538 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_mul_le_of_one_lt_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L542 [soft] `skeletal-proof` in `theorem primitiveWeight_mul_le_of_ne_one` — proof appears to close via minimal tactic one-liner
  - L553 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_mul_le_of_ne_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L556 [soft] `skeletal-proof` in `theorem primitiveWeight_eq_integral_mellinKernel` — proof appears to close via minimal tactic one-liner
  - L562 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_eq_integral_mellinKernel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L573 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_eq_integral_mellinKernel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L589 [soft] `skeletal-proof` in `theorem primitiveWeight_eq_integral_modularKernel` — proof appears to close via minimal tactic one-liner
  - L594 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_eq_integral_modularKernel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L596 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_eq_integral_modularKernel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L606 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_eq_integral_modularKernel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L627 [soft] `skeletal-proof` in `theorem primitiveWeightSum_empty` — proof appears to close via minimal tactic one-liner
  - L631 [soft] `skeletal-proof` in `theorem primitiveWeightSum_singleton` — proof appears to close via minimal tactic one-liner
  - L635 [soft] `skeletal-proof` in `theorem arithmeticCountWeight_eq_mul_kernel` — proof appears to close via minimal tactic one-liner
  - L639 [soft] `skeletal-proof` in `theorem arithmeticPartition_eq_sum` — proof appears to close via minimal tactic one-liner
  - L643 [soft] `skeletal-proof` in `theorem arithmeticTotalMass_eq_sum` — proof appears to close via minimal tactic one-liner
  - L647 [soft] `skeletal-proof` in `theorem arithmeticBaseShape_eq_div` — proof appears to close via minimal tactic one-liner
  - L811 [soft] `law-field-locker` in `structure-field ArithmeticExponentialRay.partition_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L818 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L848 [soft] `skeletal-proof` in `theorem arithmeticShapeMellin_eq_sum` — proof appears to close via minimal tactic one-liner
  - L853 [soft] `skeletal-proof` in `theorem arithmeticPartition_empty` — proof appears to close via minimal tactic one-liner
  - L857 [soft] `skeletal-proof` in `theorem arithmeticTotalMass_empty` — proof appears to close via minimal tactic one-liner
  - L861 [soft] `skeletal-proof` in `theorem arithmeticShapeMellin_empty` — proof appears to close via minimal tactic one-liner
  - L865 [soft] `skeletal-proof` in `theorem arithmeticPrimePartition_eq_sum` — proof appears to close via minimal tactic one-liner
  - L870 [soft] `skeletal-proof` in `theorem arithmeticPrimePartition_empty` — proof appears to close via minimal tactic one-liner
  - L933 [soft] `skeletal-proof` in `theorem primitiveWeightSum_eq_integral_mellinKernel` — proof appears to close via minimal tactic one-liner
  - L947 [advisory] `local-hypothesis-injection` in `theorem primitiveWeightSum_eq_integral_mellinKernel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1007 [soft] `skeletal-proof` in `theorem primitiveFinset_singleton` — proof appears to close via minimal tactic one-liner
  - L1011 [advisory] `local-hypothesis-injection` in `theorem primitiveFinset_singleton` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1012 [advisory] `local-hypothesis-injection` in `theorem primitiveFinset_singleton` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1088 [advisory] `local-hypothesis-injection` in `theorem primitiveFinset_image_div` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1145 [advisory] `local-hypothesis-injection` in `theorem primitiveDivisorQuotient_erase_one_supportedAbove_two` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1146 [advisory] `local-hypothesis-injection` in `theorem primitiveDivisorQuotient_erase_one_supportedAbove_two` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1151 [advisory] `local-hypothesis-injection` in `theorem primitiveDivisorQuotient_erase_one_supportedAbove_two` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1152 [advisory] `local-hypothesis-injection` in `theorem primitiveDivisorQuotient_erase_one_supportedAbove_two` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1156 [advisory] `local-hypothesis-injection` in `theorem primitiveDivisorQuotient_erase_one_supportedAbove_two` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1163 [advisory] `local-hypothesis-injection` in `theorem primitiveDivisorQuotient_erase_one_supportedAbove_max` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1167 [advisory] `local-hypothesis-injection` in `theorem primitiveDivisorQuotient_erase_one_supportedAbove_max` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1169 [advisory] `existential-packaging` in `theorem primitiveWeightSum_primitiveDivisorQuotient_erase_one_le_of_finiteStatement` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1190 [soft] `skeletal-proof` in `theorem primitiveDivisorQuotient_one_mem_iff` — proof appears to close via minimal tactic one-liner
  - L1198 [advisory] `local-hypothesis-injection` in `theorem primitiveDivisorQuotient_one_mem_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1199 [advisory] `local-hypothesis-injection` in `theorem primitiveDivisorQuotient_one_mem_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1209 [soft] `skeletal-proof` in `theorem primitiveDivisorFiber_eq_filter` — proof appears to close via minimal tactic one-liner
  - L1213 [soft] `skeletal-proof` in `theorem primitiveDivisorQuotient_eq_image_fiber` — proof appears to close via minimal tactic one-liner
  - L1324 [soft] `skeletal-proof` in `theorem primitiveScaledWeightSum_le_if_mem_add_erase` — proof appears to close via minimal tactic one-liner
  - L1385 [soft] `skeletal-proof` in `theorem primitiveWeight_vonMangoldt_divisorSigma_scaled_eq` — proof appears to close via minimal tactic one-liner
  - L1413 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_vonMangoldt_divisorSigma_scaled_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1421 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_vonMangoldt_divisorSigma_scaled_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1455 [soft] `skeletal-proof` in `theorem primitiveWeight_vonMangoldt_divisorSigma_quotient_eq` — proof appears to close via minimal tactic one-liner
  - L1483 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_vonMangoldt_divisorSigma_quotient_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1491 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_vonMangoldt_divisorSigma_quotient_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1530 [advisory] `local-hypothesis-injection` in `theorem supportedAboveFinset_one_nonzero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1579 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_vonMangoldt_divisorSigma_scaled_le_of_supportedAbove` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1581 [advisory] `existential-packaging` in `theorem primitiveWeight_vonMangoldt_divisorSigma_scaled_le_of_finiteStatement` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1610 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_vonMangoldt_divisorSigma_scaled_le_of_finiteStatement` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1611 [advisory] `local-hypothesis-injection` in `theorem primitiveWeight_vonMangoldt_divisorSigma_scaled_le_of_finiteStatement` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1626 [advisory] `existential-packaging` in `theorem primitiveWeight_vonMangoldt_divisorSigma_scaled_split_le_of_finiteStatement` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1705 [advisory] `local-hypothesis-injection` in `theorem badDivisorFilter_eq_empty_of_le_two` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1711 [advisory] `local-hypothesis-injection` in `theorem mem_badDivisorFilter_imp_div_lt` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1712 [advisory] `local-hypothesis-injection` in `theorem mem_badDivisorFilter_imp_div_lt` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1720 [advisory] `local-hypothesis-injection` in `theorem mem_badDivisorFilter_imp_two_lt` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1721 [advisory] `local-hypothesis-injection` in `theorem mem_badDivisorFilter_imp_two_lt` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1734 [advisory] `local-hypothesis-injection` in `theorem mem_badBiUnionDivisorFilter_imp_lt_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1772 [soft] `skeletal-proof` in `theorem mem_largeDivisorFilter_imp_div_lt` — proof appears to close via minimal tactic one-liner
  - L1776 [advisory] `local-hypothesis-injection` in `theorem mem_largeDivisorFilter_imp_div_lt` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1789 [advisory] `existential-packaging` in `theorem primitiveWeight_vonMangoldt_divisorSigma_scaled_le_largeDivisorSlice_of_finiteStatement` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1899 [advisory] `local-hypothesis-injection` in `theorem primitiveWeightSum_le_div_log_mul_sigma` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1901 [advisory] `local-hypothesis-injection` in `theorem primitiveWeightSum_le_div_log_mul_sigma` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L2001 [advisory] `existential-packaging` in `def PrimitiveLargeDivisorAnalyticInput` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L2095 [advisory] `local-hypothesis-injection` in `theorem goodDivisorSumChebyshevBound` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L2096 [advisory] `local-hypothesis-injection` in `theorem goodDivisorSumChebyshevBound` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L2100 [advisory] `local-hypothesis-injection` in `theorem goodDivisorSumChebyshevBound` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L2102 [advisory] `local-hypothesis-injection` in `theorem goodDivisorSumChebyshevBound` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L2112 [advisory] `local-hypothesis-injection` in `theorem goodDivisorSumChebyshevBound` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L2115 [advisory] `local-hypothesis-injection` in `theorem goodDivisorSumChebyshevBound` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L2116 [advisory] `local-hypothesis-injection` in `theorem goodDivisorSumChebyshevBound` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L2118 [advisory] `local-hypothesis-injection` in `theorem goodDivisorSumChebyshevBound` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L2119 [advisory] `local-hypothesis-injection` in `theorem goodDivisorSumChebyshevBound` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L2155 [advisory] `local-hypothesis-injection` in `theorem goodDivisorSumChebyshevBound` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L2199 [soft] `law-field-locker` in `structure-field PrimitiveFiniteMaxEntWitness.entropyReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2203 [soft] `law-field-locker` in `structure-field PrimitiveFiniteMaxEntWitness.admissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2211 [soft] `law-field-locker` in `structure-field PrimitiveFiniteMaxEntWitness.maxent_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2217 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

