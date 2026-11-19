# A-A CAPA review: explicit scalar algebra after T16 findings

**Disposition: PASS for the exact revised source snapshots.** The changes replace scalar automation with explicit algebra/order lemmas while preserving all theorem types, hypotheses, and noncommutative operator constructions. No further semantic correction is requested.

Review date: 2026-11-16. Repository: `/workspace/scratch/9eb3301f34a1/info-geometry-lean`. This reviewer performed read-only source comparison, hashing, and native-lemma inspection. No tests, compiler, gates, repository edits, or acceptance commands were run. The parent reports that the first QA attempt stopped at the strict lexical T16 check; this audit does not represent that attempt as a fresh compile or axiom audit.

## Exact reviewed sources

| Owner | Prior approved snapshot SHA256 | Revised SHA256 |
|---|---|---|
| `Analysis/HilbertGramReciprocity.lean` | `bc50cac4df8325569b5b4573c71623b5ec2c6445046fe3598a09eca2c427880b` | `64975ff850e1e32ac98e07a52c2d315e83dcc98a0c60833a854bcbd7d7ddbae9` |
| `Analysis/HilbertGramMoorePenrose.lean` | `c9084d9c8ef24dbb9dd243ddc1d16f25c95ab32cff1e257bff40fdd65d4f4c33` | `aa016bd2a2711ba481373d23496f3e115e84602c0b4321a3e7731ecc219b1f30` |

The old snapshots under `reciprocity/development-hilbert/src/InfoGeometry/Analysis/` were hash-matched and directly compared with the current owners using `diff -u`. The full diff contains only the scalar proof changes summarized below. Targeted staged/worktree comparison was empty.

The trace owner retains SHA256 `cdde658faa0d10ab862a648062b405c3178eeff0a504bfd0a1be223ccdef3451`. Contract, formalization report, and `All.lean` retain hashes `0594dfd47f6ba9a253a4d4f0cf1ce1a5f8ad6c27d49ed146a963274f4d565328`, `d4ce080275e295eb34152f00f23759d2ced56abae5648d3e664383fedfb6effa`, and `5bd6c78068eab621d0ba45fc64a5f1da9ba7172295a2ab3fddf69a469537d09f`, respectively.

## Scalar-goal classification and review

* **Reciprocity line 104:** The expression contains the scalar normalization coefficient, the embedded real eigenvalue, and a scalar inner-product value. `simp only [mul_assoc]` proves reassociation without any commutation. It does not change or commute the underlying operators.
* **Moore–Penrose line 120:** After the isometry norm law and scalar division equivalence, the goal is a real equality. `mul_comm ‖B y‖ (sqrt r)` followed by the established norm equation has the correct orientation. The denominator remains justified by `r>0`.
* **Moore–Penrose lines 138–142:** The cancelled quantity is `‖y‖`, proved strictly positive from the actual nonzero eigenvector. `one_mul` and `mul_right_comm` only rearrange real norm/square-root factors before applying `mul_le_mul_iff_of_pos_right`. No operator product is rearranged.
* **Moore–Penrose lines 143–150:** `one_mul`, `pow_two`, `mul_pow`, and commutation of real squares replace scalar ring normalization. The preceding multiplication inequality retains its nonnegativity conditions. The final substitution still uses `(sqrt r)^2=r` under `r≥0`.
* **Moore–Penrose lines 169–171:** `lt_add_one` supplies `‖B‖² < ‖B‖²+1`; `mul_lt_mul_of_pos_left` uses the existing strict positivity `hr` to multiply by `r`. Transitivity with the upper bound gives `r‖B‖²<1`, contradicting the already-derived `1≤r‖B‖²` through `not_lt_of_ge`. No division by `‖B‖` or extra assumption appears.

The relevant pinned Mathlib order and commutation lemma declarations were inspected. In particular, strict left multiplication requires a positive multiplier, which is supplied by `hr`; right-factor cancellation requires the positive eigenvector norm; and `mul_right_comm` operates here on the commutative real scalar carrier.

The removed automation was applied to scalar goals after the operator identities had been established. These were lexical gate findings, not evidence that the proof had assumed commutativity of operators. The explicit replacements make that distinction inspectable. Actual bounded-map composition, adjoint reversal, native eigenspaces, the constructed isometry, and the existing Moore–Penrose construction remain unchanged. The inventory remains 20 theorems and one definition.

## Preserved audit chain and next gate

Prior reports remain unchanged and were rehashed:

* `aa-source-review.md`: `4bc63e5413fe42394b2fdb545e51695b54bd8cbb1277f94d27ff68f4b770e459`.
* `aa-source-delta-review.md`: `ade9a8d22b075d5b3b7595ba049c45e4e33e3748bb64f14413d2f41ff9b57b9a`.
* `aa-source-delta-final.md`: `f46be5933c5587eddb64b47b0d7fb179a24552c3774ae70d112563e22608121a`.

Their scope findings continue to apply. This closes the A-A review of the revised frozen sources; the independent QA lane must perform its own fresh compiler, axiom, and gate checks. **A-A PASS is not QA acceptance.**
