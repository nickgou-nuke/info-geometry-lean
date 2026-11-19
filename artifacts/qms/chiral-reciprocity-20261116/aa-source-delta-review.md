# A-A delta review: proof repairs and completeness scope

## Disposition

**PASS for the exact source and documentation snapshots below.** The proof repairs preserve the reviewed mathematics. Removing the completeness assumption from the cyclic weighted-commutator theorem is a valid strengthening, with the corresponding analytic limitation correctly documented.

This is a read-only source/semantic review dated 2026-11-16. No compiler, tests, source gates, or acceptance tools were run, and no repository files were edited. Development compiler results reported by the parent are not independent QA acceptance. The running development session is not used as evidence of a completed result.

The initial audit remains unchanged at `reciprocity/aa-source-review.md`, SHA256 `4bc63e5413fe42394b2fdb545e51695b54bd8cbb1277f94d27ff68f4b770e459`. Its source semantics and scope findings continue to apply, except for the explicitly reviewed completeness strengthening below.

## Exact snapshot record

Repository: `/workspace/scratch/9eb3301f34a1/info-geometry-lean`.

| Artifact | Reviewed SHA256 |
|---|---|
| `lean/InfoGeometry/Analysis/HilbertGramReciprocity.lean` | `bc50cac4df8325569b5b4573c71623b5ec2c6445046fe3598a09eca2c427880b` |
| `lean/InfoGeometry/Analysis/HilbertGramMoorePenrose.lean` | `c9084d9c8ef24dbb9dd243ddc1d16f25c95ab32cff1e257bff40fdd65d4f4c33` |
| `lean/InfoGeometry/Analysis/GradedExponentialTrace.lean` | `384521a207386586b85b729ff4d1d30c14d0fcbc9c736d9a017e3f2588b49179` |
| `docs/CHIRAL_RECIPROCITY_CONTRACT.md` | `0594dfd47f6ba9a253a4d4f0cf1ce1a5f8ad6c27d49ed146a963274f4d565328` |
| `docs/CHIRAL_RECIPROCITY_FORMALIZATION.md` | `d4ce080275e295eb34152f00f23759d2ced56abae5648d3e664383fedfb6effa` |
| `lean/InfoGeometry/All.lean` | `5bd6c78068eab621d0ba45fc64a5f1da9ba7172295a2ab3fddf69a469537d09f` |

The targeted `git diff --name-only -- <six reviewed paths>` was empty: staged and worktree contents agreed for these artifacts at review time. `All.lean` has the same hash as the initial three-import review. The declaration inventory remains **20 theorems and one definition**.

## Comparison evidence

The Hilbert candidate files retain the initially approved hashes:

* `reciprocity/candidates/HilbertGramReciprocity.lean`: `509d924afe43d1e9420becafd7f9f7b19ae719ecb5b98a8cc641e94cecca90a2`.
* `reciprocity/candidates/HilbertGramMoorePenrose.lean`: `2a218f7f5995df24c075d711ef4a1bac519445ddcae010c3dc3f123058eae7d0`.

The trace source preserved under `reciprocity/development-attempt-2/src/InfoGeometry/Analysis/GradedExponentialTrace.lean` has the initially approved hash `45755d760281cd434c364f8aa7e009c496355839081059b8f51a53ff116c767c`.

These exact initial files were hashed and directly compared to the current owners with `diff -u`; current owners were also read directly. Ordinary diff exit status one recorded source differences, not a failed test. Current documentation and the relevant pinned Mathlib `Commute.exp_right` source were read to assess the changed scope.

## Delta findings

| Location in current source | Change | Semantic finding |
|---|---|---|
| `HilbertGramReciprocity.lean:133` | Removed the trailing `ring` after `field_simp`. | Proof-only. The theorem type, denominator nonzero proof, construction, and normalization are unchanged. |
| `HilbertGramMoorePenrose.lean:104` | Same removal of trailing `ring`. | Proof-only; square-root direction and eigenspace identity are unchanged. |
| `HilbertGramMoorePenrose.lean:138` | Uses `mul_le_mul_iff_of_pos_right hy_norm`. | Correct API for cancelling the strictly positive eigenvector norm. No assumption or inequality direction changes. |
| `GradedExponentialTrace.lean:73–78` | Replaces the incomplete tactic step with explicit distributivity, associativity, and `E²=0` rewrites. | Shows directly why only the first factor must square to zero. The arbitrary partner remains unrestricted. |
| `GradedExponentialTrace.lean:101–104` | Explicitly types the vanishing coefficient and replaces the deprecated conditional simplification lemma. | Coercion/elaboration repair only; the cyclic functional and positive-power conclusion are unchanged. |
| `GradedExponentialTrace.lean:114–126` | Explicitly omits `CompleteSpace A` from the additive cyclic weighted-commutator theorem. | Valid strengthening; see the scope analysis below. |
| `GradedExponentialTrace.lean:143–170` | Introduces typed entrywise `HasSum` intermediates and restricts block simplifications. | Preserves actual convergent block-exponential transport. The constant term and both off-diagonal blocks remain accounted for. |
| `GradedExponentialTrace.lean:197–201` | Separates block multiplication, trace decomposition, and final simplification. | Preserves the ordered products, signed blocks, and dimension correction. No diagonalization or extra commutativity premise appears. |

### Completeness strengthening

The pinned Mathlib theorem `Commute.exp_right`, in `Mathlib/Analysis/Normed/Algebra/Exponential.lean`, requires no complete-space assumption. It proves that commuting with the argument implies commuting with the native `exp` value. The new weighted-commutator theorem then applies the existing algebraic cyclic-trace cancellation to that commuting weight. Its functional is only additive and cyclic, and is never moved through an infinite sum.

Therefore removing completeness is correct for this theorem. It does **not** establish convergence of the exponential series in an arbitrary incomplete algebra; native `exp` is a total definition there. The current docstring at lines 114–117, contract at lines 103–106, and report at lines 251–255 make the required distinction: completeness is unnecessary for the commutation argument, while the analytic results use complete carriers where the native exponential has its convergent series.

The separate `cyclicFunctional_exp_odd_square` still retains `CompleteSpace A` and still transports a genuine native `HasSum` through a continuous linear map. The finite matrix applications remain complete and retain their genuine exponential interpretation. There is no extension to ordinary traces on all bounded Hilbert operators, no unbounded heat kernel, and no new index interpretation.

## Documentation and remaining work

The report continues to label implementation and final validation as pending. It preserves the earlier corrections replacing premature “checked declarations” and established-acceptance wording. The statement inventory, noncommuting witness, separate `EF` weight, point-spectrum obstruction, and open analytic claims remain faithful to the current owners.

No new semantic issue, vacuity problem, hidden desired-conclusion premise, or scope overclaim was found. No source change is requested for these hashes. The separate compiler/QA lanes must still establish their own frozen-source compile, axiom, warning, gate, and hook results. Later proof repairs require hash-specific delta review; validation-record-only updates need not reopen unchanged mathematics.

**Final A-A delta disposition: PASS; independent QA acceptance remains separate.**
