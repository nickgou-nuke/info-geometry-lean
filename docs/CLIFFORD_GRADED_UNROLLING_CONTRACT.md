# Exact graded Clifford unrolling and tensor trains

## Status and source

The eleven selected mathematical owners have passed the focused Lean build and
exhaustive declaration-axiom audit at `3a183d7a527cfea5ede84c301bc4b1e681a0028e`. The
[checked evidence](../verification/cl11-graded-unrolling/checked-evidence.json)
identifies the exact revision and verification run. The staged source gate and
repository-wide SorryGate remain failed as recorded below.

The input is the user attachment `Pasted text(20261113-085735).txt`, preserved
byte-for-byte in `handover/injections/cl11-graded-unrolling-source.md`.
Its SHA-256 is
`4c2d41da3c0f692a6e414e03f9c6aaa3066497cae21bc4335b37535f83c8e9d7`.
The implementation baseline is PR #338 at
`ce34c806983f97e7ff3c95b5d06081bd93534c5b`. Prior compression PR #350 is a
separate task. This continuation reuses the existing native graded tensor
equivalence and the pinned Lean/Mathlib environment.

## Mathematical primitives and dependency order

1. The native real Clifford quotient of the recursive split quadratic form.
2. Its existing recursive generator representation and proved surjectivity.
3. Its native dimension recurrence, yielding faithfulness at every finite stage.
4. The resulting algebra equivalence and one tensor factor containing the entire
   arbitrary real coefficient algebra.
5. The native graded head equivalence, explicit Walsh basis change, and
   involutive four-coefficient parity correction.
6. A separately constructed left-head equivalence, explicit binary indexing,
   and canonical Clifford parity identified with conjugation by the recursive
   tensor power of `K`.
7. Exact recursive inverse, real-linear word coordinates, and native synthesis.
8. Homogeneous native chains with forward and inverse suffix-parity correction; simple chains
   characterized by factorization of the corrected coefficient tensor.
9. Actual ordered matrix-core contraction, exact image-basis factorization with
   a left inverse, and one compatible train attaining all positive cut ranks.
10. Explicit prefix/suffix reindexing and native Clifford readback of the
    contracted train, including comparison with every other exact train.
11. Independently defined local Clifford cores, contracted through native
    graded head insertion and proved equal to the same global word synthesis.
12. Ordered absorption of a positive-length train's terminal vector into its
    last core, fixing the outer dimensions to one while preserving all
    interior ranks and the same native matrix reconstruction.

Each dependency is a map, an inverse identity, or a stated implication. Naming
a dependency DAG establishes no additional theorem. No psychological or physical
interpretation is used as a formal hypothesis.

## Carrier and convention contract

The coefficient algebra satisfies only `[Ring B] [Algebra ℝ B]`. The general
unrolling theorem imposes no commutativity or finite-dimensionality hypothesis
on `B`. There is one copy of `B` in `Clsplit n ⊗[ℝ] B`. It is not repeated
independently at each Clifford site.

The native Clifford orthogonal-sum step uses `CliffordAlgebra.prodEquiv`.
The intake basis is `(1, η, K, Ω)`, with `η = Eplus`, `Ω = Eminus`, and
`K = J1` in the original `Cl11Matrix` convention. The first and third basis
elements are even. Right multiplication by `K` exchanges `1 ↔ K` and
`η ↔ Ω`. The one-step adapter explicitly undoes the existing standardized
owner's Walsh change of basis.

The older spinor representation puts the recursive head on the rightmost
binary tensor index. The new recursive map constructs a left-head convention
independently, with the first bit most significant. No equality between these
two coordinate maps is asserted.

Coefficient arrays are real-linear coordinates. Their pointwise ring product
is not the Clifford product. Multiplicativity is carried by actual native
algebra equivalences. The inverse is defined on every matrix, including
singular matrices.

## Declaration map

The declarations below belong to the eleven selected owners covered by the
checked build and exhaustive audit. Their precise scope is part of the contract.

| Owner | Main declarations | Exact scope |
| --- | --- | --- |
| `Clifford.SplitCliffordMatrixEquiv` | `splitClNNAlg_finrank`, `spinorRepresentation_bijective`, `splitSpinorAlgEquiv` | Every natural stage, including zero; actual native quotient and existing generator representation. |
| Same | `coefficientMatrixEquiv`, `unroll`, inverse laws, `unroll_mul`, `unroll_expansion` | One arbitrary real coefficient algebra; ordered products and exact matrix-unit expansion. |
| `Clifford.Cl11GradedUnrolling` | `coefficientEquiv`, `correctionEquiv`, `tensorMatrixEquivOriginal`, `tensorMatrixEquivOriginal_symm_apply` | Four original-basis blocks, involutive odd-tail exchanges, and actual native graded inverse. |
| `Clifford.Cl11RecursiveUnrolling` | `leftMatrixEquiv`, `matrixParity_eq_gamma_conj`, `unrollCoefficients_succ`, `binaryUnroll_succ` | Actual left-head recursive construction; explicit binary indices and four corrected recursive calls. |
| Same | `wordCoefficientEquiv`, `wordReconstruct`, `wordReconstruct_succ` | All word coefficients and their synthesis through actual native Clifford heads. |
| `Clifford.Cl11HomogeneousChains` | `nativeChain_matrix_suffixParity`, `unrollNative_ordinaryChain_suffixParity`, `unrollCoefficients_ordinaryChain_suffixParity`, `unrollCoefficients_pure_chain_iff` | Forward and inverse suffix parity come from actual native homogeneity; real site atoms and one terminal coefficient; empty and zero cases included. |
| `Algebra.MatrixRankFactorization` | `exists_rank_factorization_with_left_inverse`, `rank_isLeast_factor_width`, `rank_le_one_iff_pure` | Actual image-basis factorization `L * R = M`, `Q * L = 1`; least width, including zero; two-factor outer-product criterion. |
| `Tensor.ExactTensorTrain` | `eval_full_word_train`, `matricize_eval_eq_mul`, `matricize_eval_rank_le` | Ordered exact contraction over a semiring; native rank bounds over a field. The full-word witness does not claim compression. |
| `Tensor.RankMinimalTensorTrain` | `exists_rank_minimal_train`, `cutRank_coeff_le_bond`, `exists_bondwise_minimal_exact_train` | One actual variable-bond train attains every positive cut rank simultaneously; every competing exact train obeys the lower bound. |
| Same | `Train.absorbTerminalBoundary`, coefficient/bond/boundary preservation theorems | Ordered last-core absorption over an arbitrary semiring; empty train unchanged; positive-length final bond and boundary fixed to one; every earlier bond preserved. |
| `Tensor.TensorTrainMatricization` | `cutRank_scalar_eq_matricize_rank`, `scalar_four_letter_cutRank_le` | Explicit row equivalence to `Fin.append` matricization; bound `4 ^ min k m`. |
| `Clifford.Cl11PureTensorObstruction` | `controlledTensor_not_simple`, `pairMatrixEquiv_controlled`, `controlledMatrix_not_single_chain` | Native controlled-`K` two-factor tensor is not simple; readback is four-by-four in two-by-two blocks. |
| `Clifford.Cl11TensorTrainSynthesis` | `trainMatrix_eq_iff`, `exists_exact_clifford_train`, `exists_minimal_clifford_train` | Exact matrix readback of the corrected tensor; arbitrary-algebra existence and real scalar simultaneous minimality. |
| `Clifford.Cl11LocalCoreTrain` | `localCore`, `nativeCoreContraction`, `wordReconstruct_trainCoeff_native`, `trainMatrix_eq_nativeCoreReadback`, `exists_unitBoundary_minimal_native_core_train` | Actual real local Clifford atoms and variable-bond sums; exact matrix readback; positive-length unit boundaries with simultaneous interior-cut minimality. |

## Rank and boundary qualifications

A zero tensor with at least one site, or with a retained terminal coefficient,
is simple. The two-factor criterion is rank at most one unless nonzeroness is
added. The homogeneous-chain owner retains a terminal coefficient at length
zero, while the empty native chain itself is `1`.

Minimal TT ranks are native ranks of the corrected coefficient unfoldings,
not ranks of the original matrix. The representation allows `Fin 0` bonds.
The incoming dimension is supplied and excluded from the minimality equality.
Positive cuts include the terminal vector bond; that bond can be zero for the
zero tensor. Terminal absorption then fixes the final dimension to one for
positive length and preserves every earlier bond. The resulting fixed-boundary
theorem asserts minimality only at interior cuts; it makes no terminal-rank
minimality claim. Empty trains retain their scalar boundary, which equals a
unit boundary exactly when that scalar is one. Classical basis selection
supplies exact existence, not a numerical approximation algorithm.

The general bridge contracts scalar or `B`-valued cores and then applies native
`wordReconstruct`. The local-core owner separately constructs each real `W`
entry as a sum of actual Clifford atoms and contracts the internal bond sums
through native graded head insertion. Its optional coefficient extension uses
one common terminal `b : B` multiplying a real train; it does not assert that
arbitrary `B`-valued cores have that form. Absorption of the terminal vector
into the last actual core gives a fixed right boundary dimension one at
positive length; the native local-core bridge proves exact reconstruction and
interior minimality after that normalization. Equality with the older
right-head spinor coordinates remains outside the claims.

## Existing owners inspected and reused

- `Clifford.Cl11Matrix`: original real atom and native Clifford equivalence.
- `Clifford.Cl11GradedMorita`: inner canonical parity and Walsh conventions.
- `Clifford.Cl11GradedTensorMorita`: native graded lift and four-unit inverse.
- `Clifford.Tower`: native orthogonal-sum equivalence.
- `Clifford.Cl55SpinorRepresentationGeneration`: unconditional all-stage
  surjectivity of the actual representation.
- `Clifford.SplitCliffordNativeTensorFinrank` and
  `Canonical.SplitCliffordColimitDimension`: native finite dimensions.
- `Canonical.SplitCliffordHeadMorita`: actual finite/algebraic-colimit tail maps.
- `OperatorAlgebra.PeirceHadamardNative`: arbitrary-ring Walsh identities.
- Mathlib native matrix/tensor equivalences, range bases, matrix rank, and
  finite-dimensional injectivity.

## Verification record

### Checked selected-owner result

The [focused CI job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43421680904/job/131872938214)
on `3a183d7a527cfea5ede84c301bc4b1e681a0028e` completed the selected-owner build and a fresh Lean
execution of `Cl11GradedUnrollingAudit.lean` with warnings treated as errors.
The [checked evidence receipt](../verification/cl11-graded-unrolling/checked-evidence.json)
records this result separately from the historical source-recovery record.

| Check | Result | Coverage |
| --- | --- | --- |
| Focused kernel build | PASS | All eleven mathematical owners and their required imports. |
| Exhaustive declaration-axiom audit | PASS | `470` declarations across all eleven selected owners, including private and generated declarations. |
| Observed axiom dependencies | `[propext, Classical.choice, Quot.sound]` | Transitive dependencies collected through Lean's native `Lean.collectAxioms`. |
| Canonical audit-source comparison | Exact match | The tracked audit source matches `tools.quality.reviewed_audit_source.audit_source` for the same eleven owners. |

The audit selects declarations by native module ownership, requires a positive
count for every selected owner, and rejects unsafe or partial owned declarations.
Its only allowed foundational axioms are `propext`, `Classical.choice`, and
`Quot.sound`. The observed set above is taken from the completed audit output.
The generator comparison and the fresh Lean execution are separate checks.

The implementation uses explicit `noncomputable` declarations for recursive
real Clifford constructions and native `Nat.rec` folds for computational train,
indexing, and parity operations. Generic semiring contraction and terminal
normalization retain their computational scope. These changes avoid newly owned
unsafe recursive runtime helpers without changing the exhaustive audit, its
owner selection, or its axiom allowlist.

The workflow uses Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Its
`cl11-graded-unrolling-evidence` artifact contains the build and fresh audit logs,
plus `source-evidence.json` identifying the exact checked commit, toolchain,
selected owners, and source hashes. Reused build traces do not replace the fresh
final audit. This result covers the selected owners and their import closure;
root integration remains a separate requirement.

### Separate checks and outstanding failures

| Check | Recorded result | Evidence and scope |
| --- | --- | --- |
| Staged source gate, 2026-11-13 UTC | FAIL: one T16 finding | `Cl11RecursiveUnrolling.lean:44`; imported and nested matrix-carrier recognition remains unresolved. |
| Root SorryGate, 2026-11-13 UTC | FAIL: 91 debt files, 878 findings | [Run 43421680575, job 131872936887](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43421680575/job/131872936887); repository-wide debt gate. |
| Local full acceptance | INCOMPLETE | The local prerequisite build ended with wrapper exit 247 after subprocess exit 137. |

The T16 finding concerns `Matrix (Fin 2) (Fin 2) (RealMatrix n)`. The explicit
native witness `realBlock_noncommuting` compiled in the preceding focused checks
and belongs to the checked owner. The scanner does not recognize the imported
witness specialization on this nested carrier. The source gate remains failed;
its criteria are unchanged. The root SorryGate failure is
also unresolved. No local full-repository acceptance is claimed, and the focused
result does not clear either separate gate. The PR remains a draft while those
acceptance requirements are unresolved.

### Source provenance and review

Independent read-only reviews covered all eleven mathematical owners, including
the homogeneous inverse, terminal-boundary normalization, and native local-core
bridge. Source review and hash identity establish different facts from the
kernel and axiom results above.

[recovery-evidence.json](../verification/cl11-graded-unrolling/recovery-evidence.json)
remains the unchanged historical recovery record. It distinguishes exact recovered
hash matches from reconstructed source intervals. The original attachment and its
SHA-256 are preserved. The checked evidence receipt records the later execution
result without rewriting that history.
