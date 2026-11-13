# Exact graded Clifford unrolling and tensor trains

## Status and source

This draft contains complete Lean proof scripts that still require kernel
acceptance. Independent source reviews are recorded separately below. Neither
a source review nor the absence of proof placeholders is a successful Lean build.

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

All entries below describe the declared source targets, pending kernel checking.

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
| `Tensor.TensorTrainMatricization` | `cutRank_scalar_eq_matricize_rank`, `scalar_four_letter_cutRank_le` | Explicit row equivalence to `Fin.append` matricization; bound `4 ^ min k m`. |
| `Clifford.Cl11PureTensorObstruction` | `controlledTensor_not_simple`, `pairMatrixEquiv_controlled`, `controlledMatrix_not_single_chain` | Native controlled-`K` two-factor tensor is not simple; readback is four-by-four in two-by-two blocks. |
| `Clifford.Cl11TensorTrainSynthesis` | `trainMatrix_eq_iff`, `exists_exact_clifford_train`, `exists_minimal_clifford_train` | Exact matrix readback of the corrected tensor; arbitrary-algebra existence and real scalar simultaneous minimality. |
| `Clifford.Cl11LocalCoreTrain` | `localCore`, `nativeCoreContraction`, `wordReconstruct_trainCoeff_native`, `trainMatrix_eq_nativeCoreReadback` | Actual real local Clifford atoms and variable-bond sums; comparison with word synthesis and matrix readback; original terminal vector retained. |

## Rank and boundary qualifications

A zero tensor with at least one site, or with a retained terminal coefficient,
is simple. The two-factor criterion is rank at most one unless nonzeroness is
added. The homogeneous-chain owner retains a terminal coefficient at length
zero, while the empty native chain itself is `1`.

Minimal TT ranks are native ranks of the corrected coefficient unfoldings,
not ranks of the original matrix. The representation allows `Fin 0` bonds.
The incoming dimension is supplied and excluded from the minimality equality.
Positive cuts include the terminal vector bond; that bond can be zero for the
zero tensor. Classical basis selection supplies exact existence, not a
numerical approximation algorithm.

The general bridge contracts scalar or `B`-valued cores and then applies native
`wordReconstruct`. The local-core owner separately constructs each real `W`
entry as a sum of actual Clifford atoms and contracts the internal bond sums
through native graded head insertion. Its optional coefficient extension uses
one common terminal `b : B` multiplying a real train; it does not assert that
arbitrary `B`-valued cores have that form. Absorption of the terminal vector
into a last core with fixed right boundary dimension one remains a separate
target. Equality with the older right-head spinor coordinates is also outside
the claims.

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

### Completed source work

Independent read-only reviews covered all eleven mathematical owners, including
the homogeneous inverse extension and the independently defined local Clifford
cores. They found no semantic blocker at the declared scope. Subsequent proof
repairs are checked against the actual compiler diagnostics. No source review
is a kernel certificate.

The recovered source snapshots are recorded in
`verification/cl11-graded-unrolling/recovery-evidence.json`. Exact hash matches
are distinguished there from any reconstructed source interval. The original
attachment was recovered and its original SHA-256 verified.

### Local execution boundary

The pinned Mathlib cache hydration completed successfully. The first focused
build failed before checking the new proofs because the workspace disk was
full. A temporary native Lake configuration retained the exact dependency
revisions, selected the independent checkout's sources, and placed generated
outputs on the temporary filesystem. No cache was deleted and no dependency
pin or toolchain was changed.

The queued retry reached Lake, emitted a package-directory relocation warning,
and terminated with return code 247 before reporting a theorem result. The
execution environment then became unavailable. At that recovery checkpoint:

- no new owner had a successful local kernel build;
- the selected-owner axiom audit had not completed;
- the tracked pre-commit source gate and root integration gate had not run
  for the final recovered tree;
- no local full-repository acceptance is claimed.

The first focused CI run, [43406594970](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43406594970),
reached the new owners and reported elaboration errors in `ExactTensorTrain`,
`RankMinimalTensorTrain`, `SplitCliffordMatrixEquiv`, and `Cl11GradedUnrolling`.
The matrix-rank factorization owner compiled. The follow-up proof scripts repair
those reported errors; acceptance of the complete closure remains pending.

The second focused run,
[43408976175](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43408976175),
compiled `SplitCliffordMatrixEquiv`, `Cl11GradedUnrolling`,
`MatrixRankFactorization`, and `RankMinimalTensorTrain` on commit
`4ad3bced5caf5f76b969b1d0237869609911f5be`. Three owners still reported
elaboration failures: `ExactTensorTrain`, `Cl11PureTensorObstruction`, and
`Cl11RecursiveUnrolling`. Their dependent owners and the exhaustive audit
remain blocked until a subsequent successful build.

The tracked staged source gate was subsequently executed. Its remaining T16
finding is on the nested coefficient carrier `Matrix (Fin 2) (Fin 2)
(RealMatrix n)`. The owner exposes `realBlock_noncommuting`, which specializes
the existing matrix witness to that exact carrier. Independent inspection
found that the scanner does not resolve the imported operands' types and its
generic specialization recognizer does not handle matrix coefficient rings;
its raw and expanded carrier strings also differ. The gate remains failed,
and the explicit witness still requires the full Lean check. This record does
not claim source-gate acceptance or alter its criteria.

The published draft includes a focused CI workflow using Lean `v4.34.1` and
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. It builds all eleven owners,
audits every owned declaration, and records exact source hashes. Allowed
foundational axioms remain only `propext`, `Classical.choice`, and `Quot.sound`.
A workflow definition or a queued run is not a successful check.

Root integration remains a separate requirement. The unchanged baseline PR
already reports unrelated optional-package/recursive-checkout failures; those
historical results are context, not a fresh run on this tree. This PR must remain
a draft until its actual checks and any reported proof errors are resolved.
