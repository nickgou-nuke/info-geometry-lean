# Candidate source-semantic review 01

Reviewer: /root/graded_unroll_intake.

Checkout: /workspace/scratch/9009f3c86480/graded-unroll-extension.

Observed checkout HEAD: ce34c806983f97e7ff3c95b5d06081bd93534c5b.

Scope: independent read-only mathematical/source review of three uncompiled
candidate owners and their stated contract. No owner modifications, Lean/Lake
execution, tests, axiom-collector execution, GitHub writes, or kernel acceptance
were performed by this reviewer.

## Frozen reviewed identities

| File | SHA-256 |
|---|---|
| lean/InfoGeometry/Clifford/Cl11GradedAdjoint.lean | 279b381913282fd0b58d3366c54138cc4e27877871da1133b2ca15fe637f7ec8 |
| lean/InfoGeometry/LinearAlgebra/FiniteRealAnticommutation.lean | 6ff63798bde7ae22a89d4b58c95d492207b26e81bba7f039a23fe5a831f23cff |
| lean/InfoGeometry/Clifford/GradedUnrollingCounterexamples.lean | 74ae3b5c54152b61eb973a8261d40e80d46348ae8138d476cfdce050bcca5597 |
| docs/GRADED_CLIFFORD_STAR_RANK_CONTRACT.md | a68eb6e7c17f55bbd6e95b35ba32ca544607951cda0bf8eff378e9066da12e5b |
| lean/InfoGeometry/Clifford/Cl11GradedTensorMorita.lean | 18d797dbf7943d847d85aea59bb4779a4b5130c585d8139053cc5df8f0298c59 |
| lean/InfoGeometry/Clifford/Cl11GradedMorita.lean | b0011f1c0b9157a18f7237fe1e9f0514d8c55b8850e33409f244ed643fe85419 |
| lean/InfoGeometry/Clifford/Cl11Matrix.lean | c95d89d20b10271d66e9cbe1632f04d57b817f118d92867b5121c55d7c4f7f85 |

The three candidate files were read completely. The actual imported graded
tensor equivalence owner was read completely. The standard-head and concrete
matrix owners were inspected at the definitions and declarations supporting
the representation, parities, generator images, and native matrix convention.
This was a bounded owner/dependency review, not a complete imported-source audit.

## Verdict

**No mathematical or source-semantic blocker found for these exact snapshots.**
Acceptance is limited to source-semantic fit. The files remain uncompiled at
this review and require independent exact-source execution and axiom auditing.
Later changes require a differential or fresh review.

## Cl11GradedAdjoint

The actual carrier is the native graded tensor product of the split Clifford
algebra and the supplied native coefficient grading. Coefficients have an
arbitrary associative real algebra structure, a star-ring structure, and
real star-module compatibility. Neither commutativity nor finite dimension
is assumed.

The imported tensorMatrixEquiv is constructed by a native graded tensor lift
and an explicit matrix-unit inverse. It is not a structure field asserting
the result under review. Pullback of matrix conjugate transpose therefore
constructs an actual anti-involution on the intended carrier.

The head operation pulls real matrix transpose back through the faithful
Walsh-conjugated standard representation. The positive generator is fixed,
the negative generator changes sign, and the even grading implementer is
fixed. The source explicitly distinguishes this convention from Mathlib's
canonical Clifford star and installs no replacement global star instance.

The additive, real-linear, involutive, and product-reversing properties follow
from genuine matrix properties transported through the algebra equivalence.
The LinearEquiv uses the same operation as its inverse. The idempotence
consequence assumes only idempotence of the input, not a parity condition or
the desired conclusion.

The homogeneous formula uses the correct factor (−1)^(ij). Its explicit
coefficient condition θ(star a) = star(θ a) is a sufficient star/parity
compatibility hypothesis, not the claimed tensor identity disguised as an
assumption. The four parity cases agree with the concrete twisted-column
matrix representation. The general anti-involution construction itself
does not require this additional compatibility condition.

The stated boundary is accurate: one native Clifford head with arbitrary
graded coefficients, algebraic anti-involution, and a homogeneous elementary
tensor formula. No positive cone, C* norm, completion, or all-length TT theorem
is asserted by this owner.

## FiniteRealAnticommutation

The matrix statements concern Matrix n n ℝ with finite index n. Ordered matrix
products are retained until taking the real determinant, where commutativity
is legitimate. Nonzero determinants, native IsUnit hypotheses, and odd/even
cardinality are used in the proper carrier.

The even-dimension obstruction does not assume involutivity and thus proves
the stronger valid algebraic statement about any invertible anticommuting pair.
The odd-dimensional singularity statement has one invertible reversing map
and no assumed polynomial for the reversed map.

The Module.End statements transport through LinearMap.toMatrixAlgEquiv on a
finite real basis. They preserve composition and use the actual real vector
space dimension. They do not confuse it with an external coefficient-matrix
index.

The separate square-root-of-minus-identity obstruction correctly uses real
determinant nonnegativity. No analogous statement for arbitrary operator-valued
entries is claimed.

## GradedUnrollingCounterexamples

The reversal counterexample uses the exact matrices S = diag(2,−2,0) and J
swapping the first two coordinates. The owner exhibits J² = 1, its native unit
witness, anticommutation, determinant zero by the general theorem, failure of
S³ = S, and a concrete noncommuting entry. This refutes forced tripotence
without assuming it away.

The external-index example has the full carrier Matrix (Fin 3) (Fin 3) Mat2.
The witnesses repeat Eplus and J1 on the three outer diagonal blocks, but the
coefficient blocks are actual noncommuting 2×2 real matrices. Concrete
noncommutativity is proved at a coefficient entry. This is a valid countermodel
inside the full noncommutative carrier, not a claim that all matrices may be
replaced by diagonal/commuting scalars.

The native Matrix.compAlgEquiv flattens to indices Fin 3 × Fin 2 and transports
the ordered anticommutation law and both IsUnit facts. Its recorded index
cardinality is six. Therefore the example separates odd external index from
even real representation dimension exactly as required.

## Remaining acceptance work

- Exact-source compilation of these owners and their actual repository import
  closure against the unchanged pins.
- Native module-ownership declaration audit with the foundational axiom
  allowlist and explicit per-owner coverage.
- Review of future projector/rank owners and final integration diff.
- Staged and root quality gates reported independently at their actual scope.

No current execution success, axiom footprint, or whole-repository status is
inferred from this source-only review.
