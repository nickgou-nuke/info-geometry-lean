# Tripotent integer grading and structural bridges

## Intake and provenance

This task formalizes the mathematical assertions in the user attachment
`Pasted text(20261113-090226).txt`, preserved verbatim in
`docs/intake/tripotent-integer-structure.txt`. Its SHA256 is
`91f298d175b92810a214d6696f4a4a588c2fa231ee5058449a8a74c0bf89d2c8`.
The starting revision is `c23aa651772224079271a35a0acca5a3f9767354`,
the head of PR #323, `feat/tripotent-graded-operator-flow`.
This change extends that implementation.

The carrier is an arbitrary unital associative real algebra:
`[Ring A] [Algebra ℝ A]`. Multiplication is not assumed commutative.
A tripotent satisfies `S * S * S = S`. Existing owners define
`projPos S = (S² + S)/2`, `projNeg S = (S² - S)/2`,
`projZero S = 1 - S²`, and the integer family `adGrade S k`.

## Reused owners and missing implications

| Existing owner | Actual interface reused | Extension |
| --- | --- | --- |
| `Physics/TripotentAdjointDerivation` | `adGrade`, `mem_adGrade_iff`, multiplication and commutator closure | Native integer graded algebra and finite homogeneous-sum criteria |
| `Physics/Algebra/TripotentPeirceProjectors` | Spectral projectors, orthogonality, idempotence, sum | Extreme support, strict kernels, direct range sums, corner spans |
| `Physics/Algebra/TripotentFiveGradingDecomposition` | `fiveGradeProjector`, `fiveGradeRange`, reconstruction | Internal direct sums on the original carrier |
| `Core/TripotentAdjoint` | Adjoint/eigenspace bridge and quintic annihilator | Native Lagrange interpolation at the actual adjoint |
| `Core/TripotentEigenspaces` | Finite spectral support and native eigenspace identification | Independence and support of all integer grades |
| `Core/TripotentAdjointRigidity` | `ker_ad_sq_eq_ker_ad` | Reuse of the proved bounded-flow converse |
| `OperatorAlgebra/PeirceSpine/TripotentSuperbracket` | Parity and associative signed bracket | Uniform integer homogeneous Jacobi without finite-label side conditions |
| `Canonical/TKKJordanPairData` | Existing repository `JordanPair` structure | Actual extreme Lie intersections, with proved identities and separate trilinearity lemmas |
| `OperatorAlgebra/TripotentExponentialFlow` | Genuine Banach exponential transport and centralizer rigidity | Integer covariance and opposite-grade product generators |
| `Canonical/TripotentMatrixExample` | Dense full 4-by-4 real matrix algebra and transported matrix units | Explicit nonzero integer grades, normalized pair, and constructed Jordan triple |
| Mathlib algebra equivalences and `ConjAct` | `MulSemiringAction.toAlgEquiv` | Commuting-unit covariance and anticommuting-unit grade reversal |

`Core/TripotentChiralRestriction` was consulted as an adjacent owner; the
new generic conjugation proof uses native algebra equivalences directly.
The implementation uses native `Submodule`, `Module.End`, eigenspaces,
`DirectSum.IsInternal`, `GradedAlgebra`, polynomial `aeval`,
`Lagrange.basis`, `LieSubalgebra`, and `skewAdjoint.submodule`.
The Jordan-pair type is the existing repository interface, not a claimed
Mathlib JordanPair type. Its type does not store trilinearity fields;
six explicit theorems supply them for the constructed operations.

## Ordered theorem contract

1. The original family `adGrade S : ℤ → Submodule ℝ A` is independent.
   For tripotent `S`, it has support in `[-2,2]`, spans the algebra,
   and supplies a native graded algebra and algebra equivalence with its
   direct sum. Multiplication and the unit are preserved.
2. The signed associative bracket has typed integer homogeneous codomains.
   Parity addition and signed Jacobi hold uniformly, including intermediate
   degrees outside the five-element support.
3. The grouped Peirce projectors equal native Lagrange polynomials evaluated
   at `ad S`. Every adjoint-stable real submodule decomposes internally
   into its homogeneous intersections; individual corner stability is not
   an extra premise.
4. For a nonzero extreme endomorphism, the middle range is strictly smaller
   than its join with the target spectral range, and that join lies in the
   kernel. The two ranges are disjoint. Opposite operators normalized by
   `Nplus * Nminus = projPos S` and `Nminus * Nplus = projNeg S`
   have common kernel exactly `range (projZero S)`.
5. The real span of same-sign degree-one anticommutators equals the real
   span of products `Psign * x * P0 * y * Popposite`.
   Equality with the entire extreme grade is an explicit spanning criterion.
6. A real-linear ring star reverses weights when `star S = S` and
   preserves them when `star S = -S`. In the former case every
   nonzero-degree skew-adjoint eigenvector vanishes. The native skew
   submodule is an ordinary Lie subalgebra; its anticommutators are
   self-adjoint. Under the skew-generator condition it splits into five
   weights. The paired outer degree-zero corners have zero intersection
   with the middle corner, with explicit reconstruction formulas.
7. Every native Lie subalgebra `p` has an extreme Jordan pair on
   `p.toSubmodule ⊓ adGrade S 2` and
   `p.toSubmodule ⊓ adGrade S (-2)`, with actual triple
   `[[x,y],z]`. Closure, real trilinearity, outer symmetry, and both
   fundamental identities are proved, rather than assumed as fields.
   No adjoint-stability premise on the entire `p` is needed for this pair.
8. A finite homogeneous sum centralizes `S` exactly when its component
   of every nonzero degree vanishes. Repeated degrees are grouped first,
   permitting cancellation within a degree. The double-sum specialization
   uses actual `J m * K n` products grouped by `m + n`.
   Opposite-grade products and their finite sums are immediate centralizer
   elements, without factorwise commutation hypotheses.
9. Algebra equivalences transport grades. Commuting units preserve every
   grade and anticommuting units reverse grades. The genuine bounded
   exponential flow preserves all integer grades exactly when its generator
   commutes with a tripotent, and opposite-grade products supply such
   generators.
10. The existing dense full matrix model witnesses all five integer grades,
    both normalized products, and a nonzero triple of the constructed
    Jordan pair for `p = ⊤`. This is not a witness of a nonzero
    skew-adjoint/Krein extreme pair.

## Corrections and boundaries

- The quintic `D⁵ - 5D³ + 4D` is an annihilating polynomial, not
  necessarily the minimal polynomial. Some or all nonzero grades may vanish.
- On the extreme grades `D⁴ - D² = 12 id`; the extra factor `3` in
  the attachment's intermediate factorization is incorrect.
- `star S = -S` suffices for skew-submodule stability but does not force
  nonzero skew extremes. Necessity fails in general: a central summand
  does not change the adjoint. The exact criterion for skew `X` is
  `adOp (S + star S) X = 0`.
- Ordinary skew-adjoint Lie closure does not imply superbracket closure.
  Positive C-star hypotheses are not imposed on the skew-tripotent
  construction.
- Products through the middle corner mean a linear span of products.
  No categorical Morita equivalence or unconditional endpoint generation
  is asserted.
- Normalized opposite pairs are sufficient for common-kernel isolation;
  common-kernel isolation does not automatically construct a normalized pair.
- The parity element `2P0 - 1` commutes with `S` and acts by degree
  parity. It is distinct from an anticommuting grade reverser.
- A reversing unit does not classify the full centralizer normalizer.
  For `diag(1,0,-1)` in real 3-by-3 matrices, every permutation matrix
  normalizes the diagonal centralizer.
- The algebraic covariance theorem for a supplied commuting unit does not
  construct an unbounded unitary flow. The unbounded Stone--Tomita/KMS
  node H8 remains open analytic work. A domain, spectral calculus,
  strongly continuous unitary group, state, and analytic boundary theorem
  are still needed.
- Defining an unbounded generator as `-log ρ` requires appropriate
  faithfulness/injectivity or restriction to the support of `ρ`.
  With that sign, `exp(i t K) = ρ^(-i t)`. For inverse temperature
  `β > 0`, the scaling is `K = -β⁻¹ log ρ`.
  Resolvent commutation establishes no KMS state by itself.
- Existing bounded strip/KMS and algebraic twisted-trace owners are separate
  constructions. No unbounded conclusion is introduced as an axiom or a
  supplied-result structure field. H9 is therefore a corrected algebraic
  chain with bounded dynamics, not the attachment's unrestricted synthesis.

## Review and verification record

Generation/integration: root, with isolated candidates from
`tripotent_owner_scout` and `tripotent_kernel_candidate`.
Independent mathematical/source review: `tripotent_spec_audit`.
Environment restoration and independent QA: `tripotent_build_setup`.
The acceptance agent did not author proof content.

The initial local staged proof gate passed. The initial strict screener
identified one lexical unused-hypothesis warning: `omega` consumed
`hk : k ≠ 0` implicitly. Its use was made explicit as
`exact hk (by omega)`, without changing the theorem.
The vacuity linter's arithmetic-automation, inferred-parameter, and local
double-negation warnings were independently classified as false positives.

The local 57-module baseline check stopped while restoring pinned Mathlib:
`No space left on device`. It compiled zero project modules and performed
no declaration axiom audit. The workspace later became unavailable.
Reviewed sources were recovered with SHA256 checks against the saved
pre-failure hashes; the intake recovery also matched its original hash.

The scoped workflow `tripotent-integer-structure.yml` runs the canonical
source-integrity checker, strict OpenGauss screening, and vacuity reports.
It then invokes `check_tripotent_integer_structure.py`, which reuses the
maintained exact-source closure checker and native owning-module axiom audit.
Every selected owner's declarations, including private/generated ones, must
use only `propext`, `Classical.choice`, and `Quot.sound`.
Compilation, semantic review, static checks, and axiom auditing are distinct.

Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` are unchanged.
Current upstream results and the exact verified source revision are recorded
on the pull request. A selected-source success is not a whole-repository
certificate or a successful local pre-push gate. Existing root-package
dependencies and quality gates are unchanged.
