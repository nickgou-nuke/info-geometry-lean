# Clifford–Dirac operator algebra: epistemic contract

## Frozen input and source authority

The source is the user attachment `Pasted text(20261028-091007).txt`, received
2026-10-28, SHA-256
`1a28ad7ea95f5538c5c4b8289ba83855af1a4945fb58e08293877f3877b49716`.
The complete attachment is preserved with the task. Its generated code and
claims of compilation are input claims, not verification evidence.

Base: `cb7482d86eadb42f2ab9c2f6f624d67b7bfe7ce4`.
Lean: `leanprover/lean4:v4.34.1`.
Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
No dependency or toolchain changes are part of this work.

Repository discovery inspected tracked owner definitions, imports, proofs, and
direct consumers, then searched the broader `dirac`, `backward`, `defect`,
`Weitzenbock`, `curvatureCommutator`, grading, and centralizer surfaces. An
unrelated checkout's untracked `CanonicalGeometry` candidates are not base
owners and are not dependencies of this change.

## Atomic claims and dispositions before proof generation

| Input atom | Disposition | Exact mathematical meaning |
| --- | --- | --- |
| Two involutions anticommute | Named hypotheses | `g*g = 1`, `h*h = 1`, `g*h + h*g = 0` in an arbitrary unital ring. |
| Their product squares to minus one | Existing owner | `positive_bivector_sq_neg_one`; a complex structure, without a quaternion classification claim. |
| Reversal flips the bivector | Locally provable | Reversing the two factors changes the sign. Adjoint reversal also needs self-adjoint generators. |
| Forward/backward operators | Locally provable | `g*x+h*y` and `x*g+y*h`; difference equals the two paired commutators. This is factor reversal. |
| Dirac square equals sum of squares plus curvature | Conditional existing owner | Four mixed commutations suffice to remove the defects; the coefficient pair remains free to fail to commute. Cancellations can also remove the total defect. |
| The same expansion without compatibility | New theorem contract | Retain four explicit mixed commutator defects; impose no mixed commutation assumptions. |
| Sign-flipped expression | Locally provable | Inner conjugation by `g`, under the relevant compatibility assumptions. |
| Chiral charge and the N=2 label | Clarification and extension | The raw theorem does not assert equality of squares. `(gamma*Q)^2 = -Q^2`; the complex charge `I • (gamma*Q)` supplies the stronger equal-square construction. |
| Grading may be constructed from Clifford data | New integration | `gamma = I • (g*h)`; the second charge is `h*x-g*y`. |
| Actual adjoint block doubling | Existing owner plus extension | Reuse rectangular `dirac T`, `qPlus T`, `qMinus T`, and the two Gram operators. Add the equal-square Hermitian charge. |
| Joint commutant preserves each polynomial | Native owner plus application | Membership in `Algebra.adjoin` and `Subalgebra.centralizer`, with native `Commute`. |
| Separate invariance versus Hamiltonian conservation | Clarification and counterexample to a stronger reading | The raw theorem proves commutation with a specified joint symmetry `C`. Commutation of each summand with the Hamiltonian is a different, generally false statement. |
| Matrix coefficients are derivations | Unsupported interpretation | Call them coefficient endomorphisms. Native adjoint Lie actions, if used, have an explicit associative Leibniz statement. |
| Geometric Lichnerowicz, time reversal, Cartan core, quaternion algebra | Open interpretation debt | No manifold, compatible bundle connection, antiunitary operation, Cartan classification, or quaternion representation is supplied by the attachment. |

## Ground-truth carriers and owners

All universal identities use a potentially noncommutative `Ring A`. Star results
use its native involution. Complex grading uses `Algebra ℂ A` and the corresponding
star-module structure. Finite instances use full `Matrix n n ℂ`, never a
restricted diagonal carrier. Rectangular input is arbitrary `Matrix m n ℂ`;
normality and invertibility are not assumed. The Gram operators act on their
respective row and column spaces; for square input they need not coincide or
commute.

The bracket is Mathlib's native `⁅x,y⁆`, with `Ring.lie_def`. Compatibility is
native `Commute`. The pinned Mathlib has no `Anticommute` predicate, so the
anticommutation equation is stated explicitly; no replacement structure is
introduced. Native `Derivation` requires a commutative domain at this pin and
must not be misapplied to the matrix algebra.

Existing source owners:

- `InfoGeometry.Clifford.LorentzianBivectorSignatureBridge.positive_bivector_sq_neg_one`.
- `InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis.diracOperator`,
  `diracOperator₂`, `bochnerLaplacian₂`, `curvatureCommutator`, and
  `diracOperator₂_sq_weitzenbock`.
- `InfoGeometry.Krein.FiniteDiracGramSquare.dirac`, `qPlus`, `qMinus`,
  their nilpotency and adjoint relation, `dirac_sq`, `dirac_isHermitian`,
  and the native positive-semidefinite Gram results.
- `InfoGeometry.Core.PeirceGrading` owns parity multiplication and Peirce ranges;
  this change does not rebuild that API.
- `InfoGeometry.Core.AnticommutingSum.sum_square` owns finite anticommuting sums;
  its two-operator specialization supplies the source's mass-sum identity.
- Native `Algebra.commute_of_mem_adjoin_of_forall_mem_commute` and
  `Algebra.adjoin_le_centralizer_centralizer` own generated-algebra conservation.

The existing Clifford and Gram owners transitively import `Mathlib.Tactic`.
That inherited import cost is accepted to reuse their actual declarations;
new independent algebra files use focused native imports.

## Smallest missing statements

For `D = g*x+h*y`, the unrestricted two-generator target is

```text
D*D = x*x+y*y + (g*h)*⁅x,y⁆
  + g*⁅x,g⁆*x + g*⁅x,h⁆*y
  + h*⁅y,g⁆*x + h*⁅y,h⁆*y.
```

Its only special hypotheses are the three Clifford equations. The finite-family
version first separates ordered products from all mixed commutator defects.
The existing named endomorphism operators receive these stronger formulas.

An additional native operator bridge uses `LieAlgebra.ad R A` and
`Algebra.lmul R A`. Its contract is
`[ad a, lmul b] = lmul [a,b]`, with compatibility reflected by injectivity of
left multiplication. Combining this with the existing two-generator owner
produces a square identity for actual inner derivations. The associative
Leibniz rule is stated explicitly. Source search inspected the regular
commutant owner and the `ad/lmul`, `ad/mulLeft`, and inner-curvature surfaces;
the native adjoint/left-multiplication bridge was not found in that scope.

The grading branch proves the negative-square sign before constructing the
complex equal-square second charge. A rectangular block application reuses the
actual existing adjoint block operator. The Clifford application joins this
branch through the explicitly constructed grading.

Nonvacuity uses spin and coefficient tensor factors in the full matrix algebra.
Both spin generators are nondiagonal. Arbitrary matrix coefficients are allowed;
an explicit self-adjoint nondiagonal pair has nonzero commutator. Curvature
nonvanishing follows from invertibility of the bivector, rather than being a
second assumed conclusion. A separate counterexample rules out conservation
of the two summands by their sum.

A three-factor refinement uses the full eight-by-eight matrix algebra. Spin
acts on the first factor, the noncommuting coefficients on the second, and
spectator symmetries on the third. Its native joint centralizer contains two
explicit noncommuting matrices. This is an existence witness, not a general
double-centralizer classification.

## Proof-dependency partial order

The partial order is the transitive closure of the proof-use edges below.
Independent rows remain incomparable unless a listed theorem connects them.
Hypotheses are inputs, not unproved assertions promoted to theorems.

| Result node | Immediate mathematical proof inputs |
| --- | --- |
| Finite and two-term mixed expansion | Associative ring operations and finite-sum distributivity. |
| `clifford_sum_sq_with_defect` | `two_sum_sq_with_mixed_commutators` and the three Clifford equations. |
| `clifford_sum_sq` | The defect formula and four native `Commute` hypotheses. |
| Flipped-square extraction | `clifford_sub_sq`, its application of `clifford_sum_sq` to the negated coefficient, and additive cancellation. |
| `chiralMate_sq` | `grading_mul_sq_neg`, an involutive grading, an odd charge, and central complex scaling. |
| Constructed Clifford charge pair | Existing `positive_bivector_sq_neg_one`, `bivector_mul_clifford_sum`, `clifford_sum_mul_bivector`, and the generic `chiralMate_*` results. It does not use the compatible square formula. |
| Rectangular charge pair | Existing `FiniteDiracGramSquare.dirac`, native block multiplication, and the generic `chiralMate_*` results. It does not use the Clifford-specific grading. |
| Rectangular Gram positivity and kernel geometry | Existing adjoint block and Gram owners; native positive-semidefinite and `mulVec` operations. |
| `inner_dirac_sq` | `inner_ad_lmul_commute_iff`, native adjoint Lie-homomorphism laws, and the existing `KahlerDiracWeitzenbockSynthesis.diracOperator₂_sq_weitzenbock`. |
| Joint symmetry invariance | Native generated-subalgebra membership and `Algebra.commute_of_mem_adjoin_of_forall_mem_commute`, independently of any square identity. |
| Full-matrix square and charges | Tracked Pauli relations, native Kronecker multiplication, and the corresponding generic square and charge theorems. |
| Nonzero matrix curvature | `coefficientLift_injective`, a nonzero coefficient bracket, and `bivector_mul_ne_zero_iff`. |
| Hamiltonian noncommutation counterexamples | `matrixDirac_sq`, `matrixLaplacian_curvature_lie`, and the explicit nonzero nested coefficient bracket. |
| Noncommuting joint symmetries | `spinLift_commute`, `coefficientLift_commute`, native centralizer membership, and faithful double coefficient lift. |

The checker also records the exact repository import DAG. This source-level
graph is separate from the mathematical proof-use poset above.

## Acceptance contract

Separate roles: root generates/integrates; an independent mathematical auditor
checks scope and hypotheses; an independent acceptance reviewer checks the
exact final sources and decisive compiler evidence. Subagents write only new
sandbox candidates. All builds acquire `/tmp/info-geometry-build.lock`; no
concurrent compiler or destructive cache command is allowed.

Acceptance requires the complete repository import closure at the pins above,
native Lean checking, a declaration-complete transitive axiom audit allowing
only `propext`, `Classical.choice`, and `Quot.sound`, scoped placeholder and
semantic-vacuity scans, and the staged proof-proxy gate. The checker records
source and output hashes. The final report distinguishes this scoped check from
any unrelated repository-wide integration failures.
