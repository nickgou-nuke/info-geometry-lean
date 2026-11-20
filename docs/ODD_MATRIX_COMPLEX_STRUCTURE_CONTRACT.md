# Odd outer matrix size and internal real complex structures

## Intake and provenance

This task continues upstream draft PR #417 at commit
`c9834db462b3798afef70c577ab19545e7e84b53`, tree
`1275cd88e581f184252b845e57bf51f2d23751e4`.
The user supplied a discussion of `A^2 = -I_3` over noncommutative rings and
requested the GitHub workflow in the ongoing formalization/publication task.
The intake is preserved at the end of this contract with normalized mathematical
typesetting. Its claims are proposals to audit, not proof authority.

## Corrected mathematical contracts

### Generic ring and characteristic two

Use native `Matrix`, `Matrix.scalar`, `Matrix.diagonalRingHom`, and unit
conjugation over an arbitrary associative unital `Ring R`.
Prove that a diagonal matrix squares to minus the identity exactly when every
coefficient does. Different diagonal roots need not commute. Scalar amplification
preserves the square law without centrality and reflects it for a nonempty index.
Use native unit conjugation to retain ordered products and actual inverses.

For any commutative ring and odd finite index cardinality, prove

\[
(\exists A\in M_n(R),\ A^2=-I)\iff(\exists j\in R,\ j^2=-1).
\]

Only this commutative section uses the ordinary determinant. Characteristic
zero alone is not an obstruction: the original table's category includes
fields with a square root of minus one. The examples R and Q without such a
root remain excluded.

In characteristic two, prove the complete elementary identity

\[
A^2=-I\iff(A-I)^2=0.
\]

Do not infer diagonalizability. The identity matrix is one solution.

### Real representation dimension and exact block classification

Reuse `LinearAlgebra.FiniteRealAnticommutation.even_card_of_square_eq_neg_one`
for necessity and `Quantum.Realification.internalJ_sq` for the even-dimensional
construction. Transport the latter through a native finite-index equivalence;
do not repeat the existing real determinant proof or define another phase axis.

Prove

\[
(\exists A\in M_n(\mathbb R),\ A^2=-I)\iff\operatorname{Even}(n),
\]

and use the actual `Matrix.compRingEquiv` to prove

\[
(\exists A\in M_m(M_k(\mathbb R)),\ A^2=-I)
\iff\operatorname{Even}(mk).
\]

At outer size three the criterion is exactly `Even k`. The dimension `mk` is
the real column-space dimension, not the algebra dimension `m^2 k^2`.
The zero-size case is legitimate. Include the even-dimensional real algebra
`R x R` as a counterexample to sufficiency of total algebra-dimension parity.
Do not claim a classification of all finite-dimensional real algebras from
these matrix results.

### Conjugation, infinitude, metric, and right-phase compatibility

Conjugation preserves the square law, but does not guarantee infinitely many
distinct conjugates. A central scalar matrix is fixed under conjugation, and a
finite ring has only finitely many matrices of any fixed size.
If an infinitude theorem is included, construct the actual shear family

\[
J_t=\begin{pmatrix}t&-(1+t^2)\\1&-t\end{pmatrix}
=P_tJ_0P_t^{-1},\qquad
P_t=\begin{pmatrix}1&t\\0&1\end{pmatrix},
\]

prove its square law and injectivity by the `(0,0)` entry, and impose an infinite
coefficient ring for infinitude. The formula is polynomial in one coefficient,
so it is meaningful in a general ring. For the real instance, `J_1` gives an
explicit square-minus-one matrix that is not orthogonal for the fixed metric.
Expose actual noncommuting matrix pairs: a shear unit and the phase over any
nontrivial coefficient ring, and two real phase roots with the second failing
fixed-metric orthogonality. These pairs establish the noncommutative content
on the native carriers used by the constructions.

Having a root of minus one does not make it central in the full coefficient
algebra or a phase commuting with every observable. Reuse the existing
`MatrixAmplification.scalar_commute_iff`. For column vectors over a real algebra,
right multiplication by the chosen root commutes with arbitrary left matrix
multiplication by associativity and finite distributivity. Keep this Hestenes
right action distinct from the left action of the scalar matrix `j I`.

### Actual coefficient-algebra examples

Consume the already proved native `Cl55InternalComplex.phaseBivector55_sq` in a
three-by-three matrix over the actual even Clifford algebra. No external complex
scalar is required for this construction.

For bounded operators, consume `Krein.clockAxis` on the actual real Hilbert
space `DoubledSpace E := WithLp 2 (E x E)`. Its square law and norm preservation
are already proved in the owner. Transfer it through an actual
`ContinuousLinearEquiv` using Mathlib's `conjContinuousAlgEquiv`, then form the
three-by-three matrix over the resulting continuous endomorphism ring.
A general continuous equivalence preserves boundedness and the square law,
not necessarily the fixed Hilbert metric.

The universal claim about every infinite-dimensional real Hilbert space
requires constructing a Hilbert self-doubling equivalence. If the relevant
native equivalence is not constructed here, record that step as open and report
the supplied-equivalence theorem as conditional. Do not generalize to arbitrary
operator subalgebras or real Banach spaces.

Native real quaternion examples may reuse existing quaternion axis owners after
checking their actual dependency closure. A mixed diagonal requires no pairwise
commutativity; its square law should consume the generic diagonal theorem.
Also construct two noncommuting square-minus-one matrices over the actual
three-by-three quaternion carrier from the existing quaternion axes.
A full quaternion conjugacy classification is a separate target.

## Source ownership and dependency order

Observed existing owners include `Algebra.MatrixAmplification`,
`Algebra.HypercomplexTriadMatrix`, `LinearAlgebra.FiniteRealAnticommutation`,
`Quantum.Realification`, `Clifford.GradedUnrollingCounterexamples`,
`Krein.DoubledSpace`, `Quantum.RealSplitClifford`, and the #417 native Clifford
phase owners. Native Mathlib supplies determinant identities, ring-equivalence
transport, matrix flattening/reindexing, characteristic-two algebra, and
continuous-operator conjugation.

Planned focused additions are `Algebra.MatrixSquareNegOne`,
`LinearAlgebra.RealMatrixSquareNegOne`, and
`Quantum.OperatorRingSquareNegOne`, with a small native quaternion consumer
only if its source closure is suitable. Dependencies follow actual imported
maps and proved square laws. No conceptual analogy is treated as an implication.

## Acceptance and limitations

Candidate generation, independent A-A mathematical review, and fresh QA are
separate contexts. All compiler/test execution is serialized under the shared
build lock. Preserve Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` and all maintained checkers/gates.
Check the new owners with zero compiler warnings, freshly compile their actual
repository import closure, and audit every owned declaration for the permitted
axioms `propext`, `Classical.choice`, and `Quot.sound` only. Retain raw static
heuristic outcomes and independently adjudicate any flags. Recheck root/package
and installed publication hooks separately; scoped compilation does not certify
whole-`All.lean` or the root workspace.

The finite-dimensional real-algebra ideal criterion, full quaternion conjugacy
classification, Dieudonne determinants, and arbitrary Hilbert self-doubling are
separate mathematical results. No Type III, full Clifford thermodynamic
representation, or physical heat-cycle closure follows from this ring theorem.

## Primary mathematical references

- V. Moretti and M. Oppio, [*Quantum theory in real Hilbert space: How the
  complex Hilbert space structure emerges from Poincare symmetry*](https://arxiv.org/abs/1611.09029),
  Proposition 2.23 and Remark 2.24: complex linearity relative to a chosen
  Hilbert complex structure requires commutation with that structure; the
  Hilbert-space existence criterion distinguishes finite odd dimension from
  finite even or infinite dimension. The latter general existence statement is
  contextual mathematics, not a theorem claimed by the supplied-equivalence
  operator owner here.
- M. Bresar and V. S. Shulman, [*On, Around, and Beyond Frobenius' Theorem on
  Division Algebras*](https://arxiv.org/abs/1912.07846), Theorems 2.1 and 3.1:
  Frobenius' division-algebra classification has finite-dimensional associative
  real hypotheses, and the general finite-dimensional real-algebra criterion
  for a root of minus one concerns dimensions of all ideals, not just the
  dimension of the whole algebra. Neither classification theorem is claimed
  as formalized by these elementary matrix owners.

The Lean proofs use the native owners named above. These references clarify
the mathematical boundaries; they are not added axioms or proof inputs.

## Preserved intake (normalized typography)

The user's passage states that a 3 x 3 matrix A over a general noncommutative
ring R can satisfy A^2 = -I_3 provided R contains elements behaving as imaginary
units. It says the usual determinant and eigenvalue proofs break down because
ordinary determinants no longer provide the same multiplicative map and scalars
do not commute.

1. Diagonal construction: if j in R satisfies j^2 = -1, take
   A = diag(j,j,j), yielding A^2 = diag(-1,-1,-1) = -I_3.
   Examples given are the quaternions H and M_2(R_real). With distinct roots,
   such as quaternion i,j,k, the passage proposes diag(i,j,k), then PAP^{-1}
   for invertible P, describing infinitely many non-diagonal solutions.
2. Finite-dimensional real algebras: for R = M_k(R_real), it identifies
   M_3(R) with M_(3k)(R_real), requires 3k even, hence k even. It says M_2(R_real)
   works and M_3(R_real) does not.
3. Infinite-dimensional operators: for R = B(H) on an infinite-dimensional
   Hilbert space such as L^2(R), it uses H isomorphic to H plus H to construct
   J^2 = -I and then a three-by-three solution.
4. Division algebras: it invokes Frobenius to list R_real, C, H as the
   finite-dimensional associative real division algebras, says C and H contain
   roots of minus one, and identifies R_real as the exception among these.
5. Comparison table: the row labeled "Commutative Field (Char 0)" gives R_real
   and Q as examples and says "No", because det(A)^2 = -1 has no solution.
   Quaternion and even-real-matrix-ring rows say "Yes"; the odd-real-matrix-ring
   row says "No"; the infinite-operator-algebra row says "Yes" by pairing.
6. Suggested extensions: full quaternion classification; positive
   characteristic, especially characteristic two where -1 = 1; and Dieudonne
   determinants for three-by-three matrices over noncommutative division rings.

The corrections and retained hypotheses above are explicit; this intake is not
silently promoted as a universally valid classification.
