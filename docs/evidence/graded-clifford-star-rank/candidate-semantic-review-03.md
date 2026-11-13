# Candidate source-semantic review 03

Reviewer: /root/graded_unroll_intake.

Scope: independent source-only review of the actual one-head untwisting rank
bridge, the constructed parity projections added to the rank owner, and the
ordered projector-defect candidate. No mathematical owner edits, Lean/Lake
execution, tests, or GitHub writes were performed by this reviewer.

## Exact reviewed identities

| Source | SHA-256 |
|---|---|
| graded-unroll-extension/lean/InfoGeometry/Clifford/Cl11UntwistCutRank.lean | e66706561dae1b754528be595d9b9d5b40f25890fdc4c767cc9d03fb9e8081f5 |
| graded-unroll-extension/lean/InfoGeometry/Clifford/GradedTensorCutRank.lean | 838bbd9bcd17a4b79a47d0051b0d83b20c760c2252c63be7c98adb42374e80f0 |
| candidates/graded_unroll/projector/Cl11GradedProjectorDefects.lean | 45fc8ec633695988a5d2ce0df4196685500801f777046373678a667660fc9724 |
| graded-unroll-extension/lean/InfoGeometry/Clifford/Cl11JordanWignerCARBridge.lean | 9f4acef0cb295e8936c2285b3dbf3b4d6cdb0576a28636db252ffa91a0a1c00d |
| graded-unroll-extension/lean/InfoGeometry/Clifford/Cl11TensorTower.lean | 1e08191d55b0c7827239332bcc9ba68b97d2c2004772d485ab0b19e2c00dc9ea |
| graded-unroll-extension/lean/InfoGeometry/Clifford/TowerMatrix.lean | 3489868cb323fad6ea3aed08cae00729cae4ec8f36e6da4ca42c460aa892876b |

All paths are relative to /workspace/scratch/9009f3c86480.

The final one-head bridge snapshot has 136 lines. The rank infrastructure has
337 lines. The final projector candidate has 272 lines. They were read in full.
The imported Jordan–Wigner/tower owners were inspected at the weight,
representation, basis image, string, Majorana, and index definitions actually
used by the candidate. This is a bounded dependency review, not a fresh
import-closure compilation.

Two earlier snapshots were seen during active authoring: one-head bridge
7478e413f6a1c491419bb79d71c323c7bfe4b252bde63ce7be727d70d9f153b3 and projector
b66dd23303016e031c1a418896456f74d622458c4a4f57df89e68bff1b09d7cb.
The verdict below applies to the final hashes in the table, including the
ordinary noncommutativity witness and normalized three-site scaling defect.

## Verdict

**No mathematical or source-semantic blocker found for these exact snapshots.**
This is source-semantic acceptance only. No kernel status, axiom footprint,
or repository integration status is certified here.

## Constructed parity projections

The rank owner now defines the real endomorphisms

\[
p_0=\tfrac12(\operatorname{id}+\theta),\qquad
p_1=\tfrac12(\operatorname{id}-\theta).
\]

It derives their sum, idempotence, and mixed-zero compositions from the
explicit condition θ² = id. The controlled map is then

\[
\operatorname{id}\otimes p_0+T\otimes p_1.
\]

This removes any need to supply the projector laws as unconstructed fields
when a parity operator is available. Involutivity and both cut-rank bounds
are inherited from the previously reviewed general controlled-map theorems.
The right factor remains unrestricted in dimension.

The new hypotheses are algebraic conditions on θ and T. They do not assume
the target tensor-map involutivity or its rank inequalities.

## Actual one-head untwisting bridge

The ordinary presentation is independently constructed from:

1. The faithful standard Clifford-to-real-matrix algebra equivalence.
2. Native ordinary tensor congruence and tensor-factor commutation.
3. The native matrix/tensor algebra equivalence over the complete coefficient
   algebra A.

No commutativity or finite-dimensionality of A is assumed. In the elementary
entry formula, only a real scalar coefficient is moved past an A element,
using the central real algebra action. Ordinary tensor-factor commutation
does not assert commutativity of multiplication inside either factor.

The graded presentation is the existing native tensorMatrixEquiv, built by
the graded tensor universal property and its explicit inverse. The bridge
does not define this equivalence to satisfy the desired rank relation.

The left map is actual right multiplication by the even Clifford volume
J1_cl. Its involutivity is proved from J1_cl² = 1 while retaining ordered
multiplication. The coefficient automorphism θ acts with the supplied native
grading signs; its involutivity is obtained from the existing coefficient
parity theorem, not added as an unrelated assumption.

The key coordinate identity is derived entrywise on all simple tensors,
including inhomogeneous coefficient elements, and then extended to every
native graded tensor by tensor induction. In the standard representation the
volume is Eplus, so right multiplication changes the second matrix column's
sign. The even/odd coefficient projections then give a in the first column
and θ(a) in the second, exactly matching the graded lift.

Consequently the two coordinates of the same matrix satisfy

\[
\operatorname{ordinary}^{-1}(\operatorname{graded}(z))
=C\big(\operatorname{underlying}(z)\big),
\]

where C is the constructed parity twist. Both rank inequalities now apply
to the actual one-head coordinate change. The finite-left hypothesis is
discharged by the faithful four-dimensional split Clifford representation,
so the rank-at-most-four corollary imposes no dimension condition on A.

The added ordinary_tensor_noncommuting result uses the preimages of the two
opposite elementary matrices. Its Nontrivial A hypothesis is appropriate.
It witnesses noncommutativity in the actual ordinary tensor algebra rather
than replacing that carrier with a commuting coordinate model.

This closes the one-head application gap noted in review 02. The header
accurately retains the remaining boundary: the owner does not identify every
cut of an iterated train, prove TT minimality, establish sharpness, or prove
fixed-total-parity rank invariance.

## Ordered projector defects

The universal two- and three-factor word identities use only associative ring
multiplication, generator squares equal to one, and pairwise anticommutation.
Their conclusions preserve the generator order:

\[
((1+x)(1+y))^2=2(1+x)(1+y),
\]

\[
((1+x)(1+y)(1+z))^2=4(1+x)y(1+z).
\]

The native specialization uses the real weighted quadratic form with three
positive and three negative directions. The positive elements are actual
Clifford images of distinct canonical basis vectors. Their square and
anticommutation laws are derived from the quadratic form and its polar form,
not postulated for surrogate scalar variables.

Each site element (1+e_i)/2 is proved idempotent. The pair and triple normalized
words are explicitly identified with the ordered products of these site
idempotents. The pair's square is one half of the pair. The triple's proposed
quarter-scaling has the explicit Clifford defect

\[
p_3^2-\tfrac14p_3
=\tfrac1{16}(1+e_0)e_1(1+e_2)
-\tfrac1{32}(1+e_0)(1+e_1)(1+e_2).
\]

This is exactly the n = 3 boundary found in the source intake audit.

The existing Jordan–Wigner algebra homomorphism maps the native generators
to the three-site Majorana matrices. Its target index has the complete
three-site spinor shape, with eight coordinates. The vacuum-entry evaluations
give one for the pair/triple words and zero for the middle word. They detect:

- Unnormalized triple scaling defect: −2.
- Pair non-idempotence defect: −1/8.
- Triple non-idempotence defect: −1/8.
- Normalized triple quarter-scaling defect: −1/32.

These separating values are nonzero. Therefore their preimage defects are
nonzero without requiring injectivity of the representation. Entry evaluation
is used only as a function to which equality may be applied; it is not claimed
to be an algebra homomorphism. Multiplicativity is used only for the genuine
Jordan–Wigner representation before taking an entry.

The source keeps the full ordered Clifford expressions before separation by
matrix entries. It does not replace the noncommutative problem by a scalar
calculation or assume the desired defect.

The formal carrier is the native weighted Cl(3,3) quotient. This owner does not
separately construct an all-length identification of iterated graded Cl(1,1)
tensors with weighted Clifford quotients, and its header makes the actual
carrier explicit.

## Outstanding acceptance

The current exact snapshots still require independent compilation and
owned-declaration axiom auditing. Any compiler-driven source changes require
hash-bound differential review. Integration/root gates and their failures
must remain distinct from the focused mathematical-source acceptance.
