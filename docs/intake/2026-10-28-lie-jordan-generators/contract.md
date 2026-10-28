# Real operator generators: ground-truth theorem contract

## Frozen intake and authoritative carriers

The two streams are preserved verbatim and in input order beside this contract.
Their hashes, byte counts and upload provenance are in provenance.json. Embedded
claims of successful verification are intake, not verification evidence.
This extension starts at PR #253 head
`adc916d7a8e9370401251901156ae8551ed01d39`, with Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` unchanged.

Use full associative unital algebras and native `Module.End R A`,
`LieAlgebra.ad`, the existing unnormalized `jordanLeft`, and
`LinearMap.mulLeftRight R (a,b)`. The concrete geometric and counterexample
carriers are full `Matrix n n ℝ`, with real scalars and no complexification.
There is no ambient commuting or diagonal restriction.

The symbols below are mathematical notation, not new custom carrier types:

- `D_a(x)=ax-xa`, `J_a(x)=ax+xa`, `S_ab(x)=axb`.
- `K=ab+ba`, `C=[a,b]`, `PhiPlus=S_ab+S_ba`, `PhiMinus=S_ab-S_ba`.
- For an idempotent `p`, use the existing Peirce corners and `gamma=reflection p`.
- `Gsym=-(D_a D_b+D_b D_a)`.
- `Gplus=D_a J_b-D_b J_a`.
- `Gminus=-(J_a D_b-J_b D_a)`.

The three generators may be bundled once as native endomorphisms, with their
proofs and consumers using those definitions. Do not redefine the commutator,
Jordan multiplication, sandwich maps, trace, inner product, Peirce grading or
single-jump dissipator.

## Source corrections and exact scope

1. Seven octet identities and both pure-composition projections already have
   native owners. Add only the missing Jordan–Lie difference and its two mixed
   projections. The six ordered monomial patterns are not a basis at arbitrary
   matrix evaluations.
2. The second stream switches between two different skew generators. The exact
   expansions are `Gplus=2 PhiMinus+J_C` and `Gminus=2 PhiMinus-J_C`.
   The former annihilates ordinary trace but sends `1` to `4C`; the latter
   annihilates `1` and the reflection-weighted trace but has ordinary trace
   `-4 Tr(CX)`. Keep both operators and both trace functionals distinct.
3. Generator trace annihilation means `Tr(G X)=0`. It does not mean
   `Tr(G X)=Tr X`. Generator identity annihilation means `G 1=0`, not `G 1=1`.
4. `V=1-K` has defect `V²-V=K²-K`. Opposite-corner support implies
   `Gsym V=Gminus V=0`, but `Gplus V=4 C(1-K)`.
   Over real algebras, `Gplus V=0` is equivalent to `K²=K`, hence to `V²=V`.
5. A signed difference of jump terms does not inherit a positive-semigroup
   conclusion. Prove actual full-matrix positivity obstructions. If a curve is
   exhibited, verify its operator differential equation and initial condition;
   do not infer an unproved exponential or classification theorem.
6. Positive Frobenius geometry uses the real transpose adjoint explicitly.
   For a real symmetric idempotent `p`, the reflection metric `gamma` is
   symmetric and involutive. Its Krein adjoint is
   `X ↦ gamma*X.transpose*gamma` and is distinct. In particular an odd
   corner has `U sharp = -U.transpose`.
   A reflection-weighted trace is not an inner product or that adjoint.

## Source-confirmed owners

- `Core.JordanMultiplicationClosure.jordanLeft` is the unnormalized native
  endomorphism. The similarly named normalized Jordan owner is not substituted.
- `Core.LieJordanBoundaryOperators` owns both mixed sums, the Lie–Jordan swapped
  difference, both pure symmetric compositions, their two projections and the
  exact square obstructions. Extend this owner with the three missing formulas.
- `Core.LieJordanComposition.jordan_jordan_bracket` owns the Jordan commutator.
  Native `LieHom.map_lie` applied to `LieAlgebra.ad` owns the adjoint commutator.
- `Core.PeirceCoupledCorners` owns support, quadratic compressions and reflection
  duality. `Core.PeirceQuadraticFrame` owns the specified quadratic centralizers
  and `C²=K²`; `Core.PeirceGrading` owns actual even/odd ranges and reflection.
- `Canonical.LieJordanSandwichGeometry` owns the generic symmetric sandwich
  trace and parity formulas. Those generic theorems apply to real matrices.
- `Modular.GKSL.dissipatorTerm`, in `Modular.GKSLDissipatorAlgebraic`, owns the arbitrary-star-ring
  Heisenberg-oriented term `star V*X*V-half*(star V*V*X+X*star V*V)`.
  It is real-compatible and has a two-module repository closure. Reuse it for
  paired-sum and signed-difference bridges, with its orientation explicit.
- `Canonical.TomitaTakesakiKMSEntropyBracket` already owns the real pointwise
  Schrodinger-oriented single-jump formula and zero trace. It was read; it has
  a twenty-module repository closure. No duplicate single-jump definition is
  introduced. The complex-specific `Modular.SchrodingerGKSL` is not the new
  carrier for this real development.
- `HodgeCohomology.HodgeDirac.laplacian_energy` and
  `harmonic_iff_closed_and_coclosed` apply to any adjoint pair of native real
  linear maps. Neither theorem assumes square-zero. Use them after proving
  the actual matrix adjunction; do not invoke neighboring nilpotence results.
- Native `Matrix.toMatrixNormedAddCommGroup` and
  `Matrix.toMatrixInnerProductSpace` supply the Frobenius geometry directly
  on full real matrices. Native `LinearMap.adjoint`, `IsSymmetric`, kernels,
  ranges and orthogonal complements remain the operator/geometric interfaces.

## Exact implementation plan

### Extend Core.LieJordanBoundaryOperators

For arbitrary `[CommRing R] [Ring A] [Algebra R A]`, add:

`J_a D_b-J_b D_a=J_[a,b]-2(S_ab-S_ba)`;

the sum of the two swapped differences equals `2 J_[a,b]`; their difference
equals `4(S_ab-S_ba)`. Reuse existing row seven for the two projections.

### Core.PeirceSandwichDuality

For `p²=p`, `u in pA(1-p)`, `v in (1-p)Ap`, prove the native left-reflection
intertwining equations for both sandwich maps. Also prove the input-reflection
equations `PhiPlus(gamma*X)=-PhiMinus X` and
`PhiMinus(gamma*X)=-PhiPlus X`. Derive equality of native kernels and ranges,
actual even image and annihilation of the actual odd range. Retain arbitrary
characteristic and use existing support/parity owners.

### Core.LieJordanGenerators

Construct only the three native endomorphisms `symmetricGenerator`,
`skewPlusGenerator`, `skewMinusGenerator` as the compositions stated above.
Prove their exact sandwich expansions and their values on `1`. For opposite
corners derive their values on `p`, `K`, `C`, and `1-K` as needed by the source
and real boundary witnesses. In particular prove `Gplus p=2C`, `Gplus C=0`,
the universal idempotence defect and the exact stationarity criterion.
Any cancellation of four must have an explicit valid characteristic hypothesis;
the concrete real specialization must discharge it.

### Canonical.LieJordanGeneratorTrace

Prove skew-sandwich trace transport on arbitrary finite full matrices, then
the ordinary and reflection-weighted trace table:

| Operator | Ordinary trace at X | Reflection-weighted trace at X | Value at 1 |
| --- | --- | --- | --- |
| Gsym | 0 | -4 Tr(CX) | 0 |
| Gminus | -4 Tr(CX) | 0 | 0 |
| Gplus | 0 | 4 Tr(KX) | 4C |

Only the weighted column needs opposite-corner support. Use native trace and
native linear maps; expose genuine functional annihilation interfaces where
useful. Bridge the transpose-paired sum and the appropriate signed difference
to the existing real-compatible algebraic dissipator owner, respecting its
Heisenberg orientation: for `v=u.transpose`, `Gsym=2(T_u+T_v)` and
`Gminus=2(T_v-T_u)`. No positive-rate conclusion follows for the difference.

### Canonical.RealLieJordanGeometry

For arbitrary full real matrices, install the native Frobenius structure
locally, with inner product `Tr(X.transpose*Y)`. Prove
`(ad_u).adjoint=ad_(u.transpose)` and consume the existing adjoint-pair energy
and common-kernel owners to establish:

with `Gsym=symmetricGenerator u u.transpose`,
`inner X (Gsym X) = -(norm (ad_u X)^2 + norm (ad_(u.transpose) X)^2)`;

native symmetry, negative quadratic form, the kernel equal to the intersection
of the two adjoint-action kernels, and the resulting common-centralizer and
range/orthogonal-complement geometry. These results need no Peirce hypothesis.
Keep positive-semidefinite preservation of a matrix-valued map distinct from
quadratic-form positivity of a linear operator on the Frobenius space.

### Canonical.RealLieJordanExamples

Define dense P,S,U directly over real full 3-by-3 matrices, with P's entries
1/3, S=[[1,2,3],[2,4,5],[3,5,6]], and U=component10 P S. Prove the required
support, transpose and noncommutation facts directly in this real carrier.
Prove nonzero defects for `1-K` idempotence, its skew-plus stationarity,
skew-plus identity annihilation and skew-minus ordinary trace annihilation.
Use a real matrix quadratic-form probe to certify failure of positivity of
the skew sandwich and the affine generator orbit from P. Verify any claimed
curve equation using native calculus. State the reflection-metric transpose
readouts explicitly if used; never identify that Krein adjoint with transpose.

## Prerequisite partial order and acceptance

Native associative compositions -> complementary swapped difference -> exact
generator expansions. Existing idempotent support -> sandwich reflection
intertwiners -> native kernel/range geometry. Support and quadratic centralizers
-> exact stationary-element and idempotence criteria. Native cyclic trace and
reflection intertwiners -> distinct trace-annihilation laws. Native real matrix
Frobenius structure and actual adjunction -> existing adjoint-pair energy theorem
-> kernel/common-centralizer and range geometry. The algebraic and trace
branches feed the dense real matrix witnesses; native matrix topology supplies
their curve calculus. The Frobenius geometry is a separate consequence of the
same generators. Edges are proof prerequisites.

Acceptance requires complete Lean proofs, strict target warnings, source-hash
reconciliation, constructivity/proof-proxy scans, exhaustive native ownership
and axiom inspection, an isolated native Lake build, independent semantic
review and independent artifact acceptance. Only `propext`, `Classical.choice`
and `Quot.sound` are permitted foundational axioms. All stronger interpretation
claims remain outside the accepted scope until separately formalized.
