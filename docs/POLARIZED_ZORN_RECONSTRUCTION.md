# Polarized Zorn: native multiplication, fundamental symmetry, and boundary coefficients

## Scope and verification

Source: `Pasted markdown(20260906-071112).md`, 381 lines. This document records
corrections to that source, not a transcription of its asserted verification.
The new extension is stacked on PR154 at
`96a5970762f5a9c1ea94a949a0cd0907782f8e35`. Existing files are not overwritten.

The seven new Lean files contain five theorem owners, an aggregate, and an audit.
There are 60 theorem declarations and 78 total declarations, with a native
`#print axioms` query for every declaration. All theorem statements have proof
scripts. These scripts have NOT been elaborated in the authoring environment.
The focused checker was actually invoked and exited 127 because `lake` is not
installed. No transitive-axiom or kernel certification is claimed.

The independent exact Python/SymPy suite passes 222 assertions, including a
symbolic identity in free noncommuting coefficients, all 64 scalar basis
products, matrix-coefficient regressions, and the scalar quadratic identities.
These checks are supplementary evidence, not Lean kernel proofs.

## Repository search: reuse before extension

Actual sources were inspected, rather than relying on old PR descriptions:

| Existing owner | Reused content |
|---|---|
| `Canonical/ZornVectorMatrixExplicit.lean` | Actual scalar Zorn carrier, multiplication, reduced norm, diagonal chirality, and genuine upper/lower square-zero theorems |
| `Physics/NCG/NoncommutativeChiralZornAlgebra.lean` | Existing noncommutative operator coefficients and ordered nonassociative Zorn multiplication |
| `Canonical/ThreeColorOperatorCrossCommutator.lean` | Ordered cross-product self-commutators, coordinate injections, native products, and the sufficient square-zero condition |
| `Canonical/OperatorZornCasimirNullIdentity.lean` | The existing ordered quadratic readout, without asserting it is a scalar composition norm |
| `Canonical/TwoSheetOperatorZornChannels.lean` | Existing complex matrix-coefficient specialization, not a replacement of Zorn multiplication by matrix multiplication |
| `Canonical/RealDoubledChiralKreinFrame.lean` | Genuine doubled state-space symmetry, chirality anticommutation, and Hilbertization; distinct from coordinate conjugation actions |
| `Clifford/Cl11Matrix.lean` | Existing real Pauli implementers and native Clifford representation |
| `Clifford/NeutralPhaseSpaceCore.lean` | Native quadratic carrier `E × E*` with `Q(x,f)=f(x)` |
| PR154 `Streaming/TwoBoundaryDyadCompression.lean` | Existing regular weak functional and normalized rank-one compression |

Default-branch reads resolve to the existing main snapshot
`b0fa422e6cb6d3da5be7cbbb5ecfae5c12f3237b`. The boundary bridge uses the pinned
PR154 snapshot above. This is a focused semantic source search, not an
exhaustive certification of the repository.

## 1. Eight coordinates versus ten coordinates

The source says split octonions are eight dimensional but supplies two
scalars and TWO four-vectors (source lines 52-58, 159-200). That is ten real
coordinates. The native Zorn carrier is

    (a,b,u,v),  u,v in R^3,   N=ab-u dot v.

The actual four-plus-four decomposition is

    (a,b,u,v) <-> ((a,u),(b,-v)).

Each sector contains one scalar plus THREE vector components. The native norm
is the pairing of these two null four-dimensional sectors.

The source's ten-coordinate quadratic expression is retained separately as
quadratic data, with no invented multiplication. Writing

    p=(a,U0,U1,U2,U3), q=(b,-V0,V1,V2,V3)

gives `Q=sum p_i q_i`. A genuine linear equivalence constructs these five-pair
coordinates, and evaluation by a native finite covector identifies Q with the
repository's unscaled neutral quadratic form. The difference-of-squares
normal form is proved. Finrank 10 excludes a linear equivalence with the
native eight-dimensional Zorn carrier. No four-dimensional binary cross
product or composition-algebra law is postulated.

## 2. Coordinate actions commute; the signed exchange is multiplicative

On the EXISTING operator-valued Zorn carrier, define

    K(a,b,u,v)=(a,b,-u,-v)
    S(a,b,u,v)=(b,a,v,u)
    F(a,b,u,v)=(b,a,-v,-u).

K, S and F are involutions, K S=S K, and F=S K. The source's anticommutation
statement at lines 335-345 is false; the extension contains an explicit
counterexample on an upper one-colour vector.

Neither K nor S preserves scalar Zorn multiplication: the product of two
different upper vectors provides a counterexample. In contrast,

    F(X*Y)=F(X)*F(Y)

holds even for arbitrary noncommuting coefficient rings, with the order of
every coefficient product retained. It is bundled as a native `MulEquiv`.
This does not assert that the ambient Zorn product is associative or
alternative for arbitrary operator coefficients.

These maps are not the standard octonionic conjugation: native conjugation
is `(b,a,-u,-v)`, without the off-diagonal exchange in F.

## 3. A genuine finite fundamental symmetry

For the native scalar Zorn norm, its normalized polar form is

    B(X,Y)=(a*d+b*c-u dot y-v dot x)/2.

The new source bundles B as a native bilinear form and proves

    B(X,F(Y))=(a*c+b*d+u dot x+v dot y)/2.

Therefore `B(X,F(X))` is half the sum of eight real squares, nonnegative and
zero exactly at X=0. F is an involutive real-linear norm isometry AND a
multiplication symmetry of this scalar Zorn model.

This supplies the exact finite fundamental-symmetry interpretation suggested
by the draft, but for F, not its off-diagonal sign K. The negative-norm
diagonal vector `(1,-1,0,0)` is fixed by K, obstructing positive
Hilbertization with K.

For the SOURCE ten-coordinate Minkowski-contraction layout, the analogous
signed exchange preserves Q but fails positive Hilbertization; a spatial
upper vector has polarized value -1/2. Thus one must not transfer positivity
between these two distinct carriers by reusing the name Zorn.

The scalar eight-coordinate signed exchange has determinant +1; the source
ten-coordinate map has determinant -1. These determinant signs are independently
checked exact finite-matrix consequences in the regression suite, not extra
Lean determinant declarations in this extension.

## 4. Nullness is not square-zero; operator coefficients expose the defect

The source's `chiral_rays_nilpotent` concludes only zero quadratic readout,
not a product equation. Its structure does not define multiplication at all.

The existing native operator product gives instead

    sigmaPlus(U)^2 = sigmaMinus(U cross U),
    sigmaMinus(U)^2 = sigmaPlus(-U cross U).

The new source upgrades the existing sufficient condition to equivalences:
these squares vanish if and only if the three coefficient commutators vanish.
For `U=(0,sigma3,sigma1)`, the ordered quadratic readout is zero but the
square contains `[sigma3,sigma1]` and is nonzero.

The scalar native diagonal idempotent `(1,0,0,0)` separately proves that zero
norm alone does not imply square-zero even in the genuine split algebra.
Coordinate projections also must not be confused with their values: the
projection onto a scalar slot is idempotent as a map, while the element in
that slot is idempotent only when its coefficient squares to itself.

## 5. Ordered operator norm versus traced invariant

For the existing ordered readout `C(X)=ab-sum u_i v_i`, the exact discrepancy is

    C(FX)-C(X) = [b,a] + sum [u_i,v_i].

It need not vanish. A finite matrix trace does kill it, giving

    Tr(C(FX))=Tr(C(X)).

The source proof retains both levels. It does not replace the operator-valued
readout with a commuting scalar in order to obtain the stronger false claim.

## 6. Clifford implementers versus their conjugation actions

The existing matrices K=sigma3 and S=sigma1 satisfy K S=-S K. Their product
has square -I. But conjugation by K and by S commutes, because the central
minus sign cancels. Conjugation by S K squares to identity.

Thus the valid Clifford relation is on the IMPLEMENTING two-state carrier,
not the source's coordinate actions. This is compatible with the repository's
already-proved anticommuting state-space sheet flip and chirality.

An involution on algebra coordinates is not an affine glide. It supplies no
translation, free deck group, quotient manifold, or torus double cover. F
fixes the algebra unit. No Klein-bottle or Dirac-Kahler theorem is claimed.

## 7. Boundary products are rank-one numerators

The product in source lines 17-20 has an exact role. For the rank-one probe
`A(x)=f(x)*v`, and an existing regular boundary pair,

    <post|A|pre> = <post|v> f(pre).

Its weak value is that product divided by `<post|pre>`, not divided by the
product itself. The extension connects this directly to the existing weak
functional and dyad compression. Zero and identity probes have different
weak values on the SAME boundary pair, so fixed boundary trace/norm data
cannot determine the whole probe-dependent functional.

The source's `weak_value_scalar_normalized` proves only `z/z=1` for z!=0.
It does not derive the preceding rank-one factorization or general weak
expectation from a Zorn norm.

## 8. Physical structures not supplied by these coordinates

A Weyl spinor and its vector bilinear transform in different representations.
A four-current is not itself a Weyl spinor. A two-by-two swap matrix, without
complex conjugation and standard-form data, is not a Tomita modular
conjugation. The latter's interpretation as geometric CPT requires additional
hypotheses. A Dirac-Kahler operator needs a differential/adjoint and grading
calculus, not only names for four fields.

For reference, David Tong's *Quantum Field Theory*, chapter 4, treats Weyl
representations and vector bilinears separately. Jonathan Sorce's *A short
proof of Tomita's theorem*, arXiv:2309.16762, states the von Neumann algebra
and cyclic-separating-vector setting. Neither is being used to insert a new
physical realization into the Lean definitions.

## Exact next boundary and execution

Run from the pinned repository root:

    bash scripts/check_polarized_zorn.sh

The checker builds the focused aggregate, executes all 78 axiom queries,
rejects missing reports, and permits only `propext`, `Classical.choice`, and
`Quot.sound`. It does not update the toolchain or dependencies.

After actual kernel diagnostics are resolved, a natural next theorem is to
transport this native scalar bilinear form and F into the repository's
completed doubled Krein/Hilbert carrier and certify the intertwining square.
A state-dependent Tomita construction remains a separate standard-form
problem; it is not supplied by that finite isometry alone.
