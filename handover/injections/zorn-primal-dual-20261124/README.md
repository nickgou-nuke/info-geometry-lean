# From primal/dual Zorn coordinates to associative operators

**Current status: source-reviewed implementation; native validation pending.**
The first compiler attempt was terminated before completing a module. A retry
was stopped while waiting for the required shared build lock. No successful
kernel check or executed axiom-audit result is claimed at this checkpoint.
See `VALIDATION.md` for the observed results and the exact reproduction command.

This handover formalizes the supplied brainstorm on the repository's existing
real split-octonion carrier. The preserved source texts are provenance, not
proof certificates. `CONTRACT.md` states the intended results and corrections;
`SOURCE_REVIEW.md` records the independent mathematical review. Native checking
is performed by `verification/zorn-primal-dual/check.py` and its declaration
audit, with final results recorded separately.

## 1. Coordinates and dual evaluation

Write the existing Zorn vector matrix as

\[
 z=\begin{pmatrix}a&u\\v&b\end{pmatrix},
 \qquad N(z)=ab-u\cdot v.
\]

Its multiplication is the existing cross-product multiplication. In the
source structure the field order is `a,v,w,b`, so the displayed upper and
lower spatial vectors are represented by fields `v` and `w` respectively.

For two independent four-vectors define

\[
 X_+(x)=\begin{pmatrix}x_0&\vec x\\0&0\end{pmatrix},\qquad
 P_-(p)=\begin{pmatrix}0&0\\\vec p&p_0\end{pmatrix},\qquad
 Z(x,p)=X_+(x)+P_-(p).
\]

`ZornPrimalDual.encode` is a linear equivalence from the pair of four-vector
spaces onto the entire eight-dimensional Zorn space. The definition
`hyperplane p : Module.Dual ℝ (Fin 4 → ℝ)` is the actual covector

\[
 x\longmapsto\eta(x,p)=x_0p_0-x_1p_1-x_2p_2-x_3p_3.
\]

Thus `p` supplies the coordinates used to construct the covector through the
Lorentz pairing; no unstated identification with unsigned coordinate
evaluation is required. `norm_encode` states
\(N(Z(x,p))=\eta(x,p)\).

The full quadratic space has signature `(4,4)`. The source's four-dimensional
interpretations are restrictions:

\[
 N(Z(x,x))=x_0^2-x_1^2-x_2^2-x_3^2,
\]
\[
 N(Z(x,(x_0,-\vec x)))=x_0^2+x_1^2+x_2^2+x_3^2.
\]

These two section formulas are explicit Lean theorems. No projective quotient
or physical identification of the two coordinate slots is constructed.

## 2. Alternativity controls the operator passage

The existing native linear map

```lean
ZornLeftCAR.leftMultiplication :
  ZornVectorMatrix ℝ →ₗ[ℝ] Module.End ℝ (ZornVectorMatrix ℝ)
```

sends `z` to left multiplication by `z`. Its target multiplication is ordinary
composition. Existing polarized left alternativity gives

\[
 L_aL_b+L_bL_a=L_{ab+ba}
\]

for arbitrary Zorn elements. This does not assert \(L_aL_b=L_{ab}\).
Their difference evaluates to

\[
 (L_aL_b-L_{ab})(w)=a(bw)-(ab)w.
\]

The new chiral owner identifies the existing `leftMultiplication` and `L_map`
APIs pointwise; no new octonion carrier or replacement multiplication is used.

The chiral elements satisfy

\[
 X_+(x)^2=x_0X_+(x),\qquad P_-(p)^2=p_0P_-(p),
\]

and the same equations hold for their left operators. Spatial inputs therefore
give square-zero operators, and inputs with temporal coordinate one give
idempotent operators. An assertion about orthogonality or obliqueness requires
an additional inner-product comparison and is not part of these equations.

The exact mixed anticommutator is

\[
 \{L_{X_+(x)},L_{P_-(p)}\}
 =p_0L_{X_+(x)}+x_0L_{P_-(p)}-\eta(x,p)I.
\]

The two temporal terms are essential in general.

## 3. Clifford signs and chiral reconstruction

The existing imaginary-space owner constructs the native Mathlib map

```lean
splitOctonionLeftCliffordRepresentation :
  CliffordAlgebra leftCliffordQuadratic →ₐ[ℝ]
    Module.End ℝ CanonicalZorn
```

with `leftCliffordQuadratic = -det` on the trace-zero subspace. Its generator
law is \(L_v^2=-N(v)I\), giving four positive-square and three negative-square
directions in the source convention.

The seven-dimensional generator map is injective. The entire Clifford-algebra
map is not: its domain has real dimension 128 and its endomorphism target has
dimension 64. Existing theorems prove noninjectivity and a kernel dimension
of at least 64. The focused verification includes those existing owners.
Surjectivity onto all eight-by-eight matrices, irreducibility, and identification
of a particular simple summand are not added by this handover.

Let \(\Gamma=E_{11}-E_{22}\), while the supplied convention uses
\(q_7=E_{22}-E_{11}=-\Gamma\). Then

\[
 L_{E_{11}}=\tfrac12(I+L_\Gamma)=\tfrac12(I-L_{q_7}),\qquad
 L_{E_{22}}=\tfrac12(I-L_\Gamma)=\tfrac12(I+L_{q_7}).
\]

For \(q_i=V_i-U_i\) and \(q_{i+3}=U_i+V_i\),

\[
 L_{U_i}=\tfrac12(L_{q_{i+3}}-L_{q_i}),\qquad
 L_{V_i}=\tfrac12(L_{q_{i+3}}+L_{q_i}).
\]

The source-ordered product of the seven operators equals \(-I\).
The displayed composition-defect witness on the third split direction is
\(2\Gamma=-2q_7\), correcting the sign in the source draft.

## 4. Inverse, matrix determinant, and incidence

Conjugate contraction gives, in both orders,

\[
 L_{\bar z}L_z=L_zL_{\bar z}=N(z)I.
\]

The new inverse owner constructs an actual unit when \(N(z)\ne0\), with
inverse \(N(z)^{-1}L_{\bar z}\), and proves the converse. Negative split norm
is permitted.

The determinant owner gives an explicit eight-coordinate linear equivalence
and a matrix for this same left action. Its block form is

\[
 M_z=\begin{pmatrix}aI_4&B_z\\C_z&bI_4\end{pmatrix},\qquad
 C_zB_z=B_zC_z=(u\cdot v)I_4.
\]

A block determinant argument, including the zero-pivot case, gives

\[
 \det M_z=\det L_z=N(z)^4.
\]

The matrix/action identification is proved before transferring the determinant
formula to the native endomorphism. This is an actual determinant calculation,
not a definition of a determinant-like scalar.

Consequently

\[
 x\in\ker(\operatorname{hyperplane}(p))
 \iff\eta(x,p)=0
 \iff\neg\operatorname{IsUnit}(L_{Z(x,p)})
 \iff\det M_{Z(x,p)}=0.
\]

These equivalences include `p = 0`. The additional theorem
`hyperplane_ker_finrank` assumes `p ≠ 0` and proves dimension three. A
projective interpretation also needs nonzero point representatives and the
scalar-equivalence quotient.

## 5. Separate Souriau attachment

The first supplied text is handled on existing Souriau owners, without an
unproved bridge to Zorn geometry.

- The affine coadjoint action is bundled as a Mathlib `MulAction`; its functor
  from `SingleObj G` yields a native action groupoid via `Functor.Elements`.
  Nonempty hom sets are characterized by affine-orbit reachability.
- For the actual finite nonempty moment-map ensemble, the existing partition
  function is positive and `twistedMassieu` means `log Z`. The new theorem
  proves midpoint concavity of `-log Z`, with the inverse-cocycle shift.
- The affine pairing plus `log Z` is invariant under simultaneous transport.
  Identifying it as thermodynamic entropy additionally requires a mean or
  gradient constraint, which is not supplied here.
- For a skew bilinear form `B` and the convention
  \(\Omega=\nu_2(\xi_1)-\nu_1(\xi_2)+B(\xi_1,\xi_2)\), the graph
  \(\nu=cB(\xi,\cdot)\) has pullback \((1-2c)B\). The positive graph gives
  \(-B\); the negative graph gives \(3B\).

These are algebraic groupoid, finite-ensemble, and bilinear-form results.
Smoothness, closedness, nondegeneracy, symplectic multiplicativity, full
Legendre duality, and full concavity are outside the proved contract.

## Reproduction and integration

The root pins remain Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. With those dependencies available:

```bash
python3 verification/zorn-primal-dual/check.py --force
```

`--lean` and `--packages` may point to the pinned native compiler and an
existing dependency cache. The runner verifies the dependency revisions and
uses the maintained shared build lock. It writes only its own outputs under
`.lake/zorn-primal-dual`, and never changes dependency pins or shared caches.

The focused closure contains 38 repository modules. New-owner compilation
treats warnings as errors. The axiom audit inventories all declarations,
including private and generated declarations, from the six new owners and two
existing Clifford owners; only `propext`, `Classical.choice`, and `Quot.sound`
are permitted. This focused check does not certify the full repository build
or replace its pre-push gate. Public imports were added to `InfoGeometry.All`.
