# Real spacetime algebra, observer positivity, and right-phase signs

This development extracts finite algebraic claims from the supplied notes and
states the operator hypotheses needed for the second-iterate results. Its
carrier is the repository's existing native Mathlib Clifford algebra
`HestenesCl14.Cl14`, with real coefficients and signature `(+---)`:

\[
\gamma_0^2=1,\qquad \gamma_1^2=\gamma_2^2=\gamma_3^2=-1,
\qquad \gamma_\mu\gamma_\nu=-\gamma_\nu\gamma_\mu\quad(\mu\ne\nu).
\]

The [theorem contract](HESTENES_REAL_CL13_CONTRACT.md) records the original
source hash, base revision, existing owners, and acceptance requirements.
The source attachment is preserved verbatim at
`docs/sources/hestenes-real-cl13-intake-2026-11-17.txt`. Its narrative assertions
are input to review, not evidence of completed mathematics.

## Dependency order and actual carriers

The unchanged real dimension arguments now live in
`InfoGeometry.Canonical.HestenesCliffordDimension`; their original namespace
and declaration names remain available to the Pauli consumers. Native even
reversion similarly moves to `HestenesEvenReversion`, while the existing
observer adjoint remains owned by `HestenesHermitianAdjoint`. These narrower
imports let the new real development avoid depending on a complex matrix
realization for its algebraic construction.

The mathematical order is:

1. Native real Clifford generators and real dimension 16.
2. A real algebra equivalence with the full noncommutative quaternion matrix
   algebra, using explicit matrix preimages and finite-dimensional injectivity.
3. The primitive time projector and its native minimal left ideal of real dimension eight.
4. Coordinates for the entire native even algebra, including its multiplication,
   reversion, and observer adjoint.
5. A complete ordered Clifford basis and identification of its scalar coefficient.
6. The split reversion pairing, positive observer pairing, right phase, and
   two-plane inequality.
7. Actual right-coefficient square signs and conditional field-operator squaring.

The target of `cl13QuaternionEquiv` is

```lean
Cl14 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) (Quaternion ℝ)
```

Every quaternion matrix has an explicit Clifford preimage. The resulting
equivalence retains all sixteen real dimensions and the noncommutation of the
actual spatial generators. The codomain is neither a scalar surrogate nor a
restricted family of diagonal matrices.

The even-spinor equivalence is a **linear** equivalence

```lean
ClPlus14 ≃ₗ[ℝ] (Quaternion ℝ × Quaternion ℝ)
```

with the actual Clifford multiplication transported as

\[
(p,q)(r,s)=(pr-qs,\;ps+qr).
\]

It does not identify the Clifford product with the componentwise product on
`Quaternion ℝ × Quaternion ℝ`. Quaternion order is preserved throughout.

## The primitive projector and eight-dimensional minimal left ideal

The actual Clifford element `e = (1/2) • (1 + γ₀)` maps to the matrix unit
`E₀₀`. `RealSpacetimeIdeal` proves that it is a nonzero idempotent and uses the
native noncommutative left ideal

```lean
timeProjectorLeftIdeal : Ideal Cl14 := Ideal.span {timeProjector}
```

Membership is exactly the equation `x e = x`. Under the faithful quaternion
representation these are precisely the matrices with zero second column.
`timeProjectorLeftIdealEquiv` gives an explicit real linear equivalence with
`Quaternion ℝ × Quaternion ℝ`, and `timeProjectorLeftIdeal_finrank` proves
real dimension eight.

Minimality uses the full Clifford left action. Given a nonzero ideal element,
one of its first-column entries `q = ρ(x)ⱼ₀` is nonzero. The matrix with
entry `q⁻¹` at `(0,j)` and all other entries zero left-multiplies `ρ(x)` to
`E₀₀`. Lifting this matrix constructs a Clifford element `a` with `a x = e`.
Every nonzero left subideal therefore contains `e` and its entire principal
left ideal. `timeProjectorLeftIdeal_isAtom` records this minimality in the
native ideal lattice.

The same argument proves the explicit primitive-idempotent criterion:
if `f² = f`, `e f = f`, and `f e = f`, then `f = 0` or `f = e`.
This establishes the particular projector's primitivity without asserting a
classification of every Clifford idempotent or module.

## Scalar coefficient and the sixteen blades

`RealSpacetimeBlades.bladeBasis` is a basis of the full native Clifford algebra,
in this order:

\[
1,\ \gamma_0,\ \gamma_1,\ \gamma_2,\ \gamma_3,
\ \gamma_{01},\ \gamma_{02},\ \gamma_{03},
\ \gamma_{12},\ \gamma_{13},\ \gamma_{23},
\ \gamma_{012},\ \gamma_{013},\ \gamma_{023},
\ \gamma_{123},\ \gamma_{0123}.
\]

The construction uses a full dual-pairing table to prove independence and the
native real dimension theorem to prove spanning. `scalar_eq_bladeBasis_repr_zero`
identifies the normalized real quaternion trace with the coefficient of `1`
in this basis. Thus the later scalar products use the actual Clifford scalar
coefficient, rather than an unverified matrix readout.

| Basis blades | Number | Square |
|---|---:|---:|
| `1`, `γ₀` | 2 | `+1` |
| `γ₁`, `γ₂`, `γ₃` | 3 | `−1` |
| `γ₀₁`, `γ₀₂`, `γ₀₃` | 3 | `+1` |
| `γ₁₂`, `γ₁₃`, `γ₂₃` | 3 | `−1` |
| `γ₀₁₂`, `γ₀₁₃`, `γ₀₂₃` | 3 | `−1` |
| `γ₁₂₃` | 1 | `+1` |
| `γ₀₁₂₃` | 1 | `−1` |

The exact negative-square index set is
`{2,3,4,8,9,10,11,12,13,15} : Finset (Fin 16)`, and its cardinality is ten.
The attachment incorrectly puts the three time-space **bivectors** in this
negative group. The missing three are time-plus-two-space **trivectors**.
The number ten counts this basis subset; it does not count all elements of the
algebra that square to `−1`.

## Two distinct real pairings

For even spinors, write `x ↦ (p,q)` and `y ↦ (r,s)`, and let the quaternion
dot product be the usual dot product of all four real coordinates. The forms
are defined intrinsically before their coordinate formulas are derived:

\[
K(x,y)=\langle x\widetilde y\rangle_0,
\qquad
G(x,y)=\langle x\gamma_0\widetilde y\gamma_0\rangle_0.
\]

Their complete normal forms are

\[
K(x,y)=p\mathbin{\cdot}r-q\mathbin{\cdot}s,
\qquad
G(x,y)=p\mathbin{\cdot}r+q\mathbin{\cdot}s.
\]

Because the coordinate map is onto the entire pair of quaternions, the first
formula gives four positive and four negative real directions. The second
gives a positive-definite real bilinear form on all eight even-spinor
coordinates. The zero-norm equivalence and strict positivity for nonzero
spinors are explicit theorems.

The observer conjugation is the actual Clifford operation
`θ(x) = γ₀ x γ₀`, with coordinates `(p,−q)`, and satisfies
`K(x, θ(y)) = G(x,y)`. The algebraic current has time coefficient

\[
\langle x\gamma_0\widetilde x\gamma_0\rangle_0=G(x,x).
\]

This is a finite algebraic identity. Current conservation and causal
propagation require additional differential statements. The positive form is
attached to the chosen observer; fixed-observer Lorentz invariance is not
asserted.

The indefinite Cauchy–Schwarz claim has a closed counterexample: the two
spinors with coordinates `(1,1)` and `(1,−1)` have zero self-pairings under `K`
and cross-pairing `2`. Nondegeneracy of `K` therefore does not give a positive
inner-product inequality.

## Right phase and the two-plane inequality

Let `B = γ₂γ₁` and `J(x) = x B`, using the actual even Clifford product.
The development establishes

\[
B^2=-1,\quad J^2=-\operatorname{id},\quad
G(Jx,Jy)=G(x,y),\quad G(Jx,y)=-G(x,Jy),\quad G(x,Jx)=0.
\]

The left/right compatibility is ordinary associativity:
`J(a x) = a J(x)`. It does not require that `B` commute with `a` or `x`.
Plain left multiplication likewise commutes with plain right multiplication
by the pseudoscalar. Anticommutation of the pseudoscalar with vectors is a
different assertion.

With the explicit normalization

\[
\Omega(x,y)=2G(Jx,y),
\]

the alternating and nondegeneracy identities and the bound are

\[
G(x,y)^2+\frac{\Omega(x,y)^2}{4}\le G(x,x)G(y,y).
\]

`omegaForm` exposes this pairing as a native `LinearMap.BilinForm` over the
reals. Its `IsAlt` and `Nondegenerate` theorems establish alternation and both
left and right separation at that interface.

The proof takes the nonnegative observer norm of the explicit residual

\[
r=G(x,x)y-G(x,y)x-G(Jx,y)Jx.
\]

Its expansion gives
`G(r,r) = G(x,x) (G(x,x)G(y,y) − G(x,y)² − G(Jx,y)²)`.
The zero-spinor case is handled separately, without division by a possibly
zero norm. Changing the definition of `Ω` changes the coefficient in the
displayed inequality; the factor `1/4` is part of this contract.

## Pseudoscalar substitution and the mass factor

Write `I = γ₀γ₁γ₂γ₃` and `σ₃ = γ₃γ₀`. The actual Clifford identities are

\[
(\gamma_0B)^2=-1,\qquad (\gamma_0I)^2=+1,
\qquad (\gamma_3I)^2=-1,
\]

and

\[
B\sigma_3=I,\quad I\sigma_3=B,\quad
\gamma_0\sigma_3=-\gamma_3,\quad
\gamma_3\sigma_3=-\gamma_0.
\]

Consequently the pointwise equation has the exact two-way transformation

\[
aB=m\psi\gamma_0
\quad\Longleftrightarrow\quad
aI=-m\psi\gamma_3.
\]

No invertibility or normalization of `ψ` is assumed. This corrects the
attachment's blanket conclusion that a pseudoscalar formulation is impossible.
Replacing `B` by `I` while keeping the time mass factor unchanged gives a
different equation.

`RightPhaseDynamics.second_iterate_of_right_mass_equation` is deliberately
general: for a real-linear operator `D` on algebra-valued functions, a fixed
right coefficient `C`, and explicit hypotheses

\[
D(fC)=D(f)C,\qquad C^2=s1,\qquad D\psi=m\psi C,
\]

it concludes `D(D ψ) = s m² ψ`. The three spacetime applications therefore give:

| First-order equation | Relevant coefficient square | Second iterate |
|---|---:|---:|
| `(Dψ) B = m ψ γ₀` | `(γ₀B)² = −1` | `D²ψ = −m²ψ` |
| `(Dψ) I = m ψ γ₀` | `(γ₀I)² = +1` | `D²ψ = +m²ψ` |
| `(Dψ) I = −m ψ γ₃` | `(γ₃I)² = −1` | `D²ψ = −m²ψ` |

Each theorem states compatibility with its own actual right coefficient.
The code does not construct a differential operator or identify its square
with a wave operator.

## Interpretive corrections and open claims

The choice of a fixed right bivector alone does not establish physical
rotational anisotropy. Hestenes explicitly treats covariance of the real
Dirac equation with fixed reference elements in
[Real Dirac Theory (1996), §2](https://davidhestenes.net/geocalc/pdf/REAL_DIRAC.pdf).
That physical covariance statement is supporting literature, not a theorem
claimed by these finite algebra modules.

The full real `Cl(1,3) ≃ M₂(ℍ)` construction and the particular minimal ideal
do not prove a complete classification of the opposite-signature algebra,
every Clifford module, or charged-Majorana doubling. Charge and Majorana
representation claims require a stated
commutant, module action, and gauge compatibility; they do not follow merely
from an eight-dimensional real space or its split pairing.

Fourier inversion, uniqueness of a phase choice, electromagnetic squaring,
PDE existence, current conservation, and causal propagation also remain
outside the established finite algebraic chain.

## Reproducible verification scope

`tools/quality/hestenes_real_cl13_scope.json` names the core audit targets,
legacy consumer regression targets, and changed consumer owners. The focused
workflow uses the repository's exact Lean and Mathlib pins, fresh copied
source closures, native Lean compilation, and a complete owned-declaration
axiom audit for the core. It separately compiles the existing consumers that
depend on the moved declarations and narrowed imports.

The scoped resolver explicitly supports the root `proofs.*` library, whose
Lake source root is the repository root. Other checker callers retain their
original source-root policy. Reports record each original repository path,
source hashes, dependency fingerprints, compiler results, and helper hashes.

Core acceptance requires every audited target, zero warnings in every changed
Lean owner, permitted foundational axioms only, complete placeholder and
semantic coverage, and independent audit and acceptance. The consumer run is
compilation-only; it is not mislabeled as a full historical axiom audit.
Focused verification does not certify the root package or its external path
dependencies. Actual run results belong to the PR and its attached evidence.
