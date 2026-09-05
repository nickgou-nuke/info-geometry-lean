# The split `O(5,5)` contact multigrading

## Scope

This development constructs the finite-dimensional real Lie algebra attached
to an explicit split quadratic space of signature `(5,5)`.  It then proves a
contact `|2|`-grading, a source/target block bigrading, the induced mod-two
parity, a five-pair Witt decomposition, projective boundary selection rules,
a faithful common CAR--CCR operator representation, and compatibility
readouts with the repository's existing `Pin(5,5)` lane.

The construction does not identify all earlier five-graded objects in the
repository.  In particular, the generic Freudenthal/symplectic contact Lie
algebra and this split-orthogonal contact Lie algebra are different carriers.
An equality or isomorphism would require an explicit map preserving the
bracket and grading.

Public entry point:

```lean
import InfoGeometry.Orthogonal.O55ContactAll
```

## 1. Split quadratic carrier

The real vector space is

```text
V55 = Fin 10 -> R.
```

Coordinates are grouped as

```text
E_minus  direct-sum  W  direct-sum  E_plus
   2                    6                 2
```

with quadratic pairing

```text
B(x,y) = x0*y8 + x1*y9 + x8*y0 + x9*y1
       + x2*y2 + x3*y3 + x4*y4
       - x5*y5 - x6*y6 - x7*y7.
```

The code proves symmetry and nondegeneracy.  It constructs five explicit
positive and five explicit negative directions, certifying signature `(5,5)`.

The infinitesimal orthogonal algebra is the native Mathlib `LieSubalgebra`

```text
so55 = { A in End_R(V55) |
         B(Ax,y) + B(x,Ay) = 0 for all x,y }.
```

Closure under the commutator is proved directly in the associative
endomorphism algebra.  No split-octonion multiplication is used to justify
Lie closure.

## 2. Contact Euler element and five-grading

The vector weights are

```text
-1, -1, 0, 0, 0, 0, 0, 0, +1, +1.
```

Let `H` be the diagonal Euler endomorphism with those weights.  It belongs to
`so55`, and

```text
H^3 = H.
```

For every integer `k`, define

```text
g_k = { A in so55 | [H,A] = k A }.
```

The code packages each `g_k` as a native real `Submodule`.  Jacobi in the
associative endomorphism algebra gives

```text
[g_k,g_l] subset g_(k+l).
```

The only vector weights are `-1,0,+1`, so the source/target weight differences
are `-2,-1,0,+1,+2`.  Explicit nonzero rank-two generators inhabit all five
lanes.

Every `A : so55` has a proved exact decomposition

```text
A = A_(-2) + A_(-1) + A_0 + A_(+1) + A_(+2),
```

where each summand is proved both split-skew and homogeneous of the displayed
degree.

## 3. Source/target block bigrading and parity

The three vector-weight projectors resolve the identity and are pairwise
orthogonal.  For a source/target pair `(t,s)`, define

```text
A_(t,s) = P_t A P_s.
```

The code proves

```text
[H,A_(t,s)] = (t-s) A_(t,s).
```

Mismatched adjacent blocks multiply to zero, while matching block composition
adds degree.  The nine blocks reconstruct every endomorphism.

The contact degree is reduced modulo two to obtain parity:

```text
parity(A_k) = k mod 2.
```

Thus the branch carries both the full integer contact grading and its
superalgebra parity shadow.  They are not identified.

## 4. Heisenberg radicals

Let `E_minus` and `E_plus` be the two-dimensional outer spaces and let `W`
carry the middle `(3,3)` form.  Rank-two generators give

```text
g_(-1) = E_minus wedge W,
g_(+1) = E_plus  wedge W,
g_(-2) = Lambda^2 E_minus,
g_(+2) = Lambda^2 E_plus.
```

For outer vectors `a,b` and middle vectors `w,z`, the proved same-sign bracket
is

```text
[X_-(a,w), X_-(b,z)]
  = -B_W(w,z) area(a,b) E_(-2),

[X_+(a,w), X_+(b,z)]
  = -B_W(w,z) area(a,b) E_(+2).
```

The extreme lanes centralize their corresponding degree-one lanes and are
abelian.  Hence each nilpotent radical is exactly two-step Heisenberg-shaped.
Mixed degree-one brackets are proved to land in `g_0`.

## 5. Degree-zero structure

The coordinate degree-zero generators split into two commuting families:

```text
E_minus wedge E_plus,
Lambda^2 W.
```

The first obeys the matrix-unit bracket of a `gl(2)`-shaped action.  The
second obeys the standard rank-two orthogonal bracket of the middle split form,
a `so(3,3)`-shaped action.  Their mutual commutator is zero, and both actions
on `g_(-1)` and `g_(+1)` are proved explicitly.

The development deliberately stops short of declaring a native Lie
isomorphism

```text
g_0 isomorphic to gl(2,R) direct-sum so(3,3)
```

until a basis-level map and inverse are constructed.

## 6. Coordinate-generator census

A finite coordinate label type has exactly 45 inhabitants, partitioned by
contact degree as

```text
1, 12, 19, 12, 1.
```

Every label maps to a theorem-certified homogeneous rank-two generator.  The
sum is 45, matching `dim so(5,5)` and the existing repository count.

This is an exact generator census.  It is not advertised as a basis or a
finrank theorem.  The remaining linear-algebra frontier is to prove linear
independence and spanning grade by grade and package

```text
finrank g_(-2) = 1,
finrank g_(-1) = 12,
finrank g_0    = 19,
finrank g_(+1) = 12,
finrank g_(+2) = 1.
```

## 7. Five Witt pairs and two sheets

The carrier also has five normalized hyperbolic pairs

```text
(n_i, nbar_i), i in Fin 5,
```

with

```text
B(n_i,n_j)       = 0,
B(nbar_i,nbar_j) = 0,
B(n_i,nbar_j)    = delta_ij.
```

Explicit coefficient formulas reconstruct every vector from the ten null
vectors.  A full label records

```text
(contact degree, parity, Witt index, sheet).
```

These components are simultaneous labels, not a claim that Witt index and
contact degree are the same grading.

## 8. Crosscap and Pin readouts

The matrix crosscap exchanges the two outer sectors and fixes the middle
sector.  It is an involutive split isometry and satisfies

```text
R H R = -H.
```

Conjugation by `R` is a Lie automorphism of `so55` and reverses contact degree:

```text
R g_k R = g_(-k).
```

It also reverses source/target block weights and preserves mod-two parity.

The repository already owns an independent Clifford/Pin construction in
`proofs/PinO55GlideReflection.lean`.  The bridge reuses its exact facts:

```text
carrier count = 10,
Lie-generator count = 45,
orientation sign = -1,
Pin crosscap exchanges n and -nbar,
glide conjugates a torus translation to its inverse,
glide squared is a translation on the orientable double cover.
```

The matrix and Clifford lanes are stated side by side.  No unproved linear or
Clifford-algebra equivalence between their concrete carriers is inserted.

## 9. Projective two-boundary selection

For a nonzero vector/covector incidence `(f,v)`, define

```text
omega_(f,v)(A) = f(A v) / f(v).
```

The code proves linearity, invariance under independent nonzero rescaling of
`f` and `v`, and the normalized rank-one compression law

```text
P A P = omega_(f,v)(A) P.
```

If `v` has Euler weight `a`, `f` has dual Euler weight `b`, and `A` has contact
degree `k`, then

```text
(b-a-k) f(A v) = 0.
```

Consequently a nonzero matrix coefficient requires

```text
b-a = k.
```

This is the exact selection rule.  It is representation theory, not a claim
about a physical pre/post-selected experiment.

Simultaneously transforming both boundaries and the operator by the crosscap
preserves the normalized readout while reversing all three integral weights.

## 10. Common CAR--CCR operator envelope

The doubled carrier

```text
V55 x V55
```

supports the exact one-mode CAR operators

```text
a(x,y)       = (y,0),
a_dagger(x,y)= (0,x),
a^2 = 0,
(a_dagger)^2 = 0,
a a_dagger + a_dagger a = 1.
```

The orthogonal Lie algebra acts diagonally and faithfully on both sheets.
This action commutes with `a` and `a_dagger`.

On the countable algebraic occupation carrier

```text
N -> (V55 x V55),
```

weighted left shift and right shift obey the exact algebraic CCR

```text
A C - C A = 1.
```

The pointwise `so55` action is a faithful native `LieHom`, commutes with both
bosonic ladder maps, and preserves every contact grade.  A lifted crosscap
intertwines source grade reversal with represented grade reversal and commutes
with all four ladder operators.

No Hilbert completion or unbounded-operator domain is claimed by this
algebraic construction.

## 11. Relation to the parent Freudenthal contact branch

The parent branch constructs a faithful symplectic-contact Lie algebra on an
extended Freudenthal module and corrects a non-Jacobi legacy bracket.  This PR
constructs a different Lie algebra: the split-orthogonal algebra of a concrete
ten-dimensional quadratic carrier.

Both have a `|2|` contact grading and two-step nilpotent radicals, but that
shared pattern is not an isomorphism theorem.  Connecting them requires an
explicit representation or reduction that respects the bilinear forms,
brackets and homogeneous subspaces.

## 12. Verification

Focused native commands:

```bash
lake build InfoGeometry.Orthogonal.O55ContactFullFormalism
lake env lean lean/InfoGeometry/Orthogonal/O55ContactAudit.lean
```

The audit requests transitive axiom reports for the principal theorem surface.
The PR must remain draft until those commands succeed on the exact branch head.

## Exact remaining frontier

The finite algebraic contact formalism is implemented.  The next exact gaps
are:

1. build a native homogeneous basis and prove the grade finranks
   `1,12,19,12,1`;
2. construct an explicit Lie equivalence
   `g_0 ≃ gl(2,R) × so(3,3)`;
3. construct a concrete intertwiner between the matrix `so(5,5)` carrier and
   the existing Clifford/Pin realization, rather than comparing only proved
   invariants and selected null actions;
4. only after such an intertwiner exists, transport the grading to the full
   Clifford algebra, spinor module, and any model-specific Hamiltonian.
