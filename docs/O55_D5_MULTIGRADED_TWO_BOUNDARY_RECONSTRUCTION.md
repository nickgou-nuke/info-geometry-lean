# `O(5,5)`, the `D₅` multigrading, and projective two-boundary readouts

## Scope

This development lifts the finite two-boundary matrix-coefficient arguments to
the full split orthogonal carrier.  It does not reinterpret a weak coefficient
as a physical current and does not infer a non-orientable quotient from the
existence of two boundary vectors.

The exact chain is

```text
real Witt space R^5 + (R^5)*
        |
        v
so(5,5) real split form
        |
        v complexification
so(10,C), D5 roots, Z^5 multidegrees
        |
        v collapse along a distinguished isotropic 2-plane
|2|-grading: 1 + 12 + 19 + 12 + 1
        |
        v
five spectral projectors, bracket-degree addition
        |
        v
projective two-boundary matrix coefficients and weight selection
```

## Repository audit

The repository already contained the following relevant owners:

- guarded finite weak values and the generic regular two-boundary functional;
- a static path/property separation witness;
- Hilbert--Schmidt Tomita conjugation and finite antiunitarity theorems;
- thermofield-double coefficient identities;
- Klein-bottle and glide-reflection owners;
- a native `Pin(5,5)` element exchanging the canonical null pair;
- finite `O(5,5)` carrier and generator-count readouts;
- separate five-graded contact and CAR--CCR representations.

The missing mathematical layer was the explicit `D₅` multigrading of the full
split orthogonal algebra, its exact contact collapse, its direct-sum spectral
projectors, and the corresponding boundary-weight selection theorem.

## 1. Real split form and complexification

Let `E = R^5` and use the Witt carrier

```text
V = E + E*.
```

In a chosen dual basis, the bilinear form has matrix

```text
J = [[0,I],[I,0]],
```

and signature `(5,5)`.  The real infinitesimal algebra consists of matrices
satisfying

```text
X^sharp = J X^T J = -X.
```

`O55RealWittForm.lean` constructs this as a native real `LieSubalgebra`.
Entrywise complexification gives the corresponding complex Witt-skew algebra,
which is the `D₅` algebra `so(10,C)`.  The code therefore does not call the
whole complex algebra itself a real-signature object.

## 2. Full `D₅` root multigrading

The forty roots are

```text
s_i e_i + s_j e_j,   i<j,   s_i,s_j in {+1,-1}.
```

Each root carries its complete degree

```text
mu : Fin 5 -> Z.
```

The code proves:

```text
card(root system) = 40,
sum_a mu(a)^2 = 2.
```

The diagonal Cartan matrices act by

```text
[H(h), E_mu] = (sum_a mu(a) h(a)) E_mu.
```

This is the actual simultaneous `Z^5` grading, not merely five labels attached
to generators.

## 3. Contact collapse and five-grade dimensions

Select the first two isotropic axes and define

```text
deg(mu) = mu(0) + mu(1).
```

The root counts are

```text
degree       -2  -1   0  +1  +2
root count    1  12  14  12   1.
```

The rank-five Cartan lies in degree zero, yielding

```text
dim g_k       1  12  19  12   1,
total dimension = 45.
```

This is the standard `|2|` parabolic grading associated with an isotropic
2-plane in a ten-dimensional split orthogonal space.

## 4. Native Witt root representation

The complex carrier is indexed by two Witt sheets and five axes.  For every
root, the code constructs an explicit `10 x 10` matrix.  The four sign cases
are the standard blocks:

```text
 e_i+e_j : E_(+i,-j) - E_(+j,-i)
-e_i-e_j : E_(-i,+j) - E_(-j,+i)
 e_i-e_j : E_(+i,+j) - E_(-j,-i)
-e_i+e_j : E_(+j,+i) - E_(-i,-j).
```

Every matrix is proved Witt-skew.  The Witt adjoint is proved involutive and
anti-multiplicative, so the skew-fixed space is closed under commutators and is
packaged as a native Mathlib `LieSubalgebra`.

## 5. Exhaustion of the full algebra

An arbitrary Witt-skew matrix has unique block coordinates

```text
X = [[A,B],[C,-A^T]],
```

where `A` is unrestricted and `B,C` are skew.  The code constructs a genuine
linear equivalence

```text
Matrix(5,5,C) x C^10 x C^10  ~=  splitO55Lie.
```

Thus the independent coordinate count is exactly

```text
25 + 10 + 10 = 45.
```

This prevents the root count from being used as an unsupported spanning claim.

## 6. Full direct-sum five-grading

Every matrix entry has an Euler degree in `{-2,-1,0,1,2}`.  Entrywise spectral
projections define native linear maps

```text
Pi_k : splitO55Lie -> splitO55Lie.
```

The code proves

```text
Pi_k^2 = Pi_k,
Pi_k Pi_l = 0                    for k != l,
sum_(k=-2)^2 Pi_k = identity,
Pi_k X belongs to g_k,
Pi_k = 0 outside {-2,-1,0,1,2}.
```

The commutator law is proved for arbitrary homogeneous elements:

```text
[g_k,g_l] is contained in g_(k+l).
```

This is the complete finite five-grade decomposition, not only a theorem about
selected root generators.

## 7. Multigraded two-boundary selection

For a finite state carrier, let

```text
W_B(A) = <post|A|pre> / <post|pre>,
```

with nonzero overlap.  Suppose

```text
H_a pre = alpha_a pre,
<post|H_a x> = beta_a <post|x>,
[H_a,A] = mu_a A.
```

The code proves the exact scalar equation

```text
(beta_a-alpha_a-mu_a) <post|A|pre> = 0.
```

Consequently, if `W_B(A)` is nonzero, then

```text
mu_a = beta_a-alpha_a
```

for every one of the five Cartan coordinates.  Applied to a `D₅` root operator,
this gives the full multidegree selection rule.  Summing the first two
coordinates gives the collapsed five-grade selection rule.

This theorem is representation theory of matrix coefficients.  It is not a
statement that a conserved physical quantity travels through an empty region.

## 8. Internal two-sheet exchange

The internal Witt exchange sends

```text
(+,i) <-> (-,i).
```

It squares to the identity and conjugates every Cartan operator to its
negative.  Therefore it maps a multiweight `mu` to `-mu` and reverses the
contact degree.

If both boundary vectors are exchanged and the probe is conjugated by the
same sheet operator, the normalized matrix coefficient is unchanged.

The internal exchange is distinct from the affine Klein glide.  The existing
glide satisfies

```text
b a b^-1 = a^-1,
b^2 = a translation,
```

whereas the internal sheet exchange satisfies `S^2=1`.  A theorem identifying
their representations would require an explicit intertwiner.

## 9. Existing `Pin(5,5)` owner

The branch reuses the existing native split-Pin element which exchanges the
canonical projective null pair.  It also reuses the existing orientation sign,
carrier dimension ten, and generator count 45.  The new five-grade dimension
sum is proved equal to that existing count.

No new Pin group or Klein-bottle carrier is introduced.

## 10. Claims not installed

The code does not assert:

- that a two-boundary formalism creates a Klein-bottle topology;
- that the internal sheet exchange is antiunitary;
- that a weak matrix coefficient is a probability, density, or current;
- that vanishing of a support coefficient proves carrier-free transport;
- that thermofield doubling forces opposite entropy-production arrows;
- that a non-Hermitian clock term is universally proportional to acceleration;
- that `so(5,5)` is the exceptional Freudenthal contact algebra;
- that the affine glide and the internal Witt exchange are the same map.

## Public entry point

```lean
import InfoGeometry.Orthogonal.O55FullFormalismAll
```

## Verification command

```bash
bash scripts/check_o55_multigraded_two_boundary.sh
```

The branch remains draft until the exact branch head elaborates and the
transitive axiom audit succeeds.

## Exact next frontier

After native compilation, the nearest structural theorem is an explicit
intertwiner between the ten-dimensional Witt vector representation and the
repository's existing `Cl(5,5)` null-pair representation.  It should prove that
Clifford twisted adjoint action realizes the same internal sheet and grade
reversal.  Only after that may the affine Klein glide, the Pin element, and the
internal multigrading be compared in one representation theorem.
