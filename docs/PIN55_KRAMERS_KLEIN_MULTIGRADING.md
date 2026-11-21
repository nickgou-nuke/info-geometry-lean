# Complex Kramers, Klein deck topology, and the Pin(5,5) multiple grading

## Scope

The source stream superimposes several mathematically distinct structures:

1. a complex antiunitary with square `-1`;
2. an orientation-reversing affine deck action;
3. a five-graded conformal/Clifford algebra;
4. a symmetric-pair grading of `o(5,5)`;
5. a separate Freudenthal contact five-grading;
6. downstream Hodge, thermodynamic, and BdG interpretations.

This branch formalizes the exact finite algebraic and quotient-topological core
without identifying these objects merely because they all involve doubling,
reflection, or parity.

## Deep repository audit

The repository already contained important archetypes:

- `Canonical.TimeReversalKramers`: a real-linear square-minus-one Kramers
  interface;
- `Quantum.NeutralKreinMajoranaFrame`: a doubled neutral/Krein carrier;
- `Canonical.ConformalFiveGradeInversion`: the five grade labels and their
  order-two swap;
- `Clifford.ConformalLieAlgebra55`: actual adjoint eigenspaces in `Cl(5,5)`;
- `Canonical.O55FiveGradeClosure`: explicit occupied `-2,-1,0,+1,+2` lanes;
- `proofs.O55GradedGeneratorBasis`: the `20+25=45` compact/mixed generator
  partition;
- `proofs.PinO55GlideReflection`: a native Pin(5,5) projective-null swap and
  affine Klein glide laws;
- the corrected Freudenthal symplectic-contact Lie representation and its
  common CAR--CCR carrier.

The missing pieces were therefore not another five-grade label type or another
Pin shadow.  They were:

- a genuine complex conjugate-semilinear Kramers operator;
- the full affine Klein normal-form group and free action;
- the corresponding literal orbit quotient;
- the structural `ZMod 2` bracket grading of matrix `o(5,5)`;
- exact bridges among grade reversal, parity, phase inversion, and the existing
  Pin(5,5) null swap.

## 1. Complex antiunitary Kramers operator

On `H2 = Fin 2 -> Complex`, define

```text
T(z0,z1) = (-conj z1, conj z0).
```

It is bundled as a native Mathlib star-linear equivalence

```lean
H2 ≃ₗ⋆[ℂ] H2.
```

The source proves

```text
T(c v) = conj(c) T(v),
T^2(v) = -v,
T^4(v) = v,
<Tu,Tv> = <v,u>,
<v,Tv> = 0.
```

For a complex-linear operator commuting with `T`, a real-eigenvalue
eigenvector and its Kramers partner have the same eigenvalue.  The theorem is a
finite representation statement; a global physical time reversal is not
inferred.

## 2. Phase-inverting glide lift

Let `U_z` be scalar multiplication by `z`.  Semilinearity gives

```text
T U_z = U_conj(z) T.
```

When `conj(z) z = 1`, this becomes

```text
T U_z = U_(z^-1) T.
```

This is the exact bridge between a phase-inverting orientation reversal and the
antiunitary carrier.  The additional relation `T^2=-1` is representation data;
it is not a consequence of the topology of a Klein bottle.

## 3. Klein deck normal form

The deck group is represented by pairs `(m,n) in Z x Z` with multiplication

```text
(m,n) (p,q) = (m + (-1)^n p, n+q).
```

Its affine action is

```text
(m,n) . (x,y) = ((-1)^n x + m, y+n).
```

The source installs native `Group` and `MulAction` instances and proves:

```text
(g h) . p = g . (h . p),
g . p = p  iff  g = 1,
b a b^-1 = a^-1.
```

The orientation character is `(-1)^n`; the horizontal generator has positive
orientation and the glide generator has negative orientation.

## 4. Abelian readout

The canonical additive readout is

```text
(m,n) |-> (n, m mod 2) in Z x ZMod 2.
```

It is proved additive under the noncommutative deck multiplication and
surjective.  The horizontal class has order two and the vertical class has
infinite order.

This is the expected algebraic target of the Klein-bottle abelianization.  It
is deliberately called an `abelianReadout`, not `H1`, until the universal
abelianization theorem and the covering/fundamental-group comparison are
proved.

## 5. Literal affine orbit quotient

The source constructs the orbit setoid

```text
p ~ q  iff  exists g, g . p = q
```

and the quotient topological space.  It proves projection surjectivity,
continuity, the quotient-map property, invariance under every deck element,
and the exact fibre criterion.

The group action is proved free.  Proper discontinuity, local covering charts,
smooth quotient-manifold structure, compactness, and the computation of the
fundamental group remain explicit future theorem layers.

## 6. Native O(5,5) five grading

The branch reuses `Canonical.O55FiveGradeClosure`.  That owner already defines
the Clifford grading element `D`, the adjoint map

```text
ad_D(x) = D x - x D,
```

and its eigenspaces of grades `-2,-1,0,+1,+2`.  It proves the named lanes

```text
u5,u4                 : +1,
v5,v4                 : -1,
D                     :  0,
[u5,u4]               : +2,
[v5,v4]               : -2.
```

It also proves that the Clifford inversion `thetaOp` maps every grade to the
opposite grade.

`O55FiveGradeKramersBridge.lean` identifies the five grade labels with the
finite Kramers index and proves that `thetaOp` and the complex antiunitary use
the same grade permutation while retaining different squares:

```text
thetaOp^2 = +1 on the Clifford carrier,
T^2       = -1 on the Kramers carrier.
```

## 7. Independent O(5,5) symmetric-pair grading

On the `10 x 10` matrix carrier use

```text
eta = diag(I5,-I5),
theta(X) = eta X eta.
```

The source proves `theta^2=1`, multiplicativity, and the bracket table

```text
[even,even] -> even,
[even,odd]  -> odd,
[odd,odd]   -> even.
```

It also proves closure of the matrix equation

```text
X^T eta + eta X = 0
```

under commutators, so the same `ZMod 2` grading restricts to `o(5,5)`.

The existing generator counts become structural parity counts:

```text
even rotations : 10 + 10 = 20,
mixed boosts   : 25,
total          : 45.
```

This symmetric-pair parity is independent of the five-valued conformal degree.

## 8. Freudenthal contact grading

The corrected symplectic-contact representation supplies another genuine
integer five-grading.  Its bracket satisfies

```text
[g_k,g_l] subset g_(k+l),
```

and reduction modulo two gives a compatible parity grading.

The current branch proves a label-level correspondence with the O(5,5) five
weights.  It does not assert an isomorphism between the Freudenthal contact Lie
algebra and `o(5,5)`; such an intertwiner would require an explicit common
representation and dimension-compatible data.

## 9. Product multiple degree

The complete finite label is kept as product data:

```text
(contact integer degree,
 contact parity,
 O(5,5) five-grade parity,
 O(5,5) symmetric-pair parity,
 Klein orientation parity).
```

Kramers reversal negates the integer degree while preserving its parity.  The
Pin(5,5) crosscap exchanges the two projective null rays.  The affine glide
reverses orientation.  These are compatible statements on separate carriers,
not definitions of one another.

## Claims not installed

The branch does not claim:

- that two boundary vectors determine a Klein bottle;
- that every orientation-reversing map is antiunitary;
- that `T^2=-1` follows from non-orientability;
- that the affine orbit quotient has already been proved a smooth compact
  manifold;
- that the displayed abelian readout is already singular homology;
- that the Freudenthal contact algebra is isomorphic to `o(5,5)`;
- that the complex two-component Kramers fibre is the complete spin module of
  `Spin(5,5)`;
- any BdG, transport, entropy-production, or backscattering theorem without a
  separately specified dynamical model.

## Exact remaining frontier

1. prove `ProperlyDiscontinuousSMul Deck Plane`;
2. obtain the covering-space structure of the orbit projection;
3. identify the deck group with the fundamental group of the quotient;
4. prove the universal abelianization theorem and then identify `H1` with
   `Z x ZMod 2`;
5. construct the smooth quotient manifold and a formal non-orientability
   obstruction;
6. construct a genuine `Spin(5,5)` module carrying an antiunitary and compare
   it with the finite `H2` Kramers fibre;
7. construct, if intended, an explicit grade-preserving Lie homomorphism
   between a selected Freudenthal contact instance and an `o(5,5)` subalgebra.

## Public entry point

```lean
import InfoGeometry.Clifford.Pin55KramersKleinAll
```

## Focused verification

```bash
bash scripts/check_pin55_kramers_klein.sh
```
