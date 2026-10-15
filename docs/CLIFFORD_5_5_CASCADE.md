# Exterior grades, split Clifford modules, and the open comparison frontier

> **Status: corrected mathematical map, not a completed physical unification.**
> This document preserves the intended chain—exterior grades, CAR operators,
> split Clifford algebras, Plücker geometry, pure spinors, Cartan gradings, and
> horizon interpretations—but keeps each claim on its actual carrier. A map
> between two carriers must be defined and proved before their equations can be
> identified. The formulas marked as research targets below are not theorems.

The earlier synthesis conflated three different objects: the exterior algebra
of a four-dimensional vector space, the spin module of a neutral Clifford
space, and the Plücker quadric in the second exterior power. Their dimensions
can coincide in small examples, but a dimension coincidence is not a module
isomorphism, an equivariant map, or an identity of defining equations.

## 1. The actual exterior-algebra carriers

Let `W` be a real vector space of dimension four. Its exterior algebra has
grades

| Exterior degree | 0 | 1 | 2 | 3 | 4 |
|---|---:|---:|---:|---:|---:|
| Dimension | 1 | 4 | 6 | 4 | 1 |

Thus `Λ• W` has dimension 16. Wedge by a vector and contraction by a covector
give the usual creation and annihilation operators on this carrier. With a
chosen dual pairing and the standard sign convention, these operators satisfy
the CAR. They give a Clifford action of the neutral quadratic space
`W ⊕ W*`, of signature `(4,4)`, on `Λ• W`; its real Clifford algebra has
dimension `2^8 = 256` and is represented on a 16-dimensional real module.

This is the Fock/exterior model naturally associated with four creation and
four annihilation modes. It is a `Cl(4,4)` construction. Calling `Λ• W` a
chiral 16-dimensional module for `Spin(5,5)` requires additional representation
data and is not justified by the grade dimensions alone.

For a five-dimensional space `U`, the neutral space `U ⊕ U*` has signature
`(5,5)`. Its exterior/Fock spin module is `Λ• U`, of dimension 32, with even
and odd parity subspaces of dimension 16 each. These are the two half-spin
modules. The split Clifford algebra has dimension `2^10 = 1024`; its faithful
matrix model is `Mat(32, ℝ)`. The dimension 32 belongs to the full spin module,
not to the Clifford algebra itself.

Consequently, `Λ• W` for `dim W = 4` and either half-spin module for
`Spin(5,5)` are both 16-dimensional real vector spaces, but that numerical
coincidence does not identify their actions or their grades. An explicit
linear/equivariant map and an action-intertwining theorem would be needed to
make such an identification.

## 2. CAR and the split Clifford factorization

On an exterior algebra, creation by a basis covector and contraction by its
dual basis vector satisfy, with the standard convention,

```text
aᵢ = εᵢ ∧ ·       aᵢ† = ι_{eᵢ}
{aᵢ, aⱼ} = 0       {aᵢ†, aⱼ†} = 0       {aᵢ, aⱼ†} = δᵢⱼ · id.
```

The two real combinations `aᵢ + aᵢ†` and `aᵢ† - aᵢ` square to `+id` and
`-id`, respectively; different modes anticommute. For `n` modes this realizes
the neutral Clifford algebra `Cl(n,n)` on a `2^n`-dimensional real module.
At the algebra level, the graded tensor product of `n` copies of `Cl(1,1)` is
the appropriate factorization of `Cl(n,n)`. A plain ungraded tensor product
should not silently stand in for the graded product.

These are algebraic statements about the CAR representation. Adding an affine
horizon coordinate, interpreting one mode as modular time, or assigning a
physical meaning to a grading requires additional geometric and dynamical
definitions. The factorization by itself does not provide those data.

## 3. Split `(5,5)` spinors and pure-spinor geometry

The repository has a concrete split-Clifford spinor carrier and projective
pure-spinor/annihilator construction. In that construction a pure-spinor line
determines a five-dimensional maximal totally isotropic subspace of the
ten-dimensional neutral vector carrier. The dedicated owner
`InfoGeometry.Twistor.SplitClifford55PureSpinorOrbitGeometry` proves the
maximal-neutral readout and its dimension/nullity properties.

For a 16-dimensional half-spin module, Cartan purity is expressed through the
spin representation and its annihilator (equivalently, with a chosen charge
conjugation convention, by the appropriate quadratic spinor bilinear
equations). The exact equations depend on the chosen representation and
pairing. They must be evaluated in that module; a two-form Plücker polynomial
cannot be substituted merely because both settings use exterior algebra.

The following remains a distinct representation-theoretic target: construct
the relevant `Spin(5,5)` action on the selected spinor model, state Cartan's
quadratic equations with its explicit bilinear form, and prove their
equivalence to the maximal-isotropic-annihilator condition for that model.
The repository's concrete pure-spinor theorem is evidence for the latter
construction, not for the unrelated four-dimensional Plücker identification.

## 4. Plücker/Klein geometry is not the pure-spinor equation

For a four-dimensional real vector space `W`, a bivector `P ∈ Λ² W` is
decomposable precisely when its Plücker/Klein quadratic form vanishes. In
exterior notation a decomposable bivector `u ∧ v` satisfies

```text
(u ∧ v) ∧ (u ∧ v) = 0.
```

The converse uses the four-dimensional carrier and its Klein quadratic
readout. The repository proves the coordinate criterion and transports it to
Mathlib's literal exterior square in
`InfoGeometry.Projective.ExteriorPowerPluckerBridge`.

That statement is about a point of `Λ² W`; it is neither the mass shell of a
four-momentum nor the Cartan pure-spinor equations of a `Spin(5,5)` module.
The separate `InfoGeometry.Physics.FourVectorDiracReadout` proves the finite
Dirac slash factorization and its Minkowski mass-shell readout. A connection
between these results would require an explicit map preserving the relevant
quadratic forms; none follows from the shared word “null” or “on-shell.”

Likewise, for an arbitrary degree-five decomposable exterior element, the
repeated-generator argument proves its square is zero. But over a ring where
2 is invertible, graded commutativity gives `X ∧ X = - X ∧ X` for every
homogeneous degree-five `X`, so that square is not a test for decomposability.
The generic owner theorem
`InfoGeometry.GrassmannianTower.decomposable_exterior_blade_square_zero`
includes degree five as its `n = 4` instance. It is not a `Gr(5,n)` Plücker
presentation, a `Cl(5,5)` kinematic theorem, or an amplituhedron boundary
theorem; no separate special-case five-blade module is needed. The old
`NativeMathlibAmplituhedronBridge` consisted of duplicate aliases of
Mathlib's `ι_sq_zero`/alternation facts and unused transport helpers. Those
aliases are not needed: Mathlib remains the source of the primitive laws, and
the reusable arbitrary-grade blade theorem now lives with the exterior
algebra owner.

## 5. The five exterior grades and the proposed Cartan chain

The sequence

```text
Λ⁰W → Λ¹W → Λ²W → Λ³W → Λ⁴W
 1       4       6       4       1
```

is the genuine five-grade decomposition of the exterior algebra of a
four-dimensional carrier. A `GL(W)` action preserves each degree, and the
degree operator records the grading. Depending on a chosen convention, one
may recenter the weights as `-2,-1,0,1,2` (or rescale them); those are
representation weights once the action is specified, not an automatic
five-grading of `so(5,5)`.

The old chart associated these five spaces with relative entropy, a horizon
connection, transverse area, helicity/torsion, and bulk dissipation. Those
interpretations are retained here as proposed readouts, not as consequences of
the dimension table. To establish any one of them, specify the source and
target modules, the relevant operator/action, and prove compatibility with
the degree decomposition. In particular, a Cartan 3-form requires Lie-algebra
and invariant-pairing data; it is not supplied by an arbitrary exterior
trivector.

The repository also contains actual five-gradings on specified Lie algebras
and finite operator carriers. They are separate owners. A grading theorem for
one Lie algebra does not automatically identify its graded pieces with
`Λ⁰W,…,Λ⁴W` or with a spinor representation of another group.

## 6. Orthogonal gradings, Cartan's formula, and discrete symmetries

The Lie algebra `so(5,5)` has dimension 45. A parabolic grading is determined
by the chosen parabolic (equivalently, crossed nodes/root grading); its graded
piece dimensions and Levi factor must be computed for that choice. The
previous dimension list

```text
1 + 12 + (gl(4) ⊕ so(1,1)) + 12 + 1
```

does not sum to 45, so it cannot be the claimed decomposition of `so(5,5)`.
The corrected frontier is to choose the intended parabolic, derive its root
spaces and Levi algebra, and then prove the dimensions and bracket-closure
relations in the actual Lean carrier. Do not infer a parabolic from a
five-term exterior-degree display.

For a differential `d` with `d² = 0` and contraction `ι_X`, Cartan's magic
formula identifies the Lie derivative as `L_X = d ι_X + ι_X d` under the
standard differential-geometric definitions. This is a theorem about the
de Rham complex and vector field contraction. It does not, by itself, place
`L_X` in a specified `so(5,5)` subalgebra or prove horizon isometry; that
would need a representation and an intertwining proof.

Similarly, Pin/Spin chirality exchange, an `O(5,5;ℤ)` lattice action, a
five-torus U-duality interpretation, Chern–Simons level quantization, and an
area spectrum each require their own defined carriers and invariance proofs.
The group-theoretic statements can be developed independently; the
gravitational and M-theoretic interpretations remain conjectural until their
maps and hypotheses are made explicit.

## 7. Current owner map and development order

The mathematical chain that is currently supported is:

```text
Exterior algebra alternation
    ├── decomposable bivectors → four-dimensional Klein/Plücker criterion
    ├── finite Clifford matrices → Minkowski Dirac mass-shell identity
    └── split (5,5) spinors → maximal-neutral annihilator Grassmannian
```

These are neighboring constructions, not one theorem. Their current owners
are:

| Carrier / statement | Owner | Verified scope |
|---|---|---|
| Exterior generator and decomposable-blade identities | `InfoGeometry.Algebra.GrassmannianCartanTower`; `InfoGeometry.Canonical.DecomposableBivector` | Alternation in Mathlib's associative exterior algebra |
| Four-dimensional Klein equation iff a simple bivector | `InfoGeometry.Projective.ExteriorPowerPluckerBridge` | Real `Λ²(ℝ⁴)` coordinate/exterior correspondence |
| Minkowski null and massive shell readouts | `InfoGeometry.Physics.FourVectorDiracReadout` | Finite four-vector and Dirac-matrix identities |
| Split `(5,5)` projective pure-spinor annihilator | `InfoGeometry.Twistor.SplitClifford55PureSpinorOrbitGeometry` and its imported owners | Five-dimensional maximal totally-null subspace |
| Exterior-spinor parity | `InfoGeometry.Canonical.ExteriorSpinorChiralityBridge` | Grade involution on the stated exterior-spinor carrier |

The next valid comparison theorem must name its source/target, define its map,
and prove the relevant property is transported. A future proof may show that
some selected bivector locus is a readout of a selected spinor locus; it must
not identify them in advance. The same rule applies to CAR, the Klein quadric,
nilpotent ladder operators, BCFW recursion, amplituhedron geometry, and
horizon dynamics.

This map preserves the motivating vision—one can compare exterior grades,
operator gradings, Clifford actions, and geometric constraints—but restores
the missing causal arrows as explicit proof obligations rather than silently
collapsing distinct mathematical structures.
