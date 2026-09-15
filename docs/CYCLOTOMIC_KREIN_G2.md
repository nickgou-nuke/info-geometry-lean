# Cyclotomic, neutral-pairing, and G₂ boundaries

## Scope

`InfoGeometry.Exceptional.CyclotomicKreinG2` extracts algebraic statements from
the supplied narrative. It does not identify drawings, physical spacetime,
Majorana representations, the Leech lattice, or zeta zeros with these objects.

The integer companion matrix is a new finite representation, not a replacement
for the categorical, Zorn, or existing six-dimensional twelvefold owners.
`Canonical.TwelveFoldExplicitOperators.masterTwelve` has a different carrier and
half-period operator; it must not be silently identified with this matrix.

## Reuse and proofs

- The polynomial statement uses native `Polynomial.cyclotomic`. Its expansion
  proof follows Mathlib's cyclotomic expansion identity, also used in the
  existing `proofs/TwelveFoldCyclotomicPolynomial.lean` archive-level surface.
- `CyclotomicIntegerClock` proves the quartic implication in an arbitrary
  possibly noncommutative ring, then instantiates it over integer matrices.
  The clock has exact `orderOf = 12`, not just a period dividing twelve.
  Its difference from the identity is a unit, so it is not unipotent.
- The native polynomial has `natDegree = 4` over every nontrivial commutative
  coefficient ring. This is a degree statement, not an identification with
  physical sheets or spacetime dimensions.
- `CyclotomicRotation` represents the existing primitive complex root `zeta12`
  by Mathlib's `Algebra.leftMulMatrix Complex.basisOneI`. Its algebraic
  coordinates reuse `Canonical.TwelveFoldGaussSum.zeta12_algebraic`.
  The matrix is the real rotation through `π / 6`, has determinant one,
  trace `√3`, exact order twelve, and sixth power `-1`. Its quartic equation
  is transported through the native algebra homomorphism from the primitive
  root's cyclotomic equation. Its trace differs from the integer clock's
  trace zero; these are different representations on different carriers.
- The actual cyclotomic-field Galois equivalence and Klein-four theorem are
  reused from `Canonical.TwelveFoldCyclotomicNative`. Nonidentity automorphisms
  have order two; the identity does not.
- The neutral carrier, bilinear form, and sign involution are reused from
  `Clifford.NeutralPhaseSpaceCore`, on `Space × Module.Dual ℝ Space`.
  Simultaneous inverse-dual changes preserve this pairing. The sign involution
  is an anti-isometry, and its twisted self-pairing vanishes identically; it
  cannot supply a positive-definite fundamental symmetry for this form.
- G₂ statements use Mathlib's `RootPairing.IsG2` and `EmbeddedG2` theorems:
  rank two and twelve roots, including six roots in each squared-length class
  after normalizing the invariant form's short-root squared length to one.
  Their native hypotheses are explicit. No set of
  twelve drawn points is declared to be a root system without verification.
  Four Galois automorphisms cannot be bijective with twelve root indices.
- Regression examples also reuse `Lie.G2DoubleStarRootDecomposition` and the
  existing Zorn derivation decomposition: disjoint six-element root sectors,
  a two-dimensional Cartan subspace, and a twelve-dimensional root-space sum.
  This does not assert a new equivalence between that owner and the native
  `RootPairing` used in the generic G₂ statements.
- The trace-discriminant equivalences are scalar algebra. The determinant-one
  interpretation requires a determinant-one matrix. An explicit real
  determinant-one elliptic matrix with rational entries disproves the
  proposed implication to twelfth periodicity.

## Dependency order

`CyclotomicKreinG2Dependency` is a declared finite dependency model, not a
metaprogram extracting the Lean environment's actual dependency graph:

```text
cyclotomicPolynomial → integerClock → exactPeriod
unitArithmetic → galoisGroup
rootDecomposition
neutralPairing → paraAntiIsometry
traceDiscriminant → ellipticCounterexample
primitiveRoot → rotationRepresentation → rotationPeriod
rotationRepresentation, traceDiscriminant → ellipticRotation
cyclotomicPolynomial, rotationRepresentation → rotationQuartic → rotationHalfPeriod
```

The module proves a native `PartialOrder`, the displayed strict relations,
incomparability of separate branches, and absence of strict cycles. These
properties concern this declared order, not physical causality or logical
independence of arbitrary theories.

The exact-order and discriminant readouts of the rotation are incomparable
in this declared order. The exact-order proof transports primitive-root order;
it does not infer periodicity from a negative discriminant.

## Excluded inferences

`Chronometry.MatrixClock` realizes the transposed companion convention over
the reals by mapping the existing integer clock and transposing. It does not
introduce a second independently assumed clock. The quartic identity is
transported from the integer owner; exact order twelve is separately proved.
For a real two-by-two matrix with determinant one and trace one, the module
instead proves its cube is `-1` and its sixth power is `1`. Such a matrix
cannot have exact order twelve. Thus trace one cannot replace the actual
`sqrt 3` trace of the primitive twelfth-root rotation.

Finite order is not unipotence. A negative trace discriminant does not imply
order twelve. Zero discriminant includes scalar matrices and alone does not
establish a nontrivial parabolic Jordan block. An equality of cardinalities
does not construct a representation, Galois action, root-system isomorphism,
lattice embedding, or physical identification. No statement about locations of
zeros of the Riemann zeta function is asserted.

## Validation

All six Lean modules pass the serial, shared-lock isolated validation on
2026-09-14, using installed Lean 4.28.0 and its cached Mathlib dependencies.
The thirteen regression examples and 48 explicit `#print axioms` checks pass.
Every audited theorem uses only subsets of `propext`, `Classical.choice`, and
`Quot.sound`; none uses `sorryAx` or an additional axiom.

The reused neutral-pairing, cyclotomic Galois, and Zorn root-decomposition
owners were also checked with their required local imports. Existing warnings
were left untouched. The pinned Lean 4.28.1 environment was not available for
this check; no toolchain or dependency metadata was changed. This is a narrow
compatibility validation, not a successful build claim for the whole repository.

The additional `Chronometry.MatrixClock` module and its two regression examples
also pass the same serial Lean 4.28.0 validation. Its eight axiom audits report
only `propext`, `Classical.choice`, and `Quot.sound`.
