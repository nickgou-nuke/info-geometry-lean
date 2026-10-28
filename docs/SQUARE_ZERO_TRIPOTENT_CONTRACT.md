# Square-zero pairs and tripotent matrix resolvents

## Intake and exact carrier

Three unchanged uploads dated 2026-10-28 propose a multiplication table,
reflexive closure, generalized inverses, and a resolvent interpretation.
Their hashes are recorded below. All new theorem carriers remain full
`Matrix n n R` for finite `n`; no diagonalization or commuting-operator
restriction is imposed. Multiplication is the actual matrix product.

Universal hypotheses: `X*X=0`, `Y*Y=0`. Write, in this document only,
`E=X+Y`, `J=X-Y`, `L=XY-YX`, `H=XY+YX`. Reflexive conclusions additionally
require `XYX=X`, `YXY=Y`. General tripotent results use `T*T*T=T` directly.
Star and field structure are introduced only in their corresponding sections.
The spectral parameter is a central field scalar acting on the full matrix;
it does not replace the operator with a scalar model.

## Source grounding and reuse

- `Core/PeirceDecomposition` supplies actual opposite corners and their
  square-zero laws. `Core/PeirceGrading` supplies the idempotent reflection.
- `NCG/NonCommutativeFredholmIndex` owns the matrix commutator and
  anticommutator. These are reused without new bracket definitions.
- `Canonical/DrazinMPCartan.reflexive_squareZero_supports` supplies the two
  idempotent supports. `Core/IdempotentCartan.orthogonal_difference_powers`
  and `Algebra/PeirceRegularityIdentities.orthogonal_difference_cube` own
  their difference's square and cube.
- `Canonical/GrassmannianBundleCyclotomicOrientability` already proves the
  active-support identities and ambient completion for a reflexive pair.
  `Canonical/ReflexiveNilpotentFlows` owns its complementary/Weyl laws.
  The new table removes reflexivity where only square-zero laws are needed;
  no duplicate support carrier or pair-specific completion API is created.
- `Core/DiracSuperalgebra` owns the Moore–Penrose-specialized Majorana
  quartet and global reflections; its hypotheses are stronger than mere
  algebraic reflexivity.
- `Singular/MoorePenrose.IsMoorePenroseInverse` and
  `Singular/Drazin.IsDrazinInverse` are the existing four- and three-equation
  predicates. The pasted replacement structure is discarded.
- `Canonical/DrazinTripotentTrifactorBridge` has a commutative-ring
  tripotent Drazin theorem. The present matrix theorem works over ring
  coefficients without requiring the matrix algebra to be commutative.
- `Canonical/DrazinCoreFlow.complementaryProjection_range_eq_drazinCore`
  owns the general division-ring endomorphism result. The matrix readout here
  identifies the kernel using `Matrix.mulVecLin`, over commutative rings.
- `OperatorAlgebra/GeneralizedNilpotentTripotent` owns complex finite-index
  tripotent projectors. `Canonical/BiquaternionLaplaceTripotent` and
  `External/Auto/DiracResolventZeroModeTripotent` use particular Pauli or
  diagonal operators. They are not substituted for arbitrary matrices.

## Theorem scope

The universal table includes opposing squares, two ordered mixed products,
commutator anticommutation with E and J, cubic products, and `L²=H²`.
Reflexivity gives `E³=E`, `L³=L`, and `J³=-J`.
The algebraic support is idempotent; self-adjointness is a separate property.

For an arbitrary tripotent matrix T, the complement `1-T²` is idempotent,
annihilates T, and has range equal to the kernel of T. Completion by this
complement gives an actual ambient involution. The existing Drazin predicate
is proved at witness exponent 1, without asserting a minimal index.
Self Moore–Penrose inversion is characterized by tripotency and
self-adjointness of T². Self-adjoint T is a sufficient specialization.

For field scalars λ with `λ≠0` and `λ²≠1`, the actual two-sided inverse of
`λ • 1 - T` is proved explicitly. A polynomial factorization alone is not
called an inverse. These conditions are sufficient, not necessary when
some spectral sectors vanish.

## Dependency order and boundaries

The causal order is the prerequisite-to-consumer order of proof declarations,
with its reflexive transitive closure. It is a source-derived partial order,
not physical time and not a newly declared finite poset of metaphor names.
The concrete proof-use edges will be listed after checking the final code.
Context preflight found no generated declaration-DAG/InfoTree artifacts;
no graph freshness claim is made.

No four-dimensional faithful Clifford algebra, spectral pole, mass gap,
Fredholm module, spectral triple, topology, or rewrite-system completeness is
claimed. Tripotency alone implies neither partial isometry nor unitarity.
In characteristic two E=J and L=H, so signs cannot prove linear independence.
The zero pair is permitted; nontriviality is not silently assumed.

## Verification

Pending pinned Lean kernel checking, exact-set axiom inspection, static
placeholder/vacuity checks, and independent semantic and acceptance review.

## Intake SHA256

- `Pasted text(20261028-110439).txt`: `47df7a3dc10b58649e0bbafda858bf39939796ae11aac670298e26bd88cf5a0b`.
- `Pasted text (2)(20261028-110934).txt`: `31426c3f8b2539fc39de439fe41de56b2031bc8c4eb22a841579c46324552a57`.
- `Pasted text (3)(6).txt`: `9d1e867fbcb6d9ad5f7241fe2fe6d0deed171854c508866aaee884b33033835c`.
