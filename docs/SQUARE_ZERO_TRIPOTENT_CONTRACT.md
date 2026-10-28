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
`λ • 1 - T` is proved explicitly as

```text
(λ(λ²−1))⁻¹ • ((λ²−1) • 1 + λ • T + T*T).
```

A polynomial factorization alone is not
called an inverse. These conditions are sufficient, not necessary when
some spectral sectors vanish.

## Dependency order and boundaries

The causal order is the prerequisite-to-consumer order of proof declarations,
with its reflexive transitive closure. It is a source-derived partial order,
not physical time and not a newly declared finite poset of metaphor names.
The following are principal named proof-use edges in the source (independent
rows need not be ordered). Their transitive closure gives the prerequisite
order; primitive algebraic normalizations are leaves, not temporal processes.

| Prerequisite declarations | Consumer declarations |
| --- | --- |
| `sum_mul_difference`, `difference_mul_sum` | `sum_difference_anticommute` |
| `sum_sq` | `anticommutator_commutes_sum` |
| `sum_cube` | `sum_cube_of_reflexive` |
| `reflexive_squareZero_supports`, `orthogonal_difference_cube` | `commutator_cube_of_reflexive` |
| `commutator_mul_sum` | `commutator_mul_sum_of_reflexive` |
| Native Peirce square-zero laws, `sum_cube_of_reflexive` | `corner_sum_cube` |
| `square_idempotent` | `complement_idempotent` |
| `complement_idempotent`, `complement_mul`, `mul_complement` | `completion_sq` |
| `completion_sq` | `completion_isUnit`, `completion_mem_unitary` |
| `self_moorePenrose_iff` | `self_moorePenrose_of_isSelfAdjoint` |
| `mul_complement` | `complement_mulVec_eq_self_iff`, `range_complement_eq_ker` |
| `complement_mulVec_eq_self_iff` | `range_complement_eq_ker` |
| `resolventPolynomial`, `numerator_left` | `shift_mul_resolvent` |
| `resolventPolynomial`, `numerator_right` | `resolvent_mul_shift` |
| `shift_mul_resolvent`, mathlib `Matrix.inv_eq_right_inv` | `shift_inv` |
| `shift_mul_resolvent`, `resolvent_mul_shift` | `shift_isUnit` |

The square-zero/reflexive table produces tripotent sums and commutators;
these conclusions can instantiate the general geometry and resolvent
lemmas. That is a composable interface, distinct from an existing proof-use
edge: the geometry file does not import the square-zero table.
Context preflight found no generated declaration-DAG/InfoTree artifacts;
no graph freshness claim is made.

No four-dimensional faithful Clifford algebra, spectral pole, mass gap,
Fredholm module, spectral triple, topology, or rewrite-system completeness is
claimed. Tripotency alone implies neither partial isometry nor unitarity.
In characteristic two E=J and L=H, so signs cannot prove linear independence.
The zero pair is permitted; nontriviality is not silently assumed.

## Verification

The focused [run 40681706623](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40681706623),
[job 122793778237](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40681706623/job/122793778237),
passed on source commit `5c00d6724180e394c9363e66c00472ac777468e2`.
The checked merge was `c0810a3e10b15d37d4873e195f4a248c33c55605`, against
base `cb7482d86eadb42f2ab9c2f6f624d67b7bfe7ce4` on 2026-10-28.
It rebuilt all 19 project modules in the selected import closure, serially,
with fresh project oleans and the pinned mathlib cache.

- Lean `4.34.1`, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`;
  Lake `5.0.0-src+5045d00`.
- mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; no dependency pin changes.
- 39 theorems and one definition passed exact-set `#print axioms` inspection.
  The only dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
- No placeholders, custom axioms, `unsafe`, or `native_decide` in new proofs;
  semantic vacuity gate: zero findings. Shell syntax and diff checks pass.
- New modules emit no Lean warnings. The existing `Singular/MoorePenrose`
  owner emits 14 deprecation/style warnings; it is unchanged.
- Independent source semantic audit: PASS, accepted at the documented
  algebraic scope. Separate independent QA: ACCEPTED_WITH_LIMITED_SCOPE,
  after verifying the exact source hashes, theorem inventory, compiler log,
  axiom report, and warning scope.

This is focused kernel validation, not a claim of a successful repository-wide
build. Separate existing CI jobs fail before checking these proofs: style run
`40680179717` reports the `Canonical/KRDualityCascade.lean` / `KrDualityCascade.lean`
case collision; Sorry Gate run `40680179709` cannot find `lake` (exit 127).

The final verification-document commit does not change any checked source,
audit module, dependency pin, or build script.

## Intake SHA256

- `Pasted text(20261028-110439).txt`: `47df7a3dc10b58649e0bbafda858bf39939796ae11aac670298e26bd88cf5a0b`.
- `Pasted text (2)(20261028-110934).txt`: `31426c3f8b2539fc39de439fe41de56b2031bc8c4eb22a841579c46324552a57`.
- `Pasted text (3)(6).txt`: `9d1e867fbcb6d9ad5f7241fe2fe6d0deed171854c508866aaee884b33033835c`.

## Verified source SHA256

- `SquareZeroMatrixPair.lean`: `6c30f14324ee102560908c592567ac317ce4dddc2f70f08b021576d28e1cc634`.
- `TripotentMatrixGeometry.lean`: `c9f22e1984c52a82586ce9324013ab89ee5dc0e1467b8cd8a07db2bc11e830d1`.
- `TripotentMatrixResolvent.lean`: `cd888214e5f5018f67d13197fc90326c997af1354ac4a9e429668024253ee828`.
- `SquareZeroTripotentAudit.lean`: `bf01b932599af2774dfe995b862119c6183986c9aec429dd36bc0cf116ed6a45`.
