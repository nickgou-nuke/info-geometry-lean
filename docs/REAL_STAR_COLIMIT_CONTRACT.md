# Real star-algebra colimit: theorem contract

## Immutable intake and scope

Source: `Pasted text(20261029-094556).txt`, 20,218 bytes.
SHA-256: `ed173d8b5378504778890883f318dae17a7c3cc9cbd17573668338d93375c1c4`.
The original attachment is preserved unchanged. The repository base is
`dc3ebf12fdd9ef4e88eb37acffb919e81932061a`.

The source proposes compatible stage maps and labels their target a universal,
infinite-dimensional star-algebra colimit. It also interprets ordered polynomial
identities as positivity and spectral-gap statements. This contract separates
these claims and completes the algebraic construction on an existing owner.

The carrier is exactly `Clifford.Cl11TensorTowerLimit.Limit`, the native
noncommutative `DirectLimit` of full real matrix algebras
`Cl11TensorTower.MatStage n`. Its bonding map is the existing injective real
algebra homomorphism `stageEmbed n`, namely `A ↦ A ⊗ I₂`. Its descended star is
the existing `limitStarRing`; the real scalar action is the existing `Algebra ℝ`
instance. No quotient, matrix carrier, star, or scalar action is replaced.

## Source-grounded prerequisites

| Owner | Exact prerequisite |
| --- | --- |
| `Algebra/DirectLimitSuperClosureLemmas.lean` | `DirectLimitSuperClosure`, `bondMap`, `bondDirectedSystem`, `directLimitOf_bondMap`, `directLimitOf_injective`, `directLimitLift`, `directLimitLift_of`, `directLimitLift_unique` |
| `Clifford/Cl11TensorTower.lean` | `stageEmbed`, `matStageEmbed_injective`, `stageEmbed_star` on full real matrix stages |
| `Clifford/Cl11TensorTowerLimit.lean` | `Limit`, `ofStage`, `ofStage_star`, `ofStage_apply_bond`, `realAlgebraMap_stage`, native ring/star/algebra instances |
| `Clifford/Cl11TensorTowerProjectionRank.lean` | `matStage_finrank n : Module.finrank ℝ (MatStage n) = 4 ^ n` |
| `Core/PeirceGrading.lean` | Actual corner projections, odd/even ranges, reflection, idempotent and parity laws |
| `OperatorAlgebra/PeirceCoupling/Algebra.lean` | Opposite-corner squares, ordered products, reflection conversion, parity |
| `OperatorAlgebra/PeirceSuperoperators/SquareZeroPair.lean` | Ordered square-zero-pair products and operator-weighted inner actions |
| `OperatorAlgebra/LieJordanPeirceColimit.lean` | Existing native corner and Lie–Jordan transport into the same limit |

The existing `Canonical.Cl11TensorInductiveLimit.ofStageAlgHom` bundles the
same ring inclusion as an algebra map. The new star-algebra inclusion adds the
proved star law to that same native map; it does not introduce another carrier.
`Canonical.FilteredStarAlgebraDirectLimit.liftStarAlgHom` concerns a different,
complex C-star system and is not silently reused as a real construction.

## New declarations and causal order

1. **Native star-algebra universal property.** Bundle the existing canonical
   maps as `StarAlgHom ℝ`. For every compatible family of real star-algebra
   homomorphisms into an arbitrary target real star algebra in `Type`, construct the
   induced native `StarAlgHom`, prove its stage computation, and prove uniqueness.
   Star and scalar compatibility are conclusions of proofs, not structure fields
   supplied by the caller as a substitute for a universal property.
2. **Faithfulness.** Prove canonical stage injectivity from the existing
   injective bonding maps. Prove the universal lift is injective if and only if
   every supplied stage map is injective. Faithfulness of an arbitrary target
   representation is an explicit hypothesis, not a consequence of compatibility.
3. **Actual filtration and infinite dimension.** Use the native partial order
   on `StarSubalgebra ℝ Limit` for the images of full matrix stages. Prove
   inclusion, exhaustion, and strict growth, and prove
   `¬ Module.Finite ℝ Limit` from the unbounded dimensions `4 ^ n` and the
   injective linear stage maps. This is algebraic infinite dimension.
4. **Operator actions and exact transport.** Prove native inner-action and
   double-inner-action intertwining on the same limit. Reflect zero/equality
   through canonical injections and state kernel readouts with their actual
   native `LinearMap` carriers. Transport actual fixed-stage Peirce data and
   ordered square-zero-pair mode identities without replacing operator weights
   by scalars.
5. **Universality obstruction.** The diagonal compatible family into
   `Limit × Limit` makes the source correction concrete: two
   distinct projections agree on every stage image. Both factors remain full
   noncommutative real operator algebras. Compatibility and even faithful stage
   maps therefore do not by themselves prove universality of a chosen target.

Proof prerequisites form a partial order: native ring colimit and descended star
precede the star-algebra lift; bonding injectivity independently precedes stage
faithfulness; both feed representation faithfulness. Stage faithfulness plus
finite-stage dimension feed infinite dimension. Polynomial transport depends on
the native homomorphisms and the relevant algebraic identities, independently of
the dimension argument. The filtration order is an actual native subalgebra
order; this document does not claim a compiler-extracted declaration DAG.

## Exact declaration scope

| New owner | Public theorems | Main conclusions |
| --- | ---: | --- |
| `Clifford/Cl11StarAlgebraColimit.lean` | 10 | Native stage inclusion, stage injectivity, universal lift computation/extensionality/uniqueness, existence and uniqueness, injectivity and surjectivity criteria |
| `Clifford/Cl11StarAlgebraFiltration.lean` | 9 | Native star-subalgebra membership, monotonicity, exhaustion, strict growth, common stages for finite collections, stage dimension, infinite dimension |
| `Clifford/Cl11StarCoconeObstruction.lean` | 4 | Compatible injective family in the product algebra and failure of universal uniqueness |
| `OperatorAlgebra/PeirceStarColimitActions.lean` | 4 | Double-inner-action transport, exact native kernel pullback, canonical-stage kernel equality, common-later-stage readback |
| `OperatorAlgebra/PeirceStarColimitModes.lean` | 14 | Four ordered mode equations and ten actual Peirce corner/parity/Gram consequences |

There are 41 public theorems and five private proof helpers. The native
declaration audit additionally covers the map, subalgebra and order-embedding
definitions, the scalar/star instance, and generated declarations in all five
owners. `OperatorAlgebra/All.lean` exports all five owners.

For a finite-stage star projection `p` and any matrix `a`, write
`U = ofStage n (component10 p a)`, `V = star U`, `E = U + V`, `J = U - V`,
`H = U * V + V * U`, `K = ⁅U, V⁆`, and `S = reflection (ofStage n p)`.
The proved packet consists of `U * U = 0`, `V * V = 0`,
`S * E * S = -E`, `S * J * S = -J`, `S * H * S = H`, `S * K * S = K`,
`S * H = K`, and `-((S * V * S) * U + U * (S * V * S)) = H`.
For the native endomorphism `D = -(LieAlgebra.ad ℝ Limit E *
LieAlgebra.ad ℝ Limit E)`, it also proves `D H = 0`, `D E = 0`,
`D J = -(4 • (H * J))`, and `D K = -(4 • (H * K))`.
The coefficient remains the full operator `H`.

## Claim dispositions and hypotheses

| Intake claim | Formal disposition |
| --- | --- |
| A compatible cone is automatically universal | Replaced by a constructed lift with proved existence and uniqueness on the existing quotient |
| The target is automatically infinite-dimensional | A separate theorem proves algebraic infinite dimension of the actual faithful full-matrix limit |
| A finite-stage identity survives passage to the limit | Native homomorphism transport; nonvanishing additionally uses injectivity |
| Odd linear and even quadratic Peirce terms | Algebraic parity identities from an actual idempotent |
| `D(X) = -4 H X` is a spectral gap | Only the ordered operator identity is claimed; no scalar eigenvalue or uniform positive lower bound follows |
| A sum of star squares establishes OS positivity | Algebraic Gram identity only; no OS structure or positivity order is introduced |
| All 52 named archetypes lift | No unbounded blanket theorem; only the explicit checked declarations are reported |

An actual projection `p` is fixed at a finite stage and transported by `bondMap`.
The changing family `globalChirality n` is not asserted compatible with
`A ↦ A ⊗ I₂`; its defining recursion appends a chirality matrix instead.

## Concurrent ownership and verification plan

Read-only overlap inspection found PR #267 at
`65fa4f70b74403448f699fff2c5f58b475a34013` (Peirce star reflection, native
star-ring quotient and Cartan transport), PR #268 at
`3ee4135b9adb19500e6e3e6330a003b5eb86ec10` (all-order inner actions), and PR #269
at `61dd12e56dfe97d8f796e1cfd5ef31b899ba2bdf` (finite real gap criteria and
mode actions). This work uses separate owner files and does not copy those
branches or claim their results as its own.

Read-only inspection also covered PR #270 at
`156a4a6aa739ed6d0edcc66e2491cba9ed8a31c4`. Its `SymmetricDissipator` owners
prove ring-map naturality, finite-iterate transport, fixed-stage vanishing
reflection on the same real matrix limit, and parity-sector invariance on the
separate existing `PrimonUHFAlgebra`. Its mixed operator specializes to twice
the negative double inner action when the two coefficients coincide, so faithful
fixed-stage vanishing transport is shared mathematical ground. The native real
star-algebra universal property, strict filtration, algebraic infinite dimension,
general native kernel pullback, arbitrary-limit common-stage readback, and
ordered Peirce mode equations above remain separate results. No owner from
that unmerged branch is copied.

At the publication preflight, `main` had advanced to
`87bfa4567046db6f475a9df2903bd4060dc773ca` by adding `REPOCONTENT.md` and
`Yang-Mills-Letter.md`. No proof dependency, gate, toolchain, manifest, or workflow
changed relative to the recorded intake base.

Generation: root and a sandbox-only helper. Mathematical review:
`completion_check`. Independent evidence acceptance: `colimit_owner_search`.
Only root edits the live checkout. All compiler commands are serialized through
the shared build lock; no caches, dependency revisions, or gate thresholds are
changed. Acceptance requires a fresh complete selected dependency-closure build,
native declaration/axiom audit, strict placeholder scan, semantic review, staged
hook, and exact source/evidence hashes. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. The dedicated CI artifact records the fresh selected
closure build, native audit, source hashes, and semantic findings. The full
`OperatorAlgebra/All.lean` import closure is not claimed to have been compiled;
its export source is scanned and bound in the evidence. Local development runs
may reuse verified dependency artifacts; acceptance CI does not.

The semantic scanner marks the two computational rules `ofStageStarAlgHom_apply`
and `lift_ofStage` as `warning/trivial_surface` because their proofs are `rfl`.
They specify computation of the constructed maps on actual operators, rather
than asserting a proposition-valued witness. The rules retain their canonical
proofs. CI requires precisely those two reviewed findings, complete scan
coverage, and no further findings; the scanner and its registry are unchanged.

The strict placeholder scanner also reports two soft findings on the section
parameters `f` and `hf`. These are the native cocone maps and their one-step
compatibility hypothesis. They do not assume any of the universal-property,
faithfulness, dimension, or operator-mode conclusions. Independent mathematical
review classifies these as legitimate hypotheses. Strict scanning requires no
hard findings, and the two soft findings remain visible in the CI job log.
