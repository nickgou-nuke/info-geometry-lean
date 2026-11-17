# Finite Hodge, commutants, and Kraus invariance: theorem contract

Status: reconstructed source contract, 2026-11-17. Source review and the scoped static gates have passed at the hashes below. Fresh native closure, declaration-axiom acceptance, and remote CI are pending. This document does not certify compilation.

## Intake and recovery provenance

The intake is preserved as [hodge_commutant_intake_20261116.txt](sources/hodge_commutant_intake_20261116.txt), originally supplied as `Pasted text(20261116-182549).txt`. It is research input, not an executable instruction set or a collection of accepted axioms.

- Intake SHA-256: `12f8529e51f534c71e33d0f087b95cb6628cb3fbe2459bbe9b57dbbaa140e603`.
- Repository baseline: `08c34e03f610b452e03422037949196dc7d92d6d`.
- Pinned Lean: `v4.34.1`. Pinned Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- The original transient checkout, candidates, and development logs expired overnight. No lost compiler log has been recreated.
- Four owner sources were recovered byte-for-byte against retained hashes. The generic Kraus insertion was reconstructed semantically and independently reviewed again.
- This contract and [HODGE_COMMUTANT_REVIEW.md](HODGE_COMMUTANT_REVIEW.md) are newly reconstructed documentation, not byte-certified copies of the lost documents.

| Owner below `lean/InfoGeometry/` | Recovered SHA-256 | Recovery |
|---|---|---|
| `OperatorAlgebra/NoncommutativeKrausChannel.lean` | `62091573510385b10a7678bbdca99c4cbf62737e1bf9b8e60728e62abc30ed45` | Reconstructed insertion |
| `Physics/RegularBimoduleCommutant.lean` | `a85dd111963c5ec1077069a5d2e2aa91d782e29c739690466a09854288bec6f4` | Exact |
| `Quantum/KrausUniversalFixedEffects.lean` | `19df4a3b98c871e37cfcfddc7ca3fcb30145c4d7d0258a05a5839c463e71c9ca` | Exact, including Hodge bridge |
| `OperatorAlgebra/MatrixCommutatorHodge.lean` | `c67fbceea6410b341b862b360508b550ecb28cd72b680f5d3f555a7bc6ffc092` | Exact |
| `Quantum/BipartiteOperatorSectors.lean` | `ec425286d6b824588705a1e5837bfb638d5b2171870ef5aecdf01fb1dfd71d6b` | Exact |

The former generic candidate hash was `1ed0688394c1b3d073f2b0cc2f51c6c8c4f5c26f6411468e1f837aa257ed08d8`. It is not the current generic source hash. Its historical development pass cannot certify the reconstruction.

## Actual carriers and conventions

| Construction | Carrier and hypotheses | Operations and scope |
|---|---|---|
| Generic Kraus defect | `A` with `[Ring A] [StarRing A]`; finite Kraus index | Ordered ring products and `star`; no order, norm, positivity, or analytic completion assumed |
| Regular commutant | `A →ₗ[R] A` with `[Semiring R] [Ring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]` | `leftAction a x = a * x` and `rightAction b x = x * b`; add `StarRing A` for the two new star/Kraus identities |
| Hodge degree zero | Full `Matrix n n ℂ`, `[Fintype n] [DecidableEq n]`; a finite frame `Q : ι → Matrix n n ℂ` | Hilbert–Schmidt matrix inner product and the actual finite Hilbert product `PiLp 2`; no scalar or diagonal restriction |
| Universal fixed matrices | Full `Matrix n n ℂ`; finite, decidable, nonempty `n : Type u` for the converse | All observables `E`, with no positivity hypothesis; universal index types `κ : Type u` carry `Fintype` and `DecidableEq` |
| Bipartite sectors | Full `Matrix (m × n) (m × n) ℂ` for finite decidable `m,n` | Hilbert–Schmidt submodules; nonempty factors for the dimension formulas and the stated full-range decompositions |

The inner product convention is `⟨X,Y⟩ = trace (Y * Xᴴ)`, equivalently the usual cyclic Hilbert–Schmidt pairing. Matrices retain their full noncommutative multiplication. Right regular composition reverses multiplication: `R_(ab) = R_b ∘ R_a`.

## Generic Kraus contract

Write `Φ*_V(E) = ∑ i, star (V i) * E * V i` and assume the ordered completeness equation `∑ i, star (V i) * V i = 1`.

| Declaration in `OperatorAlgebra.NoncommutativeKrausChannel` | Exact mathematical content |
|---|---|
| `krausDual_sub_self_eq_sum_commutator` | `Φ*_V(E) - E = ∑ i, star (V i) * (E * V i - V i * E)` |
| `krausDual_eq_self_of_commute` | If every `V i` commutes with `E`, then `Φ*_V(E) = E` |
| `krausDual_add` | Additivity in the observable, without completeness |
| `krausDual_add_commuting_sub_self` | A summand `Z` commuting with every `V i` drops out of the defect of `Z + E` |
| `krausDual_eq_self_of_mem_center` | Every `E ∈ Set.center A` is fixed by every complete finite family |

These are ring identities. The completeness equation here is the one used for trace preservation of the forward action. It is not the opposite equation `∑ V i * star (V i) = 1`.

## Regular commutant contract

The existing `leftCommutant_eq_rightActionRange` identifies the commutant of all regular left multiplications with the range of regular right multiplication.

The new `rightAction_kraus_invariant` states, for arbitrary `B : A`,
`∑ i, L_(star (V i)) ∘ R_B ∘ L_(V i) = R_B` under the same ordered completeness equation.

The new `star_leftAction_star` states pointwise
`star (L_(star a) (star x)) = R_a x`.

The generic statement writes multiplication by `star (V i)` explicitly. It does not assume a Hilbert-space adjoint, positivity of `B`, a KMS state, or a Tomita operator. The existing complex Hilbert–Schmidt owner supplies `hs_adjoint_mulLeft` when that concrete adjoint interpretation is needed.

## Constructed degree-zero Hodge contract

Define `d_Q(X)_i = Q i * X - X * Q i` and
`δ_Q(W) = ∑ i, ((Q i)ᴴ * W i - W i * (Q i)ᴴ)`.
Their Lean owners are `differential` and `codifferential`. The Laplacian used here is the concrete composition `(codifferential Q).comp (differential Q)`.

| Declaration in `OperatorAlgebra.MatrixCommutatorHodge` | Content and extra hypothesis |
|---|---|
| `differential_adjunction`, `codifferential_eq_adjoint` | Trace cyclicity identifies `δ_Q` with Mathlib's native adjoint of `d_Q` |
| `ker_differential`, `ker_laplacian` | Both kernels are the native joint centralizer `(Subalgebra.centralizer ℂ (Set.range Q)).toSubmodule` |
| `range_codifferential` | The coexact range is that centralizer's Hilbert–Schmidt orthogonal complement |
| `existsUnique_centralizer_coexact` | Each matrix has a unique centralizer component whose residual is coexact |
| `centralizer_eq_center_of_adjoin_eq_top` | Ordinary algebra generation `Algebra.adjoin ℂ (Set.range Q) = ⊤` identifies the joint centralizer with the center |
| `ker_laplacian_eq_center`, `range_codifferential_eq_center_orthogonal` | Under that same generation hypothesis, the harmonic kernel is the center and the coexact range is its orthogonal complement |
| `trace_codifferential` | Every coexact output is traceless, without a generation hypothesis |
| `one_not_mem_range_codifferential` | For nonempty `n`, the identity is not coexact |
| `adjoin_matrixUnits_eq_top` | Matrix units provide an actual generating frame |
| `matrixUnits_coexact_square_counterexample` | For the full `2 × 2` matrix-unit frame, a coexact `X` satisfies `X * X = 1` while `1` is not coexact |
| `coexact_zero_overlap_nonzero_numerator` | An actual coexact `X` has `⟨1,X⟩ = 0` and `⟨1,X * X⟩ = 2` |

Only degree zero is constructed. There is no higher differential, proof of `d² = 0`, three-term complex decomposition, BRST/CE extension, or general BV operator in this change.

## Universal fixed-effects contract and causal bridge

The matrix owner uses the existing `Quantum.Choi.krausMap`. The bridge `krausDual_eq_krausMap_star` identifies its adjointed-family action with the generic `krausDual`.

The constructive separator is `resetKraus r i = Matrix.single r i 1`. Its completeness is `resetKraus_complete`; `krausMap_star_resetKraus` gives `Φ*(E) = Matrix.scalar n (E r r)`; `krausMap_resetKraus` gives the forward formula `X ↦ trace X • Matrix.single r r 1`.

For nonempty finite matrices:

- `fixed_by_all_indexed_kraus_iff_scalar` already needs only complete families indexed by `n`.
- `fixed_by_all_kraus_iff_scalar` quantifies all complete finite families indexed by `κ : Type u`.
- `fixed_by_all_kraus_iff_mem_center` identifies the same universal property with `E ∈ Set.center (Matrix n n ℂ)`.
- `fixed_by_all_kraus_iff_laplacian_eq_zero` combines that result with `ker_laplacian_eq_center`: for an ordinarily algebra-generating frame, universal fixedness is equivalent to `δ_Q (d_Q E) = 0`.

This is an operator fixedness theorem with the universal family quantifier displayed. It is not a claim that one fixed instrument or one state's scalar readout forces centrality.

The theorem `Quantum.BoundaryInstrument.exists_noncommuting_zero_scalar_anomaly` gives a positive normalized state, an effect between zero and identity, and a unitary with both noncommutation and nonzero operator defect, yet zero scalar expectation of that defect. Its witnesses are `ρ = I/2`, `E = e₀₀`, and `U = J_plus + J_minus` on `Mat2C`.

## Four-sector contract

Set `p = Fintype.card m` and `q = Fintype.card n`. The actual submodules are:

| Sector | Construction | Dimension for nonempty factors |
|---|---|---|
| `scalarSector` | The complex span of the bipartite identity | `1` |
| `leftSector` | The image of trace-zero matrices under `A ↦ A ⊗ₖ I` | `p² - 1` |
| `rightSector` | The image of trace-zero matrices under `B ↦ I ⊗ₖ B` | `q² - 1` |
| `mixedSector` | Orthogonal complement of the sum of the first three sectors | `(p² - 1)(q² - 1)` |

The orthogonality lemmas, `four_sector_sup`, constructed `sectorEquiv`, and `existsUnique_four_components` establish an actual unique linear decomposition. The dimension declarations are `finrank_scalarSector`, `finrank_leftSector`, `finrank_rightSector`, and `finrank_mixedSector`. The theorem `mixedSector_ne_bot` requires both cardinalities to be at least two.

The theorem `local_ranges_inf_eq_scalarSector` states that the full local ranges intersect in the scalar sector. The theorems `range_leftLift_eq`, `range_rightLift_eq`, and `mixedSector_eq_local_ranges_orthogonal` distinguish these full local ranges from their trace-zero parts.

The full `operatorEquiv` maps bipartite matrices to `Module.End ℂ (Matrix m n ℂ)`. Its multiplication law is `operatorEquiv_mul`; `operatorEquiv_kronecker_apply` gives `operatorEquiv (A ⊗ₖ Bᵀ) X = A * X * B`. The transpose is part of the convention, not optional.

The theorem `kronecker_mem_mixed` places products of two traceless matrices in the mixed sector. No tensor-product universal-property isomorphism onto that sector, entanglement criterion, or Kraus-channel sector classification is asserted.

## Established dependency order and reused owners

| Prerequisite | Result depending on it |
|---|---|
| Cyclic matrix trace and the concrete `PiLp 2` product | Adjoint identification, then kernel/range orthogonality |
| Ordinary `Algebra.adjoin = ⊤` | Joint centralizer becomes the center |
| Complete reset family and the existing matrix center classification | Universal Kraus fixedness becomes scalar/central fixedness |
| The preceding two center identifications | Universal Kraus fixedness iff degree-zero harmonicity |
| Regular associativity and ordered Kraus completeness | Right-action conservation, without a Hodge assumption |
| Kronecker pairing, orthogonality, and finite-dimensional linear algebra | Four-sector equivalence and dimensions |

The Hodge and four-sector constructions act on different spaces: matrices as degree-zero vectors, and operators on the matrix space. No unexplained identification merges their decompositions.

Reused owners include `NoncommutativeGradedTrace` (`operatorCommutator`), `MatrixTraceGeometry` (`trace_star_lie`), `PeirceSuperoperators.HilbertSchmidt` (`hs_inner_eq_trace` and the adjoint interpretation), `Canonical.MatrixTwoNoncommutativity`, `FiniteSpinAlgebra` (`Mat2C`, `J_plus`, `J_minus`), `ChoiCompletePositivity` (`krausMap`), and `BoundaryInstrument` (existing scalar normalizer/defect and positivity results). `ReplacementStateChannel` was inspected as the existing trace-times-state owner; the new reset family supplies a Kraus realization without creating a second replacement-channel API.

## Corrected intake claim ledger

| Intake assertion | Correction and present disposition |
|---|---|
| Hodge pieces are “never subalgebras” | Orthogonal decomposition supplies linear subspaces, not a universal failure of multiplication. The owner gives a specific coexact square counterexample. Exact forms in a differential graded algebra can be multiplicatively closed. |
| Nilpotency alone puts the identity in the harmonic kernel | It does not imply either `d(1) = 0` or `d†(1) = 0`. Here the actual degree-zero commutator differential annihilates the identity; no arbitrary-complex assertion is used. |
| Failure of Leibniz proves a second-order BV structure | A second-order condition and a compatible graded algebra would be additional mathematics. Neither is constructed. |
| The harmonic part is always the algebra center | The default result is the joint centralizer of `Q`. Center identification requires the explicit generation hypothesis. |
| The center is a disjoint third algebra beside an algebra and its commutant | The local ranges have a common scalar intersection. Trace-zero parts are used before forming the orthogonal sector sum. |
| Every nonzero mixed operator is entangling | Mixed-sector membership is a linear correlation statement, not an entanglement test. A product such as `Z ⊗ Z` illustrates the distinction; no entanglement theorem is added. |
| All Kraus superoperators live entirely in the mixed sector | Their scalar and local components need not vanish. Only the ordered full-matrix action and traceless-product membership are established. |
| Noncommutation forces a nonzero scalar anomaly | False; the normalized positive `2 × 2` witness has a nonzero operator defect with zero expectation. |
| Fixation by one instrument, even for all state readouts, forces the ambient center | The universal quantifier over complete families is essential. The identity family fixes every matrix. No fixed-family center converse is asserted. |
| A nonzero coexact component always produces nonzero disturbance | A particular family or state can fail to detect it. The bridge concerns universal operator fixedness. |
| Orthogonal Hodge sectors produce a literal infinite weak value | Zero overlap excludes the usual normalized quotient; Lean division is totalized. The owner proves zero overlap with nonzero numerator and defines no quotient at zero. |
| Weighted GNS, standard Hilbert–Schmidt, and arbitrary twins are automatically the same representation | The implemented carrier is explicit Hilbert–Schmidt matrices. Weighted-GNS transport and its right action need a proved map. |
| Zero in the essential spectrum always forces a nonclosed differential range | This needs additional hypotheses; a zero differential on an infinite Hilbert space has closed range. No infinite-dimensional range theorem is claimed. |
| Every thermodynamic KMS limit is Type III₁, with no abstract Hilbert tensor factorization | Both universal claims are rejected. Algebra type and a compatible type-I subsystem realization require precise model hypotheses; this change has no such limit construction. |
| Modular flow is unbounded, or `A ↦ JAJ` is the same linear anti-isomorphism as `A ↦ JA†J` | Real modular-time operators are unitary; domains matter for other modular powers. The two maps have different linearity/multiplication conventions. Only the explicit finite star-reflection identity is added. |
| A declared 15-node “graded” poset proves a unique physical synthesis | The supplied cover/rank data and the physical uniqueness inference are not promoted. The contract records actual theorem dependencies instead. |

## Remaining claims and acceptance boundary

Missing work includes a higher Hilbert complex; analytic domain and closed-range theory; a BV construction; weighted-GNS/KMS transport; Type II/III standard-form and thermodynamic-limit results; a theorem about global history or prefix probabilities; entanglement generation; and a semantic uniqueness theorem for the proposed poset. These require separate contracts and constructions.

The existing boundary instrument owner contains scalar normalizer identities, but this change does not prove the additional converse that scalar invariance for every normalized positive state is equivalent to operator fixedness. The current bridge uses operator equality directly.

Background for the unimplemented analytic questions: Arnold–Falk–Winther, [Hilbert complexes and finite element exterior calculus](https://arxiv.org/abs/0906.4325); Hiai, [von Neumann algebras and modular theory](https://arxiv.org/abs/2004.02383); Witten, [entanglement and quantum field theory](https://arxiv.org/abs/1803.04993). These are context, not Lean proof dependencies.

Acceptance requires the exact five-owner import closure, native checking at unchanged dependency pins, an axiom audit restricted to `propext`, `Classical.choice`, and `Quot.sound`, and recorded source/semantic review. Scoped heuristic success, exact recovery, staging, and a draft publication do not substitute for those checks.
