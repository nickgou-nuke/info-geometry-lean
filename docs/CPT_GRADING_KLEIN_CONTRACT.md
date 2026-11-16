# CPT grading intake: theorem contract and corrections

## Provenance and intended scope

The input is `Pasted text(20261116-183518).txt`, preserved without editing in
[`sources/cpt-grading-intake-20261116.txt`](sources/cpt-grading-intake-20261116.txt).
Its SHA-256 is
`7c029718a61a17195b60fe3035d92371d6ef0095fcb2d40cec711e1ab1dfb5f5`.
The implementation starts from upstream main
`08c34e03f610b452e03422037949196dc7d92d6d`.

The requested mathematical content is conjugate-linear negative-square
operators, independent gradings, Klein twisting, ordered sign cancellation,
and information loss. The input's psychological descriptions are provenance,
not mathematical hypotheses. Its final physical necessity/uniqueness claim
does not follow from the proposed dependency poset.

The implemented scope is algebraic: arbitrary complex modules, associative
real/rational operator algebras, and monoids of operators. No finite-dimensional
or commutative replacement is made for the general operator statements.
The existing concrete Kramers example remains a construction on `Fin 2 → ℂ`.

## Source search and owner reuse

The review searched canonical `lean/InfoGeometry`, related `src/InfoGeometry`
and `proofs` hits, actual definitions, import edges, and consumers. It did not
rebuild an external declaration graph or claim that a graph service was fresh.
The following declarations determine the mathematical boundaries.

| Claim | Existing owner and declarations | Treatment |
| --- | --- | --- |
| Complementary projectors of an involution | `OperatorAlgebra.Z2ProjectorWeights`: `projectorPlus`, `projectorMinus`, four projector product laws, `projectorPlus_add_projectorMinus`, `projectorWeight_one_neg_one` | Imported directly into the new Klein owner; projector formulas and proofs are reused. |
| A constructed Kramers operator | `Quantum.ComplexKramersAntiunitary`: `timeReversal`, `timeReversal_sq`, `timeReversal_smul`, `timeReversal_antiunitary`, `timeReversal_kramers_orthogonal` | Existing operator retained; generic eigenvector obstruction specialized to it. |
| Exclusion of fixed nonzero Kramers vectors | `timeReversal_ne_self_of_ne_zero` | Existing API retained; its longer proof is replaced by the new generic eigenvector theorem. |
| Anti-linear inversion of scalar unitary phases | `Quantum.KramersPhaseGlideRepresentation.kramers_phase_inverse` | Existing result retained; the new twist concerns an operator depending on the grading. |
| Independent involutive gradings | `OperatorAlgebra.ThreeZ2OperatorGradings`: `gradingConjugation_involutive`, `gradingConjugations_commute`, `hasZ2Parity_mul`, `triZ2Parity_mul` | Existing coverage cited; no duplicate grading carrier or interpretation of statistics as chirality. |
| Chirality/eigenvalue exchange | `Physics.ChiralEigenspaceEquivalence.map_eigenspace`, `eigenspaceEquiv`; `Physics.FiniteChiralSpectralSymmetry.anticommuting_maps_eigenmode_neg` | Existing native linear-map/eigenspace results retained. No new claim of nonfactorizability of physical CPT. |
| Information loss after channel iteration | `PeirceSpine.PeirceCoarseGrainedDynamics.no_density_recovery_after_evolution`, `exists_cptp_coarse_grained_no_recovery` | Reused as the exact corrected statement in place of a claimed general CPT-breaking theorem. |
| Exact density-recovery boundary | `PeirceSpine.PeircePositiveCollision.density_recovery_iff_trivial` | Existing characterization: universal recovery is equivalent to `P = 0 ∨ P = 1`. |
| Pinching covariance despite information loss | `PeirceSpine.PeirceChannelDynamics.corner_channel_pinching_covariant`, `PeirceCoarseGrainedDynamics.evolve_pinching` | Covariance is compatible with the preceding no-recovery theorem. |
| Semilinear channel reversal | `Quantum.SemilinearBoundaryReversal.sheetConj_krausMap`, `reversed_trace_preserving_iff` | Existing full matrix algebra result: reversed trace preservation requires original unitality. |

Searches for Klein-root, statistics-phase, and anticommutator-to-commutator
formulas did not locate this exact construction among the inspected owners.
`KleinBottleTwistedCommutantBridge` and `KleinianTwist` have different carriers
and contracts; their names do not provide this phase construction.

`ModularSignCPT.ModularSignCPTRelations` constructs a real operator product from
supplied involution and anticommutation laws. Related datum structures and
`CPTAlgebraCommutantBranch` include supplied modular/commutant conditions. Those
fields are not promoted to independent constructions. The finite
`Dynamics.BisognanoWichmann` owner explicitly distinguishes its finite identities
from analytic Bisognano–Wichmann theory for local quantum field algebras.

## New theorem spine

### Conjugate-linear negative squares

`InfoGeometry.Algebra.AntilinearSquare` uses native `V →ₗ⋆[ℂ] V`.
For an arbitrary complex module, the explicit hypothesis
`∀ v, T (T v) = -v` implies that `T v = c • v` forces `v = 0`, for every
`c : ℂ`. The proof uses scalar norm-square positivity and semilinearity; it
does not assume finite dimension, an inner product, or antiunitarity.

The real-linear restriction is constructed on the same underlying module. In
an associative real algebra the averaging expression satisfies

\[
\left(\frac{1+t}{2}\right)^2-\frac{1+t}{2}
=\frac{t^2-1}{4}.
\]

Consequently `t*t = -1` gives defect `-(1/2) • 1`; nontriviality is explicit
when concluding failure of idempotence. The expression is never claimed to
be a complex-linear projection when `t` comes from a conjugate-linear map.

The old `ComplexKramersAntiunitary` owner adds
`timeReversal_eigenvector_eq_zero` and reuses it in its fixed-vector theorem.

### Klein twisting with an internal phase

`InfoGeometry.OperatorAlgebra.KleinTwist` works in
`[Ring A] [Algebra ℚ A]`, with existing projectors
`P₊ = projectorPlus Γ`, `P₋ = projectorMinus Γ` and

\[
Z(\Gamma,j)=P_+-jP_-.
\]

The phase is an element of the operator algebra. For a real operator algebra
it can be an internal complex structure; in a complex algebra the canonical
choice is `j = i • 1`. Assumptions are only imposed where used:

- `Γ*Γ = 1` for projector multiplication;
- `j*j = -1` for square and inverse laws;
- `Commute j Γ` for compatibility of the phase and grading;
- `star Γ = Γ` and `star j = -j` for native unitary membership;
- `Commute j A₁`, `Commute j C` and both oddness equations for the locality twist.

`twist_mul` retains the ordered coefficient product `j*k`. The main results
are `twist_sq`, `twist_fourth`, `twist_mul_neg_phase`,
`twist_neg_phase_mul`, `star_twist`, and `twist_mem_unitary`.
`orderOf_twist` proves exact order four under `Γ ≠ 1`; `twist_one` covers the
degenerate grading. `twist_mul_one_add_phase` supplies the division-free input
formula `Z*(1+j) = 1+j*Γ`.

For two odd operators the exact statement is

\[
ZCZ^{-1}=j\Gamma C,\qquad
[A_1,ZCZ^{-1}]=-j\Gamma(A_1C+CA_1).
\]

`twisted_commute_iff` proves the equivalence of twisted commutation and
anticommutation. Its reverse implication uses an explicit left inverse of
`-j*Γ`; no no-zero-divisors hypothesis or scalar reduction is used.
`map_twist` proves phase reversal under an actual rational algebra
homomorphism fixing the grading and negating the phase.

### Sign cancellation

`commuting_square_roots_involutive` and `twisted_product_involutive` are
theorems in an arbitrary monoid. If `T` and `U` commute, both square to `Γ`,
and `Γ*Γ = 1`, then `(T*U)*(T*U) = 1`. Adding a twist preserves this square
under the explicitly stated intertwining and inverse laws.

These statements prove operator identities. Identifying the resulting
involution with the modular conjugation of a represented von Neumann algebra
requires a separate construction and compatibility theorem.

## Corrected and unpromoted claims

| Input claim | Correct disposition |
| --- | --- |
| Positive energy and any invertible reversing symmetry force antiunitarity. | Missing a symmetry/isometry framework. For example `2` times complex conjugation reverses scalar unitary evolution but is not isometric. This PR assumes conjugate linearity and proves its consequences. |
| Every antiunitary has no eigenvectors. | False for ordinary conjugation; the negative-square hypothesis is essential. |
| `Θ² = Γ` follows from abstract grading data. | Representation-dependent input; not derived here from a grading alone. |
| Negative square forces an irreducible quaternionic representation. | Irreducibility is additional. The proved eigenvector obstruction makes no classification claim. |
| Klein phase always has exact order four. | Requires `Γ ≠ 1`; otherwise the constructed twist is `1`. |
| Omitting the twist necessarily destroys involutivity. | False under the input's own relations: `(ΘU)² = Γ² = 1` already. Twisting changes the locality relation. |
| The fermionic one-particle sector supports nonzero odd endomorphisms internally. | If `Γ = -1` on the whole carrier, oddness forces such an endomorphism to vanish in characteristic zero. Odd fields act between sectors of a larger graded space. |
| A parity symmetry annihilates states in a purely chiral carrier. | The algebraic argument obstructs an invertible chirality-flipping endomorphism on that carrier; it does not describe a valid parity symmetry as annihilation. |
| Four-dimensional Lorentzian spacetime universally has KO-dimension six. | The cited Connes signs concern a finite internal geometry. No universal Lorentzian KO identification is asserted. |
| An algebraic involution is automatically Tomita modular conjugation. | Missing represented algebra, cyclic/separating vector, Tomita operator, domains, polar decomposition, and identification. |
| A single imaginary boost is total spacetime inversion. | It reverses time and one spatial coordinate; total inversion additionally uses a rotation. Real modular flow is a group, while imaginary continuation has domain conditions. |
| A finite bit tower automatically triggers Nielsen–Ninomiya. | Lattice/locality/translation/chirality hypotheses must be established. No lattice no-go result is inferred from finite algebra alone. |
| Failure of Lorentz invariance implies CPT failure by Greenberg. | This reverses the relevant implication. |
| Any Kraus rank above one forbids all recovery. | Input/output dimensions and the meaning of inverse matter; adding a fixed mixed ancilla has a CPTP left inverse. The repository's actual state-collision theorem is used. |
| Nonrecoverability means symmetry covariance is broken. | Distinct properties. The existing pinching-covariance and no-recovery theorems can hold together. |
| The displayed graph's terminal vertex proves unique physical synthesis. | A chosen dependency order does not prove missing physical implications. The supplied height also skips values along covers and is not a graded-poset rank as written. |

## Actual dependency order

The proof dependencies form three separate branches:

1. Native conjugate-linear scalar transport and complex norm-square
   nonnegativity → generic eigenvector obstruction → existing Kramers
   specialization → shortened fixed-vector proof.
2. Existing involution projectors → ordered twist product → square/inverse
   laws → exact order and unitary membership; projector exchange for odd
   operators → twisted commutator → equivalent locality conditions.
3. Explicit monoid commutation and square relations → untwisted involutivity
   → phase-intertwined involutivity.

The information-loss and chirality results are existing independent owners.
No new reachability graph or assertion of physical inevitability is added.

## Primary references for interpretation boundaries

- Crismale, Duvenhage and Fidaleo, [C*-fermi systems and detailed balance](https://arxiv.org/pdf/2010.07296), §5, equations (5.5)–(5.6): the convention `P₊ - i P₋` and its conjugation action.
- Connes, [Noncommutative Geometry and the standard model with neutrino mixing](https://arxiv.org/pdf/hep-th/0608226), introduction and §2.1: the finite internal KO-six geometry is distinct from the four-dimensional spacetime factor.
- Nayak and Sen, [Invertible Quantum Operations and Perfect Encryption of Quantum States](https://arxiv.org/pdf/quant-ph/0605041), Theorem 2.1: recoverable operations can append a fixed mixed ancilla when dimensions differ.
- Greenberg, [CPT Violation Implies Violation of Lorentz Invariance](https://arxiv.org/abs/hep-ph/0201258): direction of the implication, not its converse.
- Friedan, [A Proof of the Nielsen–Ninomiya Theorem](https://www.physics.rutgers.edu/~friedan/papers/Commun_Math_Phys_85_481-490_1982.pdf): the lattice theorem requires its stated structural hypotheses.

## Validation receipt

Native validation and the final independent acceptance receipt will be
recorded here after completion. Source review has passed the mathematical
contract; that review is not a substitute for Lean elaboration or axiom audit.
Dependency pins and root package configuration are unchanged.
