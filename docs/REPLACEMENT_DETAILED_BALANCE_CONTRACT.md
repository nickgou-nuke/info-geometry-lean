# Replacement detailed balance: source and theorem contract

Date: 2026-11-18. Continuation of the matrix-relaxation work in PR #406.
Carrier: the full native matrix algebra `Matrix (Fin n) (Fin n) ℂ`.
Products remain ordered; observables need not commute with the reference.

## Attached-source provenance

The user supplied these two primary papers after publication of the initial
replacement-relaxation PR. They motivate the next connecting theorem; their
statements do not substitute for Lean proofs.

| Attachment | SHA-256 | Relevant source |
| --- | --- | --- |
| `1609.05765v3.pdf` | `f139ff53d9dbc336bcbd5a91acd6c5e785135b0fbf7c18f07dccae39b67124f3` | Mittnenzweig and Mielke, *An entropic gradient structure for Lindblad equations and couplings of quantum systems to macroscopic models*, p. 5, equations (2.4)-(2.5); pp. 18-21, the entropy-gradient and GENERIC constructions. |
| `GibbsStatesJGSPPart1.pdf` | `4b1c6a1d0ab66b9234d8ce101fc356e9afcdb48fd81c7d04a18150d2ae9d5f8b` | Marle, *On Gibbs states of mechanical systems with symmetries*, Definition 3.1.2 and Propositions 3.2.2-3.2.3, Theorem 3.2.4, and Proposition 3.3.1. |

Primary public sources:
[Mittnenzweig-Mielke](https://arxiv.org/abs/1609.05765) and
[Marle](https://marle.perso.math.cnrs.fr/pdffiles/2020/GibbsStatesJGSPPart1.pdf).
The detailed-balance formula on p. 5 of the first attachment was checked
visually as well as through text extraction.

## Existing owners and bounded search

The search inspected canonical `lean/`, the parallel `src/` lane, relevant
imports and consumers, and a bounded context-preflight packet. The local
declaration/graph-index snapshots were absent; no graph freshness or exhaustive
external-library coverage is claimed.

| Existing owner | Reused or inspected content |
| --- | --- |
| `Quantum/ReplacementStateChannel` | Actual trace-one replacement map and complete positivity at every finite ancillary amplification. |
| `Quantum/ReplacementRelaxation` | Full-matrix relaxation, semigroup law, positive forward-time path, and actual derivative. |
| `Quantum/ReplacementHamiltonian` | Existing combined linear generator; setting its Hamiltonian input to zero gives the dissipator used here. |
| `Canonical/FiniteMatrixGibbsFunctional` | Native complex-linear `weightedTrace`, positive star-square readouts, full CFC Gibbs functional, and finite algebraic KMS boundary identity. |
| `Quantum/MatrixBoundaryPurification` | Actual CFC normalized Gibbs density, PSD status, commutation, and trace-one theorem with the nonempty-index hypothesis. |
| `Canonical/NoncommutativeGibbsBKMHessianBridge` | Actual additive log-partition derivative readout and its centered BKM covariance identification, with explicit self-adjointness and positive-partition hypotheses. This is source-reviewed context, not an additional import or newly certified result of this extension. |
| `OperatorAlgebra/ChiralPackingKMSDetailedBalance` | Finite population-ratio and modular-shift results. Its scalar conversion-rate theorem is distinct from the full-matrix weighted symmetry proved here. |
| `Canonical/MatrixEntropyUnitaryOrbit` | CFC-log and matrix-entropy invariance under unitary conjugation. This is an existing owner, not a new entropy theorem here. |

The bounded search found no existing owner proving the observable adjoint and
weighted detailed balance of the replacement generator. The new owner reuses
`weightedTrace`; it does not introduce a duplicate expectation functional.

## Exact mathematical contract

Write

$$
\varphi_\sigma(A)=\operatorname{Tr}(\sigma A),\qquad
R_\sigma(X)=\operatorname{Tr}(X)\sigma,\qquad
Q_\sigma(A)=\varphi_\sigma(A)I.
$$

The observable replacement map is constructed from the existing native
linear functional and scalar multiplication of the identity. For Hermitian
`σ`, this map is the Hilbert-Schmidt adjoint of state preparation; its scalar
range does not restrict the full noncommutative domain.

The explicit weighted pairing is

$$
\langle A,B\rangle_\sigma
=\varphi_\sigma(A^*B)
=\operatorname{Tr}(A^*B\sigma).
$$

This is the right-weighted pairing used by equation (2.4) of
Mittnenzweig-Mielke. It is not replaced by a pairing with two factors of
`σ^(1/2)`. No new `InnerProductSpace` instance is placed on the current
matrix operator-norm carrier.

The dissipative state generator and observable generator are

$$
\mathcal L=\gamma(R_\sigma-\mathrm{id}),\qquad
\mathcal L^{\mathrm{obs}}=\gamma(Q_\sigma-\mathrm{id}),\quad \gamma\in\mathbb R.
$$

The state side reuses `ReplacementHamiltonian.generator 0 σ γ`.

| Result | Required hypotheses |
| --- | --- |
| Trace duality of `Q` and `R` | None for the bilinear trace form. |
| Hilbert-Schmidt adjoint identity | Hermitian `σ`. |
| `R(Aσ) = Q(A)σ` and corresponding generator intertwining | No positivity or normalization. |
| `Q(I)=I`, `Q²=Q`, and stationary `Lσ=0` | `trace σ = 1`. |
| Weighted symmetry of the observable generator | Hermitian `σ`; real rate. |
| Centered covariance/Dirichlet identity | Hermitian, trace-one `σ`. |
| Nonnegative diagonal Dirichlet readout | PSD, trace-one `σ`; nonnegative rate. |
| Positive-definite weighted Hilbert interpretation | Strict positivity of `σ`; not inferred from PSD alone. |

The adjoint identity has its actual two different maps:

$$
\operatorname{Tr}((Q_\sigma A)^*X)
=\operatorname{Tr}(A^*R_\sigma X).
$$

The Lean theorem states the conjugate-equivalent orientation
`Tr(star (R X) * A) = Tr(star X * Q A)` of this Hilbert-Schmidt identity.

In particular, `R` is generally not Hilbert-Schmidt self-adjoint:
`R(I)=nσ`, while `Q(I)=I` for normalized `σ`.

The detailed-balance identities are

$$
\mathcal L\sigma=0,\qquad
\mathcal L(A\sigma)=\mathcal L^{\mathrm{obs}}(A)\sigma,\qquad
\langle\mathcal L^{\mathrm{obs}}A,B\rangle_\sigma
=\langle A,\mathcal L^{\mathrm{obs}}B\rangle_\sigma.
$$

Define the centered observable `Cσ(A)=A-φσ(A)I`. The Dirichlet
identity preserves the ordered product:

$$
-\langle A,\mathcal L^{\mathrm{obs}}B\rangle_\sigma
=\gamma\left(\varphi_\sigma(A^*B)
 -\overline{\varphi_\sigma(A)}\varphi_\sigma(B)\right)
=\gamma\varphi_\sigma(C_\sigma(A)^*C_\sigma(B)).
$$

Positivity on the diagonal is a matrix-positive-cone consequence. The
reference need not commute with either observable. The actual CFC Gibbs
consumer supplies Hermitian/PSD and normalization hypotheses from existing
theorems, retaining the normalization theorem's nonempty-index condition.

The new owner exposes `trace_replacement_hilbertSchmidt_adjoint`,
`generator_right_weight`, `observableGenerator_weighted_symm`,
`dirichlet_eq_covariance`, and `dirichlet_self_nonneg`. The Gibbs owner
consumes these results in `normalizedGibbs_dissipator_stationary`,
`normalizedGibbs_dissipator_right_weight`,
`normalizedGibbs_dissipator_weighted_symm`, and
`normalizedGibbs_dirichlet_nonneg`.

## Souriau temperature and noncommutative representation boundary

Marle's generalized inverse temperature is an element `β ∈ g` of a real
finite-dimensional Lie algebra; the moment map takes values in its dual.
The scalar Gibbs exponent is the pairing `⟨J(x),β⟩`. The normal-convergence
domain is an explicitly controlled integrability domain, not the unrelated
`admissibleBeta := 1 < β` tag in the matrix Gibbs owner. The latter's actual
finite CFC Gibbs results apply to all real scalar parameters.

A chosen compatible operator representation can turn the parameter into a
Hermitian charge combination `Bβ = Σ βa Qa`; the charges need not commute.
Such a representation and its real/internal-complex compatibility must be
constructed before identifying this with a geometric Lie algebra action.
The existing finite Gibbs mean operator `E[J] • I` is an expectation readout,
not a representation of noncommuting charges.

The repository already has a noncommutative additive Gibbs Hessian/BKM
connection and matrix unitary entropy invariance. This extension does not
duplicate them. The BKM owner uses `exp(H) / Tr(exp H)`: to match the physical
family `exp(-Q(β)) / Z`, its exponent is `H = -Q(β)` and its tangent directions
are `-Q(X)` and `-Q(Y)`. The finite matrix Gibbs owner already uses
`exp(-βH)` and needs no additional sign reversal. Marle's entropy constancy
on adjoint orbits gives an orbit inside an entropy level; it does not
identify every level with one orbit.

Source review also qualifies Theorem 3.3.4 on pp. 36-37 before any later
orbit-metric formalization. The zero-mean normalization `J - E_J(β)` fixes its
associated cocycle. The condition `Θβ(β) = 0` alone does not uniquely determine
a representative of the cocycle's cohomology class: for an equivariant
`SO(3)` coadjoint sphere, the zero cocycle and the distinct coboundaries
`X ↦ -ad_X* μ` with nonzero `μ` parallel to `β` all satisfy that condition.
Proposition 3.3.3 gives
`Γβ([X,β],Y) = -⟨Θβ(X),Y⟩`; reversing the bracket reverses this sign.
The theorem statement uses the correct opposite bracket order, while the
printed proof does not preserve that sign. Neither the overstrong uniqueness
claim nor the proof's sign slip is a premise of this Lean extension.

## Boundaries and validation

Detailed balance here concerns the dissipator. The compatible Hamiltonian
observable derivation is weighted skew, and the full Hamiltonian-plus-bath
generator is not asserted to be weighted symmetric.

The Dirichlet form is a weighted quadratic covariance. It does not construct
the state-dependent Kubo-Mori entropy-gradient operator of the first paper,
prove relative-entropy decay, or supply closed GENERIC degeneracy conditions.
Bath variables, driven Carnot strokes and efficiency, NESS currents, geometric
holonomy, and tensor-flip/double-commutator realization remain distinct
construction tasks.

Acceptance uses the existing shared-lock scoped checker with the four
`Quantum.ReplacementRelaxation`, `Quantum.ReplacementHamiltonian`,
`Quantum.ReplacementDetailedBalance`, and `Quantum.ReplacementGibbs` targets.
Fresh CI requires successful compilation, zero selected-owner compiler
warnings, and native axiom auditing with only `propext`, `Classical.choice`,
and `Quot.sound`. Development cache reuse, source scans, and independent
mathematical review are reported separately. The exact accepted source head
and receipt are recorded in the upstream PR checks and description.

The prepublication strict placeholder scans of the new owner and modified
Gibbs consumer found no findings. The warning-strict semantic-vacuity scan
of all four owners returned six short-helper warnings and no error findings.
Four belong to the previously reviewed baseline. The two new warnings are
`observableReplacement_apply` and `observableGenerator_apply`: both are
definitional evaluation lemmas, marked `simp`, for the constructed linear
maps. Their `rfl` proofs expose these definitions to the substantive ordered
trace and covariance proofs; they assert no physical property. The scan's
nonzero warning exit is retained, separately from compiler-warning acceptance.

The first development checker attempt reported 55 successful module checks
and rejected the new covariance proof's subtraction layout. It also reported
the deprecated `Matrix.star_mul` alias. The reviewed repair matches Lean's
actual expansion order and uses `StarMul.star_mul`; all theorem statements,
hypotheses, and ordered matrix products are unchanged. The failed development
receipt is retained separately from subsequent acceptance evidence. Fresh CI
then required an explicit final `rfl` to identify `weightedPairing` with its
weighted-trace definition after the covariance rewrites. That independently
reviewed definitional closure changes no mathematical statement.

The previously observed root Lake path-dependency blocker remains outside
this scoped acceptance; no whole-package certificate is implied.
