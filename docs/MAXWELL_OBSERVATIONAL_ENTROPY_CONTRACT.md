# Maxwell prose: two-projector observational entropy contract

## Provenance and acceptance boundary

The intake is `Pasted text(20261117-134835).txt`, 39,770 bytes and 205 lines,
SHA-256 `8c5c0a9caccde73f643e18476a1baa182fa1957b50a57a6b6143d17bc8455c49`.
It combines a Maxwell-demon tutorial audit with additional physical assertions
and a proposed conceptual dependency graph. Its prose is a source of theorem
targets, not a set of Lean axioms.

The identified tutorial is A. de Oliveira Junior, Jonatan Bohr Brask, and Rafael
Chaves, *A Friendly Guide to Exorcising Maxwell's Demon*, PRX Quantum **6**,
030201 (2025), DOI [10.1103/phkv-wrsd](https://doi.org/10.1103/phkv-wrsd).
The [published PDF](https://journals.aps.org/prxquantum/pdf/10.1103/phkv-wrsd)
has 47 pages; the [arXiv record](https://arxiv.org/abs/2503.07740) is a separate
versioned source. Retrieved text was checked; no visual PDF inspection is
claimed. The public PDF was not identified with an unavailable attachment
from another conversation.

Initial repository search started at
`08c34e03f610b452e03422037949196dc7d92d6d`. A concurrent draft,
[PR #397](https://github.com/nickgou-nuke/info-geometry-lean/pull/397), appeared
for the same intake during implementation. This PR is stacked on its exact
head `80ff2c99e31ec5fb263ac31553ccbd3e53635d77` and adds the operator-log and
support consequences it leaves open. The fixed environment is Lean
`v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Dependency pins, the shared lock, and gate commands remain unchanged. The
existing post-build workflow receives the syntax repair recorded below.

The new CFC owner is
`InfoGeometry.Canonical.TwoSheetObservationalEntropy`, on full matrices over
an arbitrary finite index type. The companion
`InfoGeometry.Canonical.TwoSheetProjectiveCoarseGraining` connects it to the
parent PR's actual complex-linear channel on `Matrix (Fin d) (Fin d) ℂ`.
The entropy scope is two complementary star projections.
Native compilation, declaration-axiom audit, source review, and integration
gates are separate acceptance records. Until the native record passes, the
new proofs are source candidates, not kernel-accepted theorems.

## Formal objects and exact target

Let `Mat = Matrix n n ℂ` for an arbitrary finite index type with decidable
equality. Let `P` be a star projection with `P ≠ 0` and `P ≠ 1`,
let `Q = 1 - P`, and let `ρ` be positive
semidefinite with `trace ρ = 1`. Write

\[
d_P=\operatorname{Re}\operatorname{tr}P>0,\qquad
d_Q=\operatorname{Re}\operatorname{tr}Q>0,
\]
\[
p=\operatorname{Re}\operatorname{tr}(\rho P),\qquad
q=\operatorname{Re}\operatorname{tr}(\rho Q).
\]

The owner derives these positive volumes from the two nonzero projection
ranges. It does not assume positive outcome probabilities. The construction is the actual matrix

\[
\bar\rho=\frac{p}{d_P}P+\frac{q}{d_Q}Q.
\]

The source derives positivity, normalization, and preservation of the
two Born probabilities. It also derives idempotence of the coarse-graining map. Neither `[ρ,P]=0` nor diagonal `ρ` is a premise.
In particular this map generally differs from the pinching map
`ρ ↦ PρP + QρQ`: it also makes each block uniform.

### Connection to the existing general channel

The parent owner `Quantum.ProjectiveCoarseGraining.blockUniformChannel`
constructs a complex-linear map for a finite projective family, using the
complex coefficients `trace(P_i * X) / trace(P_i)`. The adapter supplies the
actual family `![P, 1-P]`, its projection/orthogonality/completeness laws,
and equality of that channel's output with `coarseGrainedState ρ P` for
positive `ρ`. This equality uses realness of the positive trace pairings,
not a commutation assumption. It then transports the logarithm, entropy,
and support statements to that channel.

The equality is intentionally not asserted for arbitrary complex inputs:
for nonzero `P`, the general channel fixes `iP`, while the real-coefficient
construction sends it to zero. The arbitrary-matrix total-CFC identities
and the physical positive-input channel interpretation remain distinct.


Use the existing actual matrix entropy

\[
S(A)=-\operatorname{Re}\operatorname{tr}(A\,\mathrm{CFC.log}(A))
\]

and define the two-outcome observational expression by

\[
S_{\rm obs}(\rho;P)
=p(-\log p+\log d_P)+q(-\log q+\log d_Q).
\]

The source identities are

\[
\operatorname{Re}\operatorname{tr}(\rho[-\log\bar\rho])
=S_{\rm obs}(\rho;P)=S(\bar\rho),
\]
\[
S_{\rm obs}(\rho;P)-S(\rho)
=\operatorname{Re}\operatorname{tr}
  \bigl(\mathrm{umegakiKernel}(\rho,\bar\rho)\bigr).
\]

The logarithms are evaluated using native continuous functional calculus,
with the existing `PeirceSpine.cfc_twoSheet` theorem. The right side reuses
the existing ordered operator kernel `ρ * (log ρ - log σ)`.
It is not defined to be the desired entropy difference.

The algebraic entropy identities are stated for arbitrary full `ρ`, using
total CFC. Positivity and trace-one hypotheses belong to the separate density
theorems; positivity also supplies the support theorem below. This broader
algebraic statement does not make an arbitrary matrix a quantum state.

### Zero probabilities and support

Mathlib's `Real.log` and matrix CFC logarithm are total. Their value at zero
alone does not justify a physical relative-entropy interpretation for an
arbitrary singular pair. Here the source supplies the support implication:

\[
p=0\Longrightarrow P\rho=\rho P=0,
\qquad
\ker\bar\rho\subseteq\ker\rho.
\]

The first implication uses positivity and a genuine Gram trace, with the
existing `BoundaryInstrument.gram_trace_re_eq_zero_iff`; the second combines
the two complementary projections. Thus zero-probability sheets make no
contribution and are not silently excluded. No proof may assume the desired
support inclusion or the final entropy identity as a structure field.

### Deliberately open analytic consequences

This owner does not establish quantum relative-entropy nonnegativity,
its equality characterization, the maximum-entropy principle, or entropy
monotonicity under arbitrary unitary motion. The exact gap identity is a
useful input to those results, but is not their proof.

If those missing inequalities are later established, an initially
coarse-grained state together with unitary invariance gives a comparison
with the *initial* observational entropy. This is not monotonicity between
every pair of later times. Strict increase also requires departure from
the equality case. The existing `matrixEntropy_unitary_conjugate` theorem
currently requires strict positivity; extending its use to every singular
density needs the corresponding native extension.

For the literature comparison, Strasberg and Winter,
[PRX Quantum 2, 030202 (2021)](https://doi.org/10.1103/PRXQuantum.2.030202),
Lemma 4 characterizes entropy saturation by the coarse-grained state; Lemma 5
compares later entropy with a saturated initial state. The exact projective
gap above is derived here from the logarithm's spectral decomposition and
the preserved Born probabilities. Those literature inequalities are not
imported as assumptions or claimed as native results of this owner.

## Owner search and reuse

The search covered related names and alternate formulations in canonical
and source Lean roots, imported declarations and their actual consumers,
pinned Mathlib matrix/CFC/rank APIs, the latest 70 updated upstream PRs, and
indexed PR searches for Maxwell, observational entropy, and finite baths.
A final publication-time refresh found PR #397; its actual changed owners
were read and the implementation was adapted to use its channel. This is
a bounded search, not a claim about unpublished or unindexed work.
Documentation, external references, and prior reports were navigation aids;
the declaration types and proofs determined reuse.

| Existing owner | Actual reusable content | Boundary |
|---|---|---|
| `Canonical.MatrixEntropyUnitaryOrbit` | Actual `-Re trace (ρ * CFC.log ρ)` and native unitary transport | Its unitary entropy theorem assumes strict positivity. |
| `OperatorAlgebra.PeirceSpine.TwoSheetFunctionalCalculus` | `cfc_twoSheet` and `neg_log_twoSheet` for weighted complementary star projections | A spectral formula, not a density or entropy inequality. |
| `OperatorAlgebra.NoncommutativeRenyi` | Ordered `umegakiKernel` and positive-functional readouts | No quantum Klein inequality is supplied here. |
| `Quantum.BoundaryInstrument` | Full-matrix Gram trace nonnegativity and its exact zero criterion | Supplies support ingredients, not a coarse-graining entropy theorem. |
| `Canonical.FiniteMatrixGibbsFunctional` | `gibbsDensity_strictlyPositive`, `gibbsDensity_isUnit`, nonzero partition | These finite Gibbs results hold for every real inverse temperature; unrelated `admissibleBeta` is not their premise. |
| `Canonical.FiniteMatrixGibbsFaithfulness` | Weighted-trace faithfulness derived from positive invertible density | Already consumed by the finite-seed Tomita/closability chain. |
| `Quantum.MatrixBoundaryPurification` | Normalized Gibbs positivity/trace and actual square-root purification | Purification does not prove the converse pure-marginal product theorem. |
| `Quantum.FinitePartialTrace` | Actual finite partial trace, trace preservation, diagonal evaluation | No support/rank bound here. |
| `QuantumContext.MatrixStagePartialTrace` at the original baseline | `trace_mul_partialTraceSecondOp`, general in both finite dimensions | PR #397 moves its statement/proof unchanged into `Quantum.FinitePartialTrace`, retaining its qualified namespace and old import reachability. |
| `OperatorAlgebra.PeirceSpine.BlackHoleFiniteMarginal` | Positivity of actual partial trace | Does not bound joint rank by marginal rank. |
| `Quantum.ReplacementStateChannel` | Actual CPTP replacement map and amplification | Does not construct a faithful finite-bath unitary implementation. |
| `Canonical.RealProjectionRankConjugation` | Range equivalence under conjugation, over arbitrary division rings | More general than its filename; not tensor-rank multiplication. |
| `Clifford.Cl11TensorTowerKroneckerRangeRank` | Actual real binary-tower rank doubling | Not yet arbitrary finite complex tensor factors. |
| `Physics.InformationEnergy.TraceErasure` in [PR #358](https://github.com/nickgou-nuke/info-geometry-lean/pull/358), head `473d39724c43ee5cef8ba971ff82dfe42ca084f4` | Reset fibers/kernel/range and obstruction to conjugation on the same algebra | A larger bath changes the problem. |

The scalar `LandauerDissipationNativeBridge` and finite Boltzmann macroentropy
owners are not substitutes for a full-matrix quantum entropy identity.
The present construction retains the arbitrary source matrix and uses
scalar probabilities only as the explicitly defined trace readout.

## Corrected claim ledger

All line references below refer to the frozen intake, not to the tutorial.
The ledger separates mathematical analysis from native Lean acceptance.

| Intake claim | Corrected statement and disposition |
|---|---|
| Lines 8, 165–167: finite faithful-bath exact erasure | Sound under its product-input, mixed-system, faithful-finite-bath, and unitary hypotheses. Gibbs faithfulness already has an owner. PR #397 now supplies projection-valued partial-trace support, tensor rank, and this obstruction as candidate source; native acceptance remains separate. |
| Lines 8, 111, 133, 197: ideal measurement and conjunction of divergent resources | Neither follows from the rank argument. A pure ancilla changes the preparation assumptions. Separate models and resource theorems are required. |
| Lines 11–12, 75–77, 170: measurement/reset minima and a cost “gauge” | Work lower bounds do not establish attainable equality. Zero measurement work implies `ΔF ≤ −TI`, not equality. An initially thermal memory does not imply `ΔF=0`; that value gives a nonnegative reset bound, not a zero-cost reset protocol. Changing the memory state or Hamiltonian changes the physical specification. |
| Line 14: quantum-wall spectra and low-temperature work | A central wall does not multiply every original energy level by four; states already vanishing at the wall are unaffected. Protocol and work-sign conventions matter. Both quoted absolute bosonic and fermionic works vanish as temperature goes to zero; their ratios to `k_B T` have different limits. These model-specific spectral calculations are not this PR's entropy theorem. |
| Lines 16, 59: entropy stasis invalidates nonequilibrium free energy | Unitary entropy invariance does not invalidate the definition `F=E−TS`. The relation to macroscopic entropy, strong coupling, and work constraints requires its stated model. |
| Line 57: four-part entropy/heat ledger with a pure initial battery | Final battery entropy is missing. The correct product-input ledger retains `ΔS_W`, or assumes it is zero. See the counterexample below. |
| Lines 160–163: correlated Reeb–Wolf identity | With initial bath marginal Gibbs and global unitary dynamics, the correction is `I_final−I_initial`. Initial correlations permit but do not force a violation of the uncorrected bound. The actual matrix identity and nonnegativity are open here. |
| Line 153: strict Gibbs energy and entropy monotonicity | A scalar Hamiltonian defeats unrestricted strictness. For a nonconstant Hamiltonian, entropy monotonicity also needs the intended positive-temperature interval. |
| Lines 149, 181–182: observational entropy | The new bounded target is the two-projector full-matrix construction and exact gap identity, including support at zero probabilities. Arbitrary projective families and entropy inequalities remain separate work. |
| Lines 20, 87, 174, 177: finite-bath scaling | For fixed nonzero entropy reduction and `d=d₀^n`, `d₀>1`, the displayed lower-bound expression scales as `n⁻²`. A lower bound does not make every protocol's dissipation `Θ(n⁻²)`. |
| Lines 22, 86, 88–89, 149, 153, 174–178: finite time, zero temperature, stopping | Finite-time coefficients, calorimetric laws, and stopped fluctuation identities need the actual model, integrability, and stopping hypotheses. Separate lower bounds cannot generally be added. These are not consequences of the algebraic gap identity. |
| Lines 116–138: graded causal poset and terminal synthesis | A topological ordering or longest-path height need not be a graded rank: covering edges can skip heights. Neither a unique terminal physical principle nor the proposed operator blocks is constructed by this prose. |

### Missing battery entropy: a concrete mathematical counterexample

Take equally sized qubits `S` and `W` with zero Hamiltonians. Initially let
`S` be maximally mixed and `W` pure, and leave `M` and the Gibbs bath unchanged.
A SWAP on `S,W` is energy conserving. It gives

\[
\Delta S_S=-\log 2,\quad \Delta S_W=\log 2,
\quad Q_B=\Delta S_M=0.
\]

Thus the intake's line-57 expression is negative. Initially pure does not
mean finally entropy preserving. For initially product states the corrected
identity is

\[
\Delta S_S+\Delta S_M+\Delta S_W+\beta Q_B
=I_{\rm total,final}+D(\sigma_B\Vert\gamma_B)\ge0,
\]

once entropy additivity, unitary invariance, the Gibbs logarithm, and the two
nonnegativity theorems are supplied. This counterexample and corrected ledger
are mathematical review, not a claimed Lean theorem in the present owner.

### Tutorial formula audit

The published text and the versioned arXiv text agree on the inspected issues.
On page 8, Eq. (22) reverses the relative-log order and has an inconsistent
expansion. The correct convention is
`D(σ‖ρ)=tr[σ(log σ−log ρ)]=−S(σ)−tr(σ log ρ)`.
On pages 24–25 the Gibbs entropy calculation omits `log Z`, and intermediate
signs in Eq. (66) need correction. Eq. (91), page 37, prints `O(n²)` where its
intended fixed-entropy lower-bound scaling is `n⁻²`. A decaying quantity also
belongs to the much looser `O(n²)` class, so this is an erroneous intended
scaling annotation rather than a logically false Big-O membership claim.

For the primary Landauer statement and its correlated extension, see Reeb
and Wolf, [arXiv:1306.4352](https://arxiv.org/abs/1306.4352), Theorem 3 and
Section 5.1. Its assumptions must be retained when matching prose to code.

## Concurrent finite-bath source and remaining validation

At the original baseline the missing ingredients included tensor-rank
multiplication and partial-trace support. PR #397 supplies these owners:

| Parent declaration | Exact source statement |
|---|---|
| `MatrixTensorRank.finrank_range_tensorProductMap` and `rank_kronecker` | Actual tensor-map ranges and full square-matrix Kronecker rank multiply over any field. |
| `FiniteBathErasure.projection_mul_eq_zero_of_trace_mul_eq_zero` | PSD input and zero complex trace against a star projection imply ordered annihilation, derived by Gram factorization. |
| `support_of_partialTrace_eq_projection` | A PSD joint matrix whose actual marginal equals a star projection `P` satisfies `(P ⊗ I)σ=σ=σ(P ⊗ I)`. |
| `rank_le_of_partialTrace_eq_projection` | The same hypothesis gives `rank σ ≤ rank P * n`. |
| `no_pure_marginal_of_faithful_bath` | Positive product input, invertible finite positive bath, system rank greater than one, and actual unitary exclude every normalized pure target vector. |
| `normalizedGibbs_isUnit` and `no_pure_marginal_of_normalizedGibbs_bath` | The actual preexisting normalized CFC Gibbs density supplies the faithful bath for every real β. |
| `PureAuxiliarySwap.exists_unitary_erasure_with_pure_auxiliary` | A supplied normalized pure auxiliary gives an actual finite unitary SWAP and exact reduced target state. |

These are inspected source implementations in the parent draft, not a claim
of completed native acceptance. The parent has its own verification record.
Its finite likelihood/work owner also retains explicit likelihood and
pathwise work premises; it does not construct a stopping-time process.

The stronger arbitrary-marginal inequality

\[
\sigma\succeq0\Longrightarrow
\operatorname{rank}\sigma\le r\,\operatorname{rank}(\operatorname{Tr}_B\sigma)
\]

is not supplied by the projection-valued result. It remains a possible
generalization, rather than an assumption needed to state the parent's
already-implemented pure-target obstruction. No additional tensor-rank or
erasure owner is duplicated in this PR.

## Established dependency order and verification plan

The proposed native chain is:

1. Star projection and arbitrary positive matrix → Born probabilities.
2. Nonzero projection ranges and normalized input → positive normalized coarse state.
3. Native two-sheet CFC → its logarithm and exact cross entropy.
4. Preserved probabilities → actual entropy of the coarse state.
5. Existing ordered Umegaki kernel → exact entropy-gap identity.
6. Positive Gram zero criterion → zero-sheet support and kernel inclusion.
7. Parent projective channel plus PSD trace realness → actual binary channel
   equality → transported CFC entropy and support consequences.

No edge from this chain to finite-time work, physical bath realization,
relative-entropy positivity, or the intake's conceptual operator blocks is
asserted. The finite-bath chain belongs to the independent parent owners; its native
acceptance does not follow from this entropy identity.

The focused workflow must build the complete repository import closure with
the exact dependency pins, audit every declaration owned by the target,
require zero target warnings, and run strict placeholder and semantic-vacuity
gates. Local source scans and an installed hook do not substitute for actual
hook execution. A focused success does not certify every tracked repository
file or the root Lake package.


### Source-review snapshot

The CFC owner has SHA-256
`3897c7fb02cbad3be220849fe1e20a9d7c64ca8e0676330d73b771945b2ff2e6`.
The channel adapter has SHA-256
`c1ffa420fdc2996898b480c2f44376fa4b81f2c5ae44c70291f58dd22814ba8b`.
Independent source and pinned-API review of both owners found no structural mathematical
error. The staged gate rejected a scalar `ring` invocation in the probability
normalization proof; the proof now uses additive normalization (`abel`) after
the explicit trace projection, with the statement and hypotheses unchanged. The strict placeholder scan has zero hard findings and one soft
finding on the elementary `trace_pairing_twoSheet` simplification. The
semantic-vacuity error gate passes with three warning-level findings: the
same readout lemma and the two definitional evaluations of the binary
projector family. The adapter has zero placeholder findings. These are
elementary API facts used in the construction, not physical closure claims.
None of these scans is a native compilation or axiom-audit result.

The focused workflow resolves 62 repository modules and 68 native import
roots for the two selected owners, including the parent projective-channel
implementation. It tracks the complete current repository source closure and the
verification helpers, builds the actual PR merge revision, and checks every
owned declaration. Existing dependency warnings are distinguished from the
zero-warning requirement on the new owner. It does not disable or replace the
repository's staged or pre-push gates.

Reproducible native command from the checkout root, using an initialized
Mathlib checkout at the exact pin:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /path/to/pinned/mathlib \
  --lean /path/to/pinned/lean \
  --output /path/to/fresh/evidence \
  --target InfoGeometry.Canonical.TwoSheetObservationalEntropy \
  --target InfoGeometry.Canonical.TwoSheetProjectiveCoarseGraining
```

The PR's validation record states the observed native and integration status;
a workflow definition or queued job is not a successful check.

### Existing workflow syntax repair

The first publication exposed a preexisting failure of
`.github/workflows/post-build-gate.yml`: push run
[44101904999](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44101904999)
failed without creating jobs. The unchanged baseline file ended in a literal
`EOF` line, which reproduced a YAML `ScannerError` at line 82. Removing only
that final line makes the workflow parse. All 13 steps, branch triggers,
timeouts, build commands, and audit commands are retained. This repair does
not constitute a pass of any of those checks.
