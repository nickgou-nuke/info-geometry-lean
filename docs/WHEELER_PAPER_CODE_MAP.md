# Wheeler paper-to-code map

> Status: source-grounded correspondence map with limited native verification
>
> Audited: 2026-11-16
>
> Source baseline: [`08c34e03f610b452e03422037949196dc7d92d6d`](https://github.com/nickgou-nuke/info-geometry-lean/tree/08c34e03f610b452e03422037949196dc7d92d6d)
>
> Related: [formalization discipline](FormalizationDiscipline.md), [deep-search protocol](REPO_DEEP_SEARCH_PROTOCOL.md), [categorical infrastructure](CATEGORICAL_INFRASTRUCTURE_MAP.md)

## 1. Intake, provenance, and reading rule

This document compares John Archibald Wheeler's **Information, Physics, Quantum:
The Search for Links** with the repository's native Lean 4 owners. It records
mathematical correspondences, their hypotheses, and the additional statements
needed to connect them. It does not treat the paper's research program as an
already formalized theory of physics.

The supplied source was `WHEIPQv1.pdf`, identified by SHA-256:

```text
1653d02c4dc309d837dbfa3ecdd7e9ccaadbb40d5fb151c9873217ccc0971af4
```

The PDF and its full extracted text are not included. Short motifs below identify
passages; the surrounding arguments are paraphrased. The scan uses facing pages,
so a printed page number is not a PDF page number:

| PDF page | Printed pages | Principal passages used here |
|---|---|---|
| 1 | 309 | Opening questions and information-oriented program |
| 2 | 310–311 | One world; yes/no registrations; no-cloning; Aharonov–Bohm phase |
| 3 | 312–313 | Black-hole area, hidden configurations, and bit count |
| 4 | 314–315 | Four negative starting points; boundary of a boundary; questions |
| 5 | 316–317 | Complementarity, environmental contribution, Fisher/Wootters amplitudes |
| 6 | 318–319 | Evidence, registered phenomena, and delayed choice |
| 7 | 320–321 | Communication; “More is different”; conclusion and agenda |
| 8 | 322–323 | Algorithmic entropy, Zurek's triangle inequality, and qualifications |

All relative source links refer to the `lean/` owners inspected at the baseline
above. They are convenient checkout links, not a claim that future revisions
have the same text. The separate `src/` tree was searched for alternate
formulations and consumers; duplicated files are not independent evidence.
For example, `CantorProjectiveLimit` uses a structure in `lean/` and a subtype
with explicit accessors in `src/`. Native verification refers only to the
identified `lean/` source bytes.

Two distinctions govern the map:

* **Mathematical scope:** a constructed result, a result conditional on stated
  inputs, or an integration obligation still open in the inspected route.
* **Validation:** fresh native verification is available for three owners in
  section 8: the original two-owner intake audit and the subsequent
  `BoundaryInstrument` audit. Other entries describe source-audited
  declarations and proofs; they are not covered by those compilation results.

## 2. Main correspondences

| Paper motif | Strongest inspected owner or result | Exact mathematical contribution and boundary |
|---|---|---|
| Yes/no questions and registered outcomes, pp. 309, 311 | [BoundaryInstrument](../lean/InfoGeometry/Quantum/BoundaryInstrument.lean#L80), [TwoBoundaryOperatorExamples](../lean/InfoGeometry/Quantum/TwoBoundaryOperatorExamples.lean#L26) | Finite complex Kraus instruments produce nonnegative outcome weights and normalized probabilities under explicit positivity/nonzero-normalizer hypotheses. A concrete two-outcome example is constructed. |
| Complementarity, p. 316 | [Projective/QGT](../lean/InfoGeometry/QuantumGeometry/Projective/QGT.lean#L182), `robertson_schrodinger_qgt_bound`; [TensorBridge](../lean/InfoGeometry/QuantumGeometry/TensorBridge.lean#L131) | Native inner-product inequalities yield noncommutative uncertainty bounds for specified operators and a normalized complex Hilbert state. The complex state space is an input. |
| Fisher/Wootters amplitudes, p. 317 | [FiniteFisherRaoBhattacharyya](../lean/InfoGeometry/Physics/FiniteFisherRaoBhattacharyya.lean#L20), [FisherRaoMadelungIsometry](../lean/InfoGeometry/Probability/FisherRaoMadelungIsometry.lean#L32) | Square-root probabilities give unit vectors, overlap/angle identities, and a genuine derivative identity. Operational distinguishability is a further identification. |
| Boundary of a boundary, pp. 314–315 | [BitWordSimplexCochainModule](../lean/InfoGeometry/Canonical/BitWordSimplexCochainModule.lean#L1394), [DerivationDifferentialForms](../lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean#L253) | Constructed all-degree simplex coboundaries and native Chevalley–Eilenberg differentials square to zero; the latter supports a noncommutative Bianchi identity. |
| Circuit phase and interference, p. 311 | [AharonovBohmGaugeCoboundaryInterferencePoset](../lean/InfoGeometry/Canonical/AharonovBohmGaugeCoboundaryInterferencePoset.lean#L259) | Actual complex differentiation, circle integration, gauge invariance, and two-branch interference. Physical flux/charge units and detector-fringe calibration remain separate. |
| Hidden bits and horizon area, pp. 312–313 | [CliffordColimitVolumeFactor](../lean/InfoGeometry/Epistemology/CliffordColimitVolumeFactor.lean#L257), [BekensteinHawkingDyadicEntropy](../lean/InfoGeometry/Holography/BekensteinHawkingDyadicEntropy.lean#L105) | Uniform finite entropy is computed as `N * log 2`; the gravitational area relation is an explicit calibration hypothesis. |
| Finite information and continuum idealization, pp. 317, 321–322 | [CantorProjectiveLimit](../lean/InfoGeometry/Canonical/CantorProjectiveLimit.lean#L121), [FractalMeasure/Basic](../lean/InfoGeometry/Analysis/FractalMeasure/Basic.lean#L33), [FilteredGNSVacuumState](../lean/InfoGeometry/Canonical/FilteredGNSVacuumState.lean#L54) | Actual inverse limits, infinite product measures, Hilbert completions, represented C-star completions, and positive global states exist. Their identification with Wheeler's particular measurement readouts remains an additional theorem. |
| Shared evidence and irreversible records, pp. 318–320 | [QutritExpectationSeparation](../lean/InfoGeometry/Canonical/QutritExpectationSeparation.lean#L26), [PeirceCoarseGrainedDynamics](../lean/InfoGeometry/OperatorAlgebra/PeirceSpine/PeirceCoarseGrainedDynamics.lean#L67) | Complete finite expectation data reconstruct matrices; a constructed coarse-graining has no universal density decoder. Communication and macroscopic record amplification require additional modeling. |

## 3. Questions, conditioning, and what an observation determines

### Finite instruments preserve the operator content

`BoundaryInstrument.outcomeWeight` uses full finite complex matrices:

\[
w_a=\operatorname{Re}\operatorname{Tr}
\left(\left(\sum_i V_{ai}\rho V_{ai}^{*}\right)E\right).
\]

The owner proves nonnegativity from positive-semidefinite input and effect,
characterizes positive normalization by a surviving branch amplitude, and
proves `sum_probability` and `probability_le_one`. The dimensions and index
types are finite but arbitrary. Normalizing a nonnegative weight family is
different from deriving the quantum measurement rule from elementary questions.

The actual order dependence is visible in
`TwoBoundaryOperatorExamples.normalizers_differ` and `ordered_weights_differ`:
the example gives normalizer `7/18`, bare overlap `4/9`, and ordered weights
`5/72` versus `1/8`. `BoundaryInstrument.krausMap_comp` and
`sum_effect_outcomeWeight` provide composition and removal of a final
conditioning effect by summing a complete family. These support a finite
conditioning interpretation of delayed choice, not influence on the past.
Wheeler explicitly rejects that latter interpretation on printed p. 323.

The literally named
[WheelerDelayedChoiceModularLaw](../lean/InfoGeometry/Epistemology/WheelerDelayedChoiceModularLaw.lean#L155)
instead proves a bilinear polarization identity from an involutive
anti-isometry. Its statement contains no detector choice or outcome
distribution; its naming cannot supply the missing operational bridge.

### Readout equality is model-dependent

[QutritExpectationSeparation.expectationReadout_reconstruction](../lean/InfoGeometry/Canonical/QutritExpectationSeparation.lean#L35)
reconstructs every full complex 3-by-3 matrix from nine explicitly specified
identity/Gell–Mann trace channels. The basis and its Gram orthogonality are
proved in [QutritGellMannOperatorBasis](../lean/InfoGeometry/Canonical/QutritGellMannOperatorBasis.lean).
More generally,
[PolarFrameTraceDensity.traceDensityLinear_injective](../lean/InfoGeometry/Canonical/PolarFrameTraceDensity.lean#L43)
shows that equality of trace functionals on **all** test matrices determines
the finite density matrix.

The limitation is also formalized:
[PeirceEvenObservables.even_expectations_iff_equal_blocks](../lean/InfoGeometry/OperatorAlgebra/PeirceSpine/PeirceEvenObservables.lean#L52)
identifies the visible blocks under a restricted observable family; hidden
coherences can remain different. Complete specified data can identify a state
in a specified model. This is not a theorem that independently communicating
observers necessarily establish a unique physical world.

[PeirceCoarseGrainedDynamics.no_density_recovery_after_evolution](../lean/InfoGeometry/OperatorAlgebra/PeirceSpine/PeirceCoarseGrainedDynamics.lean#L67)
proves a genuine no-decoder result using distinct densities with the same
coarse-grained output. `exists_cptp_coarse_grained_no_recovery` additionally
constructs complete positivity at all finite matrix amplifications and trace
preservation, given a nontrivial Hermitian idempotent and the stated positive
residual bound. This is an information-loss theorem on noncommuting matrices.
It does not yet identify a macroscopic amplified, persistent, communicated
detector record.

### Wheeler-named algebra is a separate carrier

[Canonical/WheelerItFromBit](../lean/InfoGeometry/Canonical/WheelerItFromBit.lean)
uses an idempotent real 32-by-32 matrix and a Krein trace readout. Its zero-state
vanishing result is algebraic; covariance symmetry requires commuting
observables. [PeirceWheelerBitwordReadout](../lean/InfoGeometry/OperatorAlgebra/PeirceSpine/PeirceWheelerBitwordReadout.lean#L32)
proves additive/refinement identities and finite dyadic coverage. Its conserved
total is the readout of `1`; positivity and unit normalization are not thereby
proved. These readouts must not be silently substituted for the normalized
instrument probabilities or the positive global states in section 6.

## 4. Boundary, gauge, and field-theory identities

### Constructed differentials are stronger than a stored square-zero law

[DiscreteStokesFinite](../lean/InfoGeometry/Canonical/DiscreteStokesFinite.lean#L71)
constructs one oriented triangle's incidence maps and proves double-boundary
cancellation. The stronger all-degree owner is
`BitWordGraphDifferential.simplexCoboundary_squared` in
[BitWordSimplexCochainModule](../lean/InfoGeometry/Canonical/BitWordSimplexCochainModule.lean#L1451).
It constructs a native cosimplicial object with full matrix-valued cochains on
binary-word vertices, identifies the alternating coface map with its explicit
coboundary, and applies Mathlib's `AlternatingCofaceMapComplex.d_squared`.

[DerivationDifferentialForms](../lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean#L253)
constructs low-degree Chevalley–Eilenberg differentials over a faithful Lie
action by bundled derivations. Its `connectionCurvature_bianchi` at line 423
defines curvature from a one-form and proves the covariant Bianchi identity.
The noncommuting-direction term is retained; no commuting-operator reduction
or supplied Bianchi equation replaces it. The native audit in section 8 covers
this owner.

By contrast,
[WheelerBoundaryHomologyBridge.ChainThreeStage](../lean/InfoGeometry/Canonical/WheelerBoundaryHomologyBridge.lean#L36)
stores double-boundary vanishing as a field. Its later theorem projects that
field. This is a useful conditional interface, but is weaker evidence for the
paper's first clue than the constructed owners above.

### Physical field equations need their own hypotheses

[ZornMaxwellSourceDifferentialBridge.externalSource_conservation](../lean/InfoGeometry/Canonical/ZornMaxwellSourceDifferentialBridge.lean#L50)
derives the continuity equation from commuting differential operators and
**assumed external Gauss/Ampère equations**. In the induced-source variant,
charge and current are defined by the field divergences/curls, making the
inhomogeneous equations definitional.
[EinsteinCartanBianchiBridge](../lean/InfoGeometry/Canonical/EinsteinCartanBianchiBridge.lean#L79)
derives Cartan Bianchi identities from a supplied graded square-zero exterior
differential and degree-one connection. Neither theorem selects Einstein field
equations, physical sources, couplings, or a spacetime metric from the boundary
principle alone.

### Aharonov–Bohm: an actual analytic normalized model

[AharonovBohmGaugeCoboundaryInterferencePoset](../lean/InfoGeometry/Canonical/AharonovBohmGaugeCoboundaryInterferencePoset.lean#L259)
defines the coefficient `-φ*i/(2*π*z)`, differentiates a slit-plane logarithmic
primitive, and proves its circle integral equals the real phase circulation
`φ` for positive radius. Exponentiation gives `exp(iφ)`. The same owner proves
finite gauge-coboundary cancellation and two-branch constructive/destructive
interference.

`abCircleConnection_no_global_primitive` requires `φ ≠ 0`. This is nonzero
**circulation**, not necessarily nontrivial U(1) holonomy: `φ = 2π` has trivial
exponential phase. The physical calibration involving charge, electromagnetic
flux, and the quantum of action, together with a detector fringe-displacement
model, is a separate integration obligation.

## 5. Statistical geometry and entropy: conventions matter

For `PositiveDist D`, the probabilities are strictly positive and sum to one.
[FiniteFisherRaoBhattacharyya](../lean/InfoGeometry/Physics/FiniteFisherRaoBhattacharyya.lean)
proves that `sqrt p` lies on the unit sphere and that

\[
B(p,q)=\sum_i\sqrt{p_iq_i}=\langle\sqrt p,\sqrt q\rangle.
\]

Its `fisherRaoDistance` is `2 * arccos B`, so it uses twice the unscaled
Wootters angle. Symmetry, nonnegativity, self-zero, and separation-related
identities are proved. The finite pairing theorem in
[FiniteFisherRaoSquareRoot](../lean/InfoGeometry/Canonical/FiniteFisherRaoSquareRoot.lean#L93)
realizes `Σ h_i*k_i/p_i` through the explicit map `h_i/√p_i`.
[Probability/FisherRaoMadelungIsometry](../lean/InfoGeometry/Probability/FisherRaoMadelungIsometry.lean#L99)
also proves the actual derivative identity, assuming positive density and
`HasDerivAt`. Operational discrimination optimality is not established by
merely defining this angular distance.

There are genuine constructions involving complex structure:
[DoubledSpace.complex_i_sq](../lean/InfoGeometry/Krein/DoubledSpace.lean#L331)
constructs a norm-preserving quarter-turn on a doubled real Hilbert carrier,
and [EmergentComplexStructure](../lean/InfoGeometry/OperatorAlgebra/EmergentComplexStructure.lean#L16)
constructs a complex algebra from a **supplied central** square root of `-1`.
The [complexAmplitude](../lean/InfoGeometry/Physics/AmariSurprisalIwasawaSynthesis.lean#L208)
definition instead chooses complex scalars and phases explicitly. None proves
that operational complementarity uniquely forces complex quantum theory.

For a uniform distribution on `2^N` states,
[CliffordColimitVolumeFactor.holographic_area_law_nats](../lean/InfoGeometry/Epistemology/CliffordColimitVolumeFactor.lean#L257)
proves

\[
S_{\mathrm{nats}}=N\log 2,\qquad S_{\mathrm{bits}}=S_{\mathrm{nats}}/\log 2=N.
\]

This is a finite Shannon-entropy calculation, despite its gravitational name.
There is no geometric area in its theorem type. Wheeler's area quantum is
`4 ℏ log 2` in the paper's geometric-unit presentation, equivalently
`4 ℓ_P² log 2` using the Planck area. The dyadic owner
[BekensteinHawkingDyadicEntropy](../lean/InfoGeometry/Holography/BekensteinHawkingDyadicEntropy.lean#L105)
defines `S = area/(4G)` and proves `S = N log 2` under the explicit hypothesis
`area = 4*G*(N*log 2)` and `G ≠ 0`.

The older
[BekensteinHawkingThermodynamics](../lean/InfoGeometry/Holography/BekensteinHawkingThermodynamics.lean#L34)
stores `N_qubits : ℝ` and `Area = N_qubits*(4*G_Newton)`, then divides its
one-bit Shannon entropy by `log 2`. With the same area convention, that
`N_qubits` cannot also mean Wheeler's binary bit count. Neither owner derives
physical horizon area from microstates.

## 6. Infinite objects and a constructed global positive state

The repository goes substantially beyond finite matrices and assumed limits.
Two distinct routes must be kept visible.

### Binary inverse limits and measures

[CantorProjectiveLimit.cantorHomeomorphPrefixProjectiveLimit](../lean/InfoGeometry/Canonical/CantorProjectiveLimit.lean#L121)
constructs a homeomorphism between binary streams and coherent finite-prefix
families, with explicit inverse maps. Its
[UHFInductiveColimitBoundary](../lean/InfoGeometry/Canonical/UHFInductiveColimitBoundary.lean#L87)
dependency proves injective diagonal-stage embeddings and compatible cylinder
evaluations. That dependency alone does not construct the full UHF completion.

[FractalMeasure/Basic.fractalMeasure](../lean/InfoGeometry/Analysis/FractalMeasure/Basic.lean#L33)
uses Mathlib `Measure.infinitePi` of uniform Boolean measures.
[CantorProjectiveBernoulliMeasure](../lean/InfoGeometry/Canonical/CantorProjectiveBernoulliMeasure.lean#L42)
transports this probability measure to the projective limit and proves exact
prefix masses `2^(-N)`, successor additivity, union, and disjointness.

### Full matrix stages, GNS completion, and state extension

The stronger operator route starts with
[CantorBernoulliCStarMatrixTraceState](../lean/InfoGeometry/Canonical/CantorBernoulliCStarMatrixTraceState.lean#L38):
the stages are full `CStarMatrix (Fin (2^n)) (Fin (2^n)) ℂ`, with the transported
operator norm and explicit reindexed embeddings `A ↦ A ⊗ I₂`.
`cstarMatrixTraceStateFamily` at line 287 **constructs** the compatible family
of normalized positive trace states `2^(-n) Tr A`; positivity, normalization,
continuity, finite faithfulness, and compatibility are proved.

Its immediate `TopCat` colimit map is a continuous readout. That map's type
alone is not a completed C-star state. The downstream owners provide the
stronger construction:

| Step | Owner and declaration | Actual construction |
|---|---|---|
| Hilbert colimit | [CantorBernoulliGaugeFilteredGNSColimitBridge](../lean/InfoGeometry/Canonical/CantorBernoulliGaugeFilteredGNSColimitBridge.lean#L57), `gaugeStage`, `gaugeSystem`, `gaugeStateFamily` | Specializes the trace family to the filtered GNS system, with stage isometries, dense union, and complete Hilbert colimit. |
| Represented closure | [FilteredGNSRepresentedCStarClosure](../lean/InfoGeometry/Canonical/FilteredGNSRepresentedCStarClosure.lean#L46), `representedCStarClosure` | Takes the operator-norm closure of the algebraic-colimit representation range in bounded operators on the GNS Hilbert colimit; constructs its C-star algebra and dense algebraic map. |
| Completion equivalence | [FilteredGNSRepresentedCStarCompletion](../lean/InfoGeometry/Canonical/FilteredGNSRepresentedCStarCompletion.lean#L212), `representedRangeCompletionStarAlgEquiv` | Equips the uniform completion of the represented algebraic range with its C-star structure and identifies it with the represented closure. |
| Vacuum functional | [FilteredGNSVacuumReadback](../lean/InfoGeometry/Canonical/FilteredGNSVacuumReadback.lean#L61), `representedVacuumFunctional` | Constructs `a ↦ ⟪Ω, a Ω⟫`, proves the unit vacuum norm, normalization, positivity from the Hilbert adjoint, and stage recovery. |
| Global state | [FilteredGNSVacuumState](../lean/InfoGeometry/Canonical/FilteredGNSVacuumState.lean#L54), `representedVacuumState`, `representedVacuumState_stage` | Constructs the native normalized positive state, including spectral-order instances, and proves exact recovery of the input stage states and independence of the chosen vacuum stage. |

The generic completion/state owners take a nonempty directed preorder, ordered
C-star stages, a coherent unital star-inductive system, and compatible states.
The concrete matrix-trace route supplies these inputs. The global
specialization described here follows the inspected constructors; it was not
separately compiled as one composite theorem in this audit.

The completed carrier is the **represented range**, which has already removed
the representation kernel. This is not an unconditional injective completion
of every raw algebraic colimit, nor identification with the entire infinite
Cuntz algebra. The constructed state extends the selected trace family;
arbitrary measurement-dependent distributions are not automatically that
state.

The remaining connection is specific: construct compatible normalized positive
stage states from the actual `BoundaryInstrument` or Peirce Wheeler data and
prove the extended state's stage evaluations equal those readouts. Exact-symbol
and consumer searches along the inspected route did not locate that theorem.
It would be incorrect to replace this obligation with a claim that no infinite
state, GNS construction, or C-star completion exists.

## 7. Limits of the current correspondence

Wheeler's closing agenda asks for more than the identities above. The following
are bounded search findings, not global nonexistence claims.

* **No-cloning, p. 311:** no matching universal quantum no-cloning theorem was
  identified after searches for cloning, broadcasting, copying, and tensor
  alternatives. The classical copied-register theorem in
  [FiniteEntanglementComplexityCore](../lean/InfoGeometry/Quantum/FiniteEntanglementComplexityCore.lean#L137)
  is a different claim.
* **“More is different,” p. 321:** the inspected phase-transition capstone proves
  [finite Euler-product positivity](../lean/InfoGeometry/Quantum/SouriauBostConnesPhaseTransitionCapstone.lean#L60),
  not cooling-induced symmetry breaking. The
  [Hurwitz-named limit theorem](../lean/InfoGeometry/Canonical/TheoremHonestHurwitzConvergenceBridge.lean#L57)
  states that a supplied convergent sequence on the unit circle has its limit
  there; no partition function or singular free energy occurs in its type.
  [ThermodynamicLimitColimit](../lean/InfoGeometry/Categorical/ThermodynamicLimitColimit.lean#L25)
  assumes `[HasColimit F]` and exposes its universal property. These routes do
  not complete the paper's physical emergence proposal.
* **Algorithmic entropy, p. 322:**
  [AlgorithmicBoltzmannKolmogorovBridge](../lean/InfoGeometry/Canonical/AlgorithmicBoltzmannKolmogorovBridge.lean#L34)
  stores the Kraft inequality. Its theorem named
  `kolmogorov_microcanonical_cardinality_bound` proves positivity of a finite
  sum, not a cardinality bound.
* **Zurek's information triangle, p. 322:** searches found no matching
  information-distance theorem. The native
  [unit-sphere angle triangle inequality](../lean/InfoGeometry/Physics/UnitSphereDistanceTriangle.lean#L51)
  is a different result. Textual Zurek matches concerned unrelated
  Kibble–Zurek disclaimers.
* **Spacetime and dynamics:**
  [ContinuumPropagatorLimitBridge](../lean/InfoGeometry/Canonical/ContinuumPropagatorLimitBridge.lean)
  supplies generator and flow convergence in structure fields, then
  transports convergence through `exp`. The actual infinite constructions in
  section 6 do not by themselves prove those dynamical limits or derive a
  Lorentzian spacetime.

## 8. Native verification and its exact scope

### 8.1 Original intake audit: 131 declarations

The successful intake audit checked the exact source closure of two targets
using Lean `v4.34.1` and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`:

| Native target | Owned declarations audited | Source SHA-256 | Result |
|---|---:|---|---|
| `InfoGeometry.OperatorAlgebra.DerivationDifferentialForms` | 84 | `064f933a187f6ab522fdd054d6e0efc0dced1839423c61c6ef173d47a172fd7f` | `[kernel_verified]` at the stated types |
| `InfoGeometry.Epistemology.CliffordColimitVolumeFactor` | 47 | `aaba8d1d8f386fb12299445c7e20af14c2b22ebd1766c6c116e243219b2aba5e` | `[kernel_verified]` at the stated types |

The total is **131 declarations**, not 131 separate physical theorems. The
reported axiom dependencies were only `propext`, `Classical.choice`, and
`Quot.sound`. Linter warnings were recorded; they were not proof failures.
The unchanged [native audit report](WHEELER_SOURCE_AUDIT_20261116.json)
records the five-module source closure, source and verifier hashes, artifact
fingerprints, and declaration counts. The [native declaration inventory](WHEELER_NATIVE_AXIOMS_20261116.txt)
lists every audited declaration, including generated declarations. All five
owner-source hashes and all four verifier-source hashes were checked again
against the publication baseline and match.

The successful invocation of the maintained audit tool had the following
shape, with task-local paths replaced here by explicit environment variables:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root "$WHEELER_MATHLIB_ROOT" \
  --lean "$WHEELER_LEAN_EXECUTABLE" \
  --output "$WHEELER_AUDIT_OUTPUT" \
  --incremental \
  --target InfoGeometry.OperatorAlgebra.DerivationDifferentialForms \
  --target InfoGeometry.Epistemology.CliffordColimitVolumeFactor
```

The preceding broader run had freshly compiled the five repository objects in
these targets' source closure. The successful incremental invocation checked
their source fingerprints, reused those objects, and ran the fresh complete
axiom audit. This command is not a claim that an arbitrary cache or a later
checkout has the same verification status.

The audit ran from local revision
`16f13675b9fecccc9db0bf88aa49ca7587a4efbc`; the relevant source bytes were checked
against the main baseline and were unchanged. Unrelated draft changes in that
local revision are not evidence for this map.

An earlier broader attempt did not verify the measurement and Fisher routes:
the available pinned Mathlib installation lacked required artifacts, including
`Mathlib.olean` and `Mathlib/LinearAlgebra/Matrix/Permutation.olean`. At that
checkpoint those routes were **source-audited**. The follow-up below changes
that status specifically for `BoundaryInstrument` and its compiled source
closure; it does not change the original report or its historical command.
An artifact-availability failure is not a mathematical refutation, and a
source proof inspection is not a successful compilation.

### 8.2 Follow-up instrument audit: 42 declarations

A fresh baseline run subsequently compiled
`InfoGeometry.Quantum.BoundaryInstrument` and its complete five-module
repository-source closure against the same Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` pins. The new
[instrument audit report](WHEELER_INSTRUMENT_AUDIT_20261116.json) records
successful compilation of `FiniteSpinAlgebra`, `ChoiCompletePositivity`,
`KrausBoundaryDuality`, `PositiveBoundaryConditioning`, and `BoundaryInstrument`.
All five objects were freshly built; the report marks none as reused.
All five owner-source hashes and all four verifier-source hashes also match
the publication baseline.

| Native target | Owned declarations audited | Source SHA-256 | Result |
|---|---:|---|---|
| `InfoGeometry.Quantum.BoundaryInstrument` | 42 | `33a1f8604ef1755adab2cee9a16321296c1a8fcb6673e5b40b5b95df5aa5db15` | `[kernel_verified]` at the stated types |

The [instrument declaration inventory](WHEELER_INSTRUMENT_AXIOMS_20261116.txt)
lists all 42 owned declarations, including generated declarations. Their
reported axiom dependencies are only `propext`, `Classical.choice`, and
`Quot.sound`. The target produced no warnings; dependency linter warnings are
recorded in the report. Its `local_revision` is
`16f13675b9fecccc9db0bf88aa49ca7587a4efbc`; the audited baseline source hash is
listed above. This follow-up does not modify the original 131-declaration
report or inventory.

The successful follow-up invocation used no `--incremental` option. With
task-local paths replaced by explicit environment variables, its exact
argument structure was:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root "$WHEELER_MATHLIB_ROOT" \
  --lean "$WHEELER_LEAN_EXECUTABLE" \
  --output "$WHEELER_INSTRUMENT_AUDIT_OUTPUT" \
  --target InfoGeometry.Quantum.BoundaryInstrument
```

The two successful reports now cover **173 owned declarations across three
owners**: 84 in `DerivationDifferentialForms`, 47 in
`CliffordColimitVolumeFactor`, and 42 in `BoundaryInstrument`. This is not a
declaration count for all compiled dependencies or all mathematical results
discussed here. In particular, the concrete `TwoBoundaryOperatorExamples`
module, the Fisher route, and the other uncompiled owners remain
**source-audited**. The generic instrument audit does not certify those
examples, the full measurement route, an umbrella build, or the whole
repository.

### 8.3 Reproduction and publication boundary

Future native checks should use the maintained locked wrappers described in
[AGENTS.md](../AGENTS.md) and [RUNBOOK.md](../RUNBOOK.md), preserve the pinned
dependencies, and audit exact declaration assumptions. This document records
the intake and follow-up results; any new owner or newly assembled composite
theorem needs its own current verification.

This publication changes documentation and its verification evidence only.
The inspected root package also requires `Atlas` and `HomotopyHypothesis`
path dependencies whose source is absent from the checkout and is not recorded
by a tracked package configuration or gitlink. The maintained path-dependency
preflight rejects an untracked replacement. Adding a new Lean owner therefore
requires a separately reviewed dependency repair and the applicable unchanged
publication gates; the scoped audits above do not satisfy that root-package
requirement. No dependency specification is changed here.

## 9. Prospective integration obligations

The useful dependency order begins with explicit carriers and maps. The
measurement route starts from a state, instrument, and effects; constructs
ordered weights; proves positivity and nonzero normalization; and obtains
probabilities. The geometric route constructs cochains or derivations before
proving differential and curvature identities. The infinite state route starts
from explicit coherent stages and compatible states before constructing GNS
and completion. Similar physical vocabulary creates no additional edge between
these routes.

The following are proposed obligations, not declarations claimed to exist:

1. **Measurement-to-global-state compatibility:** construct a positive,
   normalized, transition-compatible family from the actual instrument or
   Peirce data and prove recovery by the existing global state construction.
2. **Operational statistical distance:** state a concrete discrimination
   experiment and prove its relation to the implemented square-root angle,
   with the factor-of-two convention fixed.
3. **Physical calibration:** connect normalized AB circulation to a specified
   electromagnetic model and derive, rather than supply, any proposed
   microstate-to-horizon area law.
4. **Recorded histories:** specify which ordered measurement results become
   stable records, what transitions preserve them, and how communication or
   coarse-graining affects their equality. Existing matrix identities alone
   do not construct such a history model.
5. **Named missing agenda items:** formalize a precise no-cloning statement,
   the intended Zurek information inequality, or an actual thermodynamic
   transition only after selecting the relevant native carrier and exact
   theorem contract.

This map provides owner reuse and proof boundaries for those tasks. It does not
introduce a new history module or certify any proposed integration as complete.
