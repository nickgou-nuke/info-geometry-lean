# Information Carnot, Gibbs scale, and unitary tangent contract

## Intake and provenance

User intake, 2026-11-18, preserved verbatim below. The GitHub connector selection
names the source service and is not mathematical content.

> carnot cycle of information the expansion and contraction the weyl gauge scale (the gromov witten theory and volume) thermodynamic partition function renormalization to the unitary equilibrium soureau leflet of constant entrpy for the metriplectiv system    renormalization of the bloch ball of the spacetime fromt of sorts radial breatehr carnot cycke changing entropy around the equilibrium leaf the piston is in the radial direction tie lg time weyl gauge orthogonal to unitary evolution of sorts information thermodynakic canrnot cycle entropy and surface orbits time psiton goldstone bosons the codebase has some of these ideas partially interconnected however strange they may seem wilson loops ness ireversible and reversible oscvillations around the equilibrium forward and backward waves with reflection causal wave front waves

Source base: main `08c34e03f610b452e03422037949196dc7d92d6d`.
Gibbs dependency: draft PR #399, commit
`0680d42417725b49eacfe9cf5743522785149239`. The dependency's source is inspected;
its existence is not a compilation certificate. This contribution is stacked
on that exact revision. Lean and Mathlib pins remain unchanged.

## Formal intent

The new target is finite-dimensional operator algebra on `Matrix n n ℂ`, for
an arbitrary finite index type, with the native matrix product, adjoint,
Hermitian functional calculus, matrix exponential, trace, and unitary group.
No diagonal or commuting replacement of the Hamiltonian carrier is introduced.

The primary owner is affine scale and unitary transport of the actual Gibbs
weight and normalized Gibbs density. For Hermitian `H`, unitary `U`, real
`a ≠ 0`, and real `b`, set `H' = a • (U * H * star U) + b • 1` and
`β' = β / a`. Its theorem statements are

```text
exp(-β' H') = exp(-β' b) • (U * exp(-β H) * star U)
Z(β', H') = exp(-β' b) * Z(β, H)
Γ(β', H') = U * Γ(β, H) * star U
S(Γ(β', H')) = S(Γ(β, H))
E(Γ(β', H'), H') = a * E(Γ(β, H), H) + b.
```

Nonempty dimension is required for a strictly positive partition function,
the trace-one physical-state interpretation, and the indicated cancellation
and entropy lemmas. Totalized algebraic normalization identities can hold
with weaker hypotheses. Positive `a` is the usual thermodynamic scale convention; the algebraic
transport identity only needs nonzero `a`. Positive-temperature interpretation
additionally requires positive inverse temperature. No finite-time adiabatic
theorem or reversible bath protocol is asserted by an endpoint identity.

A second owner uses the existing cyclic matrix trace and functional
calculus owners to connect the tangent `-I • (H * ρ - ρ * H)` to spectral
directions. If `A` commutes with `ρ`, then `trace (A * (-I • [H, ρ])) = 0`.
For Hermitian `A`, this is the complex Hilbert–Schmidt orthogonality identity.
The radial direction `ρ - (card n)⁻¹ • 1` and `CFC.log ρ` are concrete
specializations. A pairing identity is not by itself a theorem differentiating
the matrix entropy along an arbitrary path.

For Hermitian `H` and `ρ`, the concrete score `G = H + T • (CFC.log ρ + 1)` satisfies
`trace (star G * unitaryFlow H ρ) = 0`. This supplies an actual missing premise
of `MetriplecticDissipation.freeEnergy_rate_nonpos`. Its resulting contraction
is exactly `-Re (trace (star G * M G))`, and is nonpositive when the complex
linear mobility `M` has nonnegative real quadratic readout on every matrix.
Symmetry, trace preservation, positivity preservation, and GENERIC degeneracy
conditions are not derived from that one assumption.

A third owner computes the existing full evolution expression at the actual
Gibbs state. For nonempty dimension and `β ≠ 0`, with `T = β⁻¹`,

```text
[H, Γ(H, β)] = 0
G(H, Γ(H, β), β⁻¹) = β⁻¹ * (1 - log Z(H, β)) • 1
stateEvolution(Γ, H, G, M) = -β⁻¹ * (1 - log Z(H, β)) • M(1).
```

Consequently `M(1) = 0` gives algebraic stationarity. The trace-constrained
Gibbs score is central and need not be zero. The identity-annihilating mobility
condition is explicit; positivity of its quadratic form alone does not imply
it. Neither this calculation nor the rate contraction constructs a global
positive trace-preserving flow, a convergence result, or the Fréchet derivative
of matrix entropy.

The three new files contain 37 theorem declarations and two definitions:
18 transport theorems, 12 tangent/rate theorems, and seven equilibrium theorems.
Their carriers, Gibbs density, CFC logarithm, entropy, unitary flow, and full
evolution expression come from the existing owners.

## Existing owner anchors and smallest missing implications

| Mathematical object | Existing owner | Scope used here |
|---|---|---|
| CFC Gibbs weight and faithful functional | `Canonical.FiniteMatrixGibbsFunctional` | Native full complex matrices; positivity and finite algebraic KMS identity |
| Trace normalization and cancellation of positive scale | `Canonical.PolarFrameTraceDensity` | `normalizedDensity_scale` already cancels the cone's positive scalar ray |
| Actual matrix entropy on a unitary orbit | `Canonical.MatrixEntropyUnitaryOrbit` | CFC logarithm and strictly positive matrices |
| Actual Gibbs log, entropy, and energy | `Canonical.MatrixGibbsEntropy`, PR #399 | Gibbs weight is the matrix exponential; actual log has the central `log Z` correction |
| Trace cyclicity for inner derivations | `Core.JordanMultiplicationClosure.trace_adjoint_identity` | Reuses the lower cyclic additive-trace owner without importing broad `Mathlib`; the equivalent matrix owner is `Physics.MatrixTraceBimodulePairingNative` |
| Commuting state and functional calculus | Native `cfc_commute_cfc`, `cfc_id`, and `IsSelfAdjoint.commute_cfc` | A real CFC direction commutes with its Hermitian carrier; the broader repository lane is `Canonical.OperatorSurprisalCFCCommute` |
| Existing Gibbs centralizer facts | `Canonical.FiniteMatrixGibbsParity` contains `FiniteMatrixGibbsFunctional.gibbsDensity_commutes_of_commute`; the other owner is `Quantum.MatrixBoundaryPurification.normalizedGibbs_commute` | Prior Gibbs-commutation mathematics; the new short adapter applies native CFC to the parent's real-trace normalization without importing the parity/sewing or boundary-purification lanes |
| Native reversible flow and energy trace | `Canonical.FreeEnergyEquilibriumUnitaryBridge` | Its energy-conservation theorem uses the same `-i[H,ρ]` expression as the dissipation owner |
| Existing nonpositive rate consumer | `Canonical.FreeEnergyDissipationRate` | The score's unitary pairing is now derived; the mobility's nonnegative real quadratic form remains an explicit hypothesis |
| Equilibrium of the existing evolution expression | `Canonical.FreeEnergyEquilibriumUnitaryBridge` and `Canonical.FreeEnergyDissipationRate` | The previous zero-stored-gradient premise is supplemented by an actual Gibbs-score calculation and the explicit condition `M(1) = 0` |
| Existing information Carnot algebra | `Detector.InformationCarnotCycle` | Efficiency expression and Peirce operator identities; not a four-stroke thermal evolution |

The new Gibbs transport extends the existing density and logarithm owners.
The tangent pairing consumes the existing cyclic trace identity, and the
equilibrium calculation evaluates the existing evolution expression.

## Source-grounded interpretation map

These are bounded source-inspection findings, not a fresh compilation
certificate for the unrelated owners in this table.

| Intake motif | Inspected source | What its declarations establish, and the boundary |
|---|---|---|
| Information Carnot cycle | [`Detector/InformationCarnotCycle`](../lean/InfoGeometry/Detector/InformationCarnotCycle.lean) | Polynomial efficiency and Peirce operator identities; no four-stroke thermal state evolution |
| Carnot and cohomology | [`Integration/CarnotDeRhamCohomologyBridge`](../lean/InfoGeometry/Integration/CarnotDeRhamCohomologyBridge.lean) | Logarithmic differential/cohomology readouts; an explicit map to a thermal cycle is still needed |
| Entropy on unitary orbits | [`Canonical/MatrixEntropyUnitaryOrbit`](../lean/InfoGeometry/Canonical/MatrixEntropyUnitaryOrbit.lean) | Actual CFC entropy is invariant under full unitary conjugation for strictly positive matrices |
| Positive scale and normalization | [`Canonical/PolarFrameTraceDensity`](../lean/InfoGeometry/Canonical/PolarFrameTraceDensity.lean) | Positive scaling of an unnormalized weight cancels after trace normalization |
| Bloch radial coordinate | [`Quantum/DensityMatrixPurity`](../lean/InfoGeometry/Quantum/DensityMatrixPurity.lean) | Actual two-by-two Pauli density expression and `Re Tr(ρ²) = (1 + r²) / 2`; the inspected file does not prove an entropy-radius classification |
| Gradient normal to an entropy level | [`Geometry/EntropyLevelGradientOrthogonality`](../lean/InfoGeometry/Geometry/EntropyLevelGradientOrthogonality.lean) | Riesz duality for a supplied continuous differential; no identification with the derivative of the actual matrix entropy |
| Souriau entropy foliation | [`Physics/SouriauEntropyFoliation`](../lean/InfoGeometry/Physics/SouriauEntropyFoliation.lean) | Finite weight permutations preserve the scalar entropy; matrix unitary transport is owned elsewhere |
| Infinite coadjoint metriplectic context | [`Canonical/SouriauCoadjointOrbitMetriplecticTheorem`](../lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean) | The context supplies rate, positivity, and split assumptions; its square-amplitude construction does not differentiate its stored entropy |
| Constructed operator Onsager forms | [`Canonical/CEBKMOnsagerSystem`](../lean/InfoGeometry/Canonical/CEBKMOnsagerSystem.lean) | Centered BKM response pulled back to CE operator derivations, with a skew curvature form |
| Reversible and dissipative components | [`QuantumContext/MarkovMetriplecticReversibleRotation`](../lean/InfoGeometry/QuantumContext/MarkovMetriplecticReversibleRotation.lean) and [`MarkovMetriplecticQuadraticDecay`](../lean/InfoGeometry/QuantumContext/MarkovMetriplecticQuadraticDecay.lean) | Full real-matrix skew action and quadratic decay, not a heat-engine protocol |
| Log radius, time, and reflection | [`Canonical/NativeSouriauHestenesRadialBridge`](../lean/InfoGeometry/Canonical/NativeSouriauHestenesRadialBridge.lean) | Log-cylinder translation `rho ↦ rho + 2t`, with reflection conjugating it to the inverse flow; the source explicitly does not identify this coordinate with inverse temperature |
| Cone and cylinder normalization | [`Canonical/RadialQuantizationFiveGradedCylinder`](../lean/InfoGeometry/Canonical/RadialQuantizationFiveGradedCylinder.lean) | Log-radius scaling, cone/cylinder readouts, finite-weight normalization, and a five-grade action on their specified carriers |
| Weighted Weyl evolution | [`Canonical/WeightedWeylNormalizationBridge`](../lean/InfoGeometry/Canonical/WeightedWeylNormalizationBridge.lean) | A density-weight correction on a doubled real Hilbert carrier; no normalized Bloch-ball contraction follows automatically |
| Goldstone language | [`Canonical/SouriauKreinMetriplecticContext`](../lean/InfoGeometry/Canonical/SouriauKreinMetriplecticContext.lean) | Dilation-operator and CAR/CCR identities; no physical Goldstone theorem is derived |
| Gromov–Witten and partition counts | [`Canonical/WeylKMSGromovWittenCounts`](../lean/InfoGeometry/Canonical/WeylKMSGromovWittenCounts.lean) | Weighted finite orbit counts; `GromovWittenCalibration` supplies the identification with GW weights and `WeylKMSVolumeCalibration` supplies the volume equality |
| Weyl-invariant volume | [`Canonical/WeylGWVolumeBridge`](../lean/InfoGeometry/Canonical/WeylGWVolumeBridge.lean) | Scale cancellation under explicit factorization and opposite weight laws |
| Quantum-cohomology algebra | [`QuantumGeometry/GromovWittenGrothendieck`](../lean/InfoGeometry/QuantumGeometry/GromovWittenGrothendieck.lean) | Concrete rank-two quantum-cohomology multiplication; no constructed moduli-space-to-thermal-trace map |
| Wilson loops and forward/backward transport | [`Topology/ThermodynamicGauge`](../lean/InfoGeometry/Topology/ThermodynamicGauge.lean) and [`WilsonLoopThermodynamics`](../lean/InfoGeometry/Topology/WilsonLoopThermodynamics.lean) | Ordered finite ring products. The named `entropy_production` is a transition commutator; its name does not establish physical entropy production |
| NESS | [`Capstone/GrandModularSpectralRHCapstoneBridge`](../lean/InfoGeometry/Capstone/GrandModularSpectralRHCapstoneBridge.lean) | A particular scalar phase-state condition and quadratic production expression; not a general open quantum steady-state construction |
| Causal wavefronts | [`Synthesis/WavefrontKMSKleinDualityBridge`](../lean/InfoGeometry/Synthesis/WavefrontKMSKleinDualityBridge.lean) | Finite Zorn, monodromy, cyclotomic, and Gibbs ingredients; no hyperbolic PDE propagation theorem |
| Optical reflection | [`OperatorAlgebra/FiniteJonesOptics`](../lean/InfoGeometry/OperatorAlgebra/FiniteJonesOptics.lean) | Concrete finite Jones events and loss/diattenuation criteria; distinct from abstract Weyl reflection |

## Related concurrent upstream work

Draft [PR #406](https://github.com/nickgou-nuke/info-geometry-lean/pull/406),
inspected at `b22b88bc70730f2ad213baede7d91e14a1223c43`, adds
[`ReplacementRelaxation`](https://github.com/nickgou-nuke/info-geometry-lean/blob/b22b88bc70730f2ad213baede7d91e14a1223c43/lean/InfoGeometry/Quantum/ReplacementRelaxation.lean),
[`ReplacementHamiltonian`](https://github.com/nickgou-nuke/info-geometry-lean/blob/b22b88bc70730f2ad213baede7d91e14a1223c43/lean/InfoGeometry/Quantum/ReplacementHamiltonian.lean), and
[`ReplacementGibbs`](https://github.com/nickgou-nuke/info-geometry-lean/blob/b22b88bc70730f2ad213baede7d91e14a1223c43/lean/InfoGeometry/Quantum/ReplacementGibbs.lean).
Its source constructs replacement relaxation, an exponential-parameter
derivative, positivity at finite matrix amplifications, target-relative radial
identities, and Gibbs stationarity for the replacement generator. Those
constructions complement the affine Gibbs entropy/energy transport and actual
logarithmic-score calculations here. Inspecting that draft's source is not a
compilation certificate for its declarations.

Three explicit compatibility results remain necessary for connecting the
drafts at the level of their APIs and dissipators:

1. `MatrixBoundaryPurification.normalizedGibbs` uses the inverse complex trace
   of the Gibbs weight; `MatrixGibbsEntropy.normalizedGibbsDensity` uses the
   inverse real part of that trace. Their equality follows mathematically from
   Hermitian trace reality and scalar compatibility, but they are not
   definitionally identical and this contribution does not add that bridge.
2. `ad ℂ ((-Complex.I) • H) ρ` and `unitaryFlow H ρ` represent the same ordered
   commutator after scalar-distribution rewrites. A consumer should supply the
   actual equality rather than rely on a naming match.
3. Replacement uses `γ • (trace ρ • Γ - ρ)`, while the existing score-based
   expression here uses `-Mρ Gρ`. A mobility identification must construct
   `Mρ Gρ = γ • (ρ - trace ρ • Γ)` with the required positivity and constraint
   properties. Sharing a stationary Gibbs state does not establish this.

In particular, taking `M = γ • (id - RΓ)` gives
`M(1) = γ • (1 - d • Γ)`, generally nonzero, so this naive assignment does not
automatically meet the identity-annihilation hypothesis proved sufficient here.
This is an explanatory operator calculation, not an additional Lean theorem
claim. Neither draft constructs a complete Carnot process; PR #406's actual
replacement trajectory is also distinct from a trajectory for its combined
Hamiltonian-plus-replacement generator.

## Proof dependency order for the new contribution

1. The existing Hermitian CFC Gibbs weight equals the native matrix exponential.
2. Native Hermitian CFC naturality handles unitary conjugation. Central energy
   shifts commute with every Hamiltonian; the exponential addition law applies
   only with that proved commutation.
3. Trace cyclicity gives the transformed partition function. Existing positive
   trace normalization cancels its scalar Boltzmann factor.
4. The transformed normalized state is actual unitary conjugation. Existing
   CFC entropy invariance then supplies the entropy conclusion.
5. Independently, the existing cyclic additive-trace identity annihilates
   commutators against the state's centralizer. Native functional calculus
   places spectral directions in that centralizer.
6. Energy conservation, logarithmic orthogonality, and the unitary tangent's zero trace give
   the concrete score's vanishing unitary pairing.
7. Substitution into the existing rate identity leaves precisely the mobility
   quadratic form; its sign follows from the stated nonnegativity assumption.
8. The Gibbs CFC centralizer relation makes its own Hamiltonian flow zero.
   Its actual normalized logarithm makes the score central at `T = β⁻¹`.
9. Native scalar-tower linearity computes the mobility response to that score.
   Its explicit value gives stationarity when `M(1) = 0`.

These are proof dependencies. No dependency edge to Gromov–Witten invariants,
spacetime Weyl geometry, a Goldstone theorem, or a wavefront is asserted.

## Carnot reading and the four different scale operations

Write `Γ(H, β) = exp(-βH) / Tr(exp(-βH))`, in units with Boltzmann constant one.
For a controlled family `H(λ) = λ H₀`, the effective Gibbs parameter is
`β λ`, with dimensionless exponent `β λ H₀`. A compensated stroke keeps that product fixed. A stroke at fixed
temperature can change it. The new transport theorem gives exact Gibbs
endpoint compatibility for the compensated stroke, including arbitrary
unitary frame changes and central energy shifts.

For example, take positive bath temperatures `Th > Tc`, inverse temperatures
`βh = 1 / Th`, `βc = 1 / Tc`, and `a = Tc / Th`. For two Hermitian Hamiltonians
`HA` and `HB`, the theorem supplies the following four endpoint assignments:

| Endpoint | Hamiltonian | Inverse temperature | Normalized state |
|---|---|---|---|
| A | `HA` | `βh` | `Γ(HA, βh)` |
| B | `HB` | `βh` | `Γ(HB, βh)` |
| C | `a • HB` | `βc = βh / a` | The same state as B |
| D | `a • HA` | `βc = βh / a` | The same state as A |

The B/C and D/A state equalities are instances of compensated scale transport.
They organize candidate hot, compensated, cold, and compensated strokes in
that order. They do not supply the paths joining the endpoints, the bath
couplings, or the heat/work integrals. This table is an application of the
general theorem, not an additional Lean process construction.

| Operation | Normalized state | Status of this interpretation |
|---|---|---|
| `P ↦ c • P`, then trace normalization | Unchanged for positive `c` and faithful `P` | Existing normalization theorem |
| `H ↦ a • H`, `β ↦ β / a` | Unchanged before an optional unitary frame change | New exact Gibbs transport |
| `H ↦ a • H` at fixed `β` | Generally changes the spectrum of the Gibbs state | Thermal control direction; no claim that all such changes are reversible |
| `ρ ↦ 1/d + c • (ρ - 1/d)` | Moves along the normalized radial line when positivity is maintained | Distinct state-space operation; the new theorem identifies its direction's Hilbert–Schmidt orthogonality |

A genuine Carnot protocol still requires two controlled thermal strokes,
two entropy-preserving strokes, bath temperatures, and heat/work accounting.
If reversible heat exchange gives `Qh = Th ΔS` and `Qc = -Tc ΔS`, with
`Th > Tc > 0` and `ΔS > 0`, its cyclic first-law ledger yields
`Wout / Qh = 1 - Tc / Th`. This conditional thermodynamic deduction is not
represented as a new Lean heat-engine theorem by these endpoint identities.

Likewise, if a scalar entropy path is nondecreasing and returns to its initial
value over a closed interval, it is constant on that interval. For a genuine
isolated GENERIC path with a symmetric positive semidefinite mobility and an
actual entropy-production formula, this excludes a strictly dissipative
periodic breather. Reversible periodic motion can remain. Constructing that
path, proving its entropy derivative, and connecting the mobility's quadratic
kernel to its vector-field kernel remain separate analytic work.

## Interpretation boundaries

- A unitary orbit has constant spectrum and entropy. Equal entropy alone does
  not imply unitary conjugacy. Stationarity for a specified Hamiltonian is a
  separate commutator condition.
- Scaling an unnormalized positive weight and renormalizing does not change
  its normalized state. This differs from moving radially about `1 / d` inside
  the trace-one state space.
- In dimension two, Bloch radius parametrizes the spectrum. In higher
  dimensions, a single radius does not determine the spectrum or entropy.
- A closed isolated metriplectic trajectory with nonnegative entropy
  production cannot have strictly positive production over a full period.
  This does not rule out reversible periodic motion, externally controlled
  Carnot cycles, or entropy-exporting nonequilibrium steady states.
- General dissipative motion need not be purely radial. Orthogonality claims
  must name their pairing; a Hilbert–Schmidt identity does not supply every
  thermodynamic metric.
- The native finite Gibbs trace is not automatically a Gromov–Witten
  generating function or a geometric volume. Those require explicit maps and
  compatibility results.
- Hamiltonian energy scaling, trace normalization, spacetime Weyl gauge
  transformations, and renormalization-group flow are different constructions.
- Wilson holonomy, Goldstone modes, characteristic wavefronts, and boundary
  reflection require their own carriers and dynamics. No such equivalence is
  inferred from shared terminology.

As an explicit mathematical counterexample to identifying entropy levels with
unitary orbits, the faithful diagonal probability matrices
`diag(1/3, 1/12, ..., 1/12)` (eight entries `1/12`) and
`diag(1/6, ..., 1/6, 1/24, ..., 1/24)` (five entries `1/6`, four entries `1/24`)
both have entropy `log 3 + (4/3) log 2`, but have different spectra. This
counterexample is an explanatory calculation, not an additional Lean theorem
claim in this contribution.

## Primary mathematical context

- [Beretta, Quantum thermodynamic Carnot and Otto-like cycles for a two-level system](https://quantum-thermodynamics.unibs.it/GPBeretta-quant-ph-0703261.pdf): distinguishes equilibrium identities from operational heat/work balance and varies the energy gap along both types of stroke.
- [Bloch, Morrison, and Ratiu, Gradient flows in the normal and Kähler metrics and triple bracket generated metriplectic systems](https://web2.ph.utexas.edu/~morrison/12arXiv1208.6193_morrison.pdf): metric dependence of orbit dynamics and the separate conservation/entropy-production conditions.
- [Kimura, The Bloch Vector for N-Level Systems](https://arxiv.org/abs/quant-ph/0301152): the qubit ball and higher-dimensional state regions have different geometry.
- [Mittnenzweig and Mielke, An entropic gradient structure for Lindblad equations and couplings of quantum systems to macroscopic models](https://www.wias-berlin.de/people/mielke/preprints/wias_preprints_2320_20170301.pdf): the entropic-gradient result retains detailed balance with respect to a thermal state as a hypothesis.
- [Kontsevich and Manin, Gromov–Witten Classes, Quantum Cohomology, and Enumerative Geometry](https://www.ihes.fr/~/maxim/TEXTS/WithManinCohFT.pdf): specifies geometric classes and generating potentials; a finite thermal trace is not identified with them merely by using the word partition.

Literature supplies context, not Lean acceptance. No diagram or graph-index
match is used as proof. The local navigation preflight found no current
declaration-DAG, type, LeanSearch, or raw-InfoTree index artifact in this
checkout. The actual owner/import search and native compiler results determine
the stated scope.

## Dependency repair and verification ledger

Observed upstream failure: PR #399's focused native run
`44101793290`, job `134103457877`, compiled its seven prerequisite modules but
failed in `log_normalizedGibbsDensity_eq_thermalModularHamiltonian` on the
real-to-complex negative scalar conversion. This contribution replaces the
inapplicable specialized simp rule with `map_neg` and `Complex.coe_algebraMap`, and removes an unused
section-level `Nonempty` instance from the purely algebraic normalized
exponential expression. No substantive theorem conclusion is weakened.

### Reviewed source freeze

The three new owners have independent mathematical/API source review. A
separate QA pass accepted the strict placeholder, refute, OpenGauss, semantic,
static Gate 4, whitespace, workflow-script, source-closure, link, and theorem-count
checks. Static Gate 4 is lexical only and is not a native certificate.
The focused closure has 15 repository modules and 26 direct
Mathlib roots, independently checked against the maintained closure helper.

| Selected owner | SHA256 of the reviewed source |
|---|---|
| `MatrixGibbsEntropy` | `12fd66e9609d4b8becbc20fdad9e471ae8932d2981bc985491d3db4e682f5c51` |
| `MatrixGibbsScaleTransport` | `74fce121f2e92f1618653cc2b5e8c1545fcca68ad286a4cb97d1c6633d1a00a5` |
| `MatrixUnitarySpectralOrthogonality` | `b133f8fe8f74198f348c6df15a01beb1de700dec15fd1ea885bb922f91b2edbb` |
| `MatrixGibbsMetriplecticEquilibrium` | `04bade35580eb64d9aa9200866e0acbfb99ecb6d259729aee76a44a3ed9fb354` |

### Native and publication status at the draft checkpoint

- Lean remains `v4.34.1`; Mathlib remains
  `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- The first independent native attempt compiled the repaired Gibbs entropy
  owner with zero warnings, but found API/elaboration errors in earlier
  transport and orthogonality candidates. Those failures are preserved as
  evidence; they are not acceptance of the repaired sources above.
- The original local four-owner run is queued through the maintained shared
  build lock with the proof sources published at draft head `fb5b9da0`. Its
  original checkout is preserved. It cannot certify the subsequent repairs
  identified by the source hashes above; exact-head CI checks those revisions.
  No successful native axiom audit of all four owners is claimed yet.
- The actual installed pre-commit hook passed at local source checkpoint
  `a752a9005b586148fc7dafe3d3eef5fd1324d61b`, tree
  `bb190923bcf8cd8223b1dd07f31373fc538d93e6`. Later documentation updates do not
  change the frozen proof or verification-helper sources.
- The actual installed pre-push hook was invoked on that clean checkpoint as
  a new branch. It classified the full range from main and requested the
  maintained locked Lake build including `InfoGeometry.All`; it is queued.
  Neither root-package acceptance nor full-mode gate coverage is claimed.
- The maintained `python tools/infra/ci_bootstrap.py paths` command returned
  exit 1: HomotopyHypothesis and Atlas have missing configurations and are
  untracked path dependencies; GIFT has a missing configuration and an
  uninitialized pinned gitlink. InfoGeometryCore passed that availability and
  provenance check. This preflight is not compilation. No replacement pins,
  stub dependencies, or gate exceptions were introduced.
- The upstream publication is a draft with native/QA acceptance pending.
  The focused workflow is configured to compile the exact source head,
  freshly compile every repository module in the closure, require zero
  selected-owner warnings, and audit every owned declaration against the
  foundational axiom whitelist. Remote workflow results must be observed
  separately; publication itself is not a compilation certificate.

Compilation, native axiom inspection, independent acceptance, and complete
repository build status remain separate gates. This ledger records the draft
checkpoint and will be updated as the queued checks produce observed results.

### First exact-head CI result and bounded repair

[Focused run 44272453540](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44272453540)
tested draft head `fb5b9da0c14d41c86f2b7e85d50e7f424389eee4`. Source-head,
Lean archive checksum, dependency-pin, and scoped cache checks passed. The
parent Gibbs entropy owner compiled with zero warnings. Transport had three
elaboration errors and two unused-simp warnings; orthogonality had one CFC
elaboration error and one unused-section-instance warning. The equilibrium
owner was blocked by its orthogonality dependency. The native axiom audit was
not reached. The failed logs and source snapshots were uploaded by that run.

The reviewed repair uses `Matrix.star_eq_conjTranspose` for the CFC argument,
`Complex.smul_re` and `smul_eq_mul` for the two real-trace readouts, and the
explicit `IsSelfAdjoint` predicate for both CFC commutation and identity.
The trace-zero lemma omits its unused `DecidableEq` instance. Its generated
type becomes more general; mathematical conclusions, remaining hypotheses,
imports, ordered matrix products, and acceptance gates are unchanged.
The repaired source hashes are listed above. Their independent source/API
review passed; native acceptance remains pending the next exact-head run.
