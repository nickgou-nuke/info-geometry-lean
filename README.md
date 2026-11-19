# InfoGeometry

Lean 4 / Mathlib research in information geometry, noncommutative operator
algebra, Clifford and Zorn constructions, categorical limits, and mathematical
physics. The project is a growing atlas of definitions, theorems, and explicit
comparisons developed through human–AI collaboration. Its research motivation
includes the spinorial *prima materia* program; the mathematical claims are the
statements in the Lean owners, with their actual hypotheses.

> Documentation source review: 2026-11-15, against
> [`abd5826b3676`](https://github.com/nickgou-nuke/info-geometry-lean/commit/abd5826b3676fab6231c66b646ec1cc5aeed6732)
> plus scoped working-tree kernel verification of
> [`InfoGeometry.Foundations.InfoGeometryCoreLibrary`](lean/InfoGeometry/Foundations/InfoGeometryCoreLibrary.lean)
> and
> [`InfoGeometry.OperatorAlgebra.PeirceBiSandwich.All`](lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/All.lean).
> This records source inspection and scoped kernel check of the named targets,
> not a whole-repository CI rebuild.

## Start here

| Purpose | Entry point |
|---|---|
| Set up and run a scoped check | [Getting started](docs/GETTING_STARTED.md) |
| Work as a coding or mathematical agent | [AGENTS.md](AGENTS.md), then the [canonical pipeline](docs/CANONICAL_AGENT_PIPELINE.md) |
| Find maintained guides and historical notes | [Documentation map](docs/README.md) |
| Explore the main Lean source | [lean/InfoGeometry/](lean/InfoGeometry/) and [InfoGeometry.All](lean/InfoGeometry/All.lean) |
| Core library & multi-pillar integration | [InfoGeometryCoreLibrary](lean/InfoGeometry/Foundations/InfoGeometryCoreLibrary.lean) |
| Peirce bi-sandwich suite & umbrella synthesis | [PeirceBiSandwich.All](lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/All.lean) |
| Trace operator-algebra owners | [OperatorAlgebra guide](lean/InfoGeometry/OperatorAlgebra/README.md) and [Peirce archetype ledger](docs/PEIRCE_OPERATOR_ARCHETYPES.md) |
| Search before proposing a construction | [Repository deep-search protocol](docs/REPO_DEEP_SEARCH_PROTOCOL.md) |
| KMS bath & anisotropic Kubo–Mori | [KMSBathAndAnisotropicKuboMori](lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/KMSBathAndAnisotropicKuboMori.lean) & [KMSCompletePositivity](lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/KMSCompletePositivityAndKrausSemigroup.lean) |
| Custodial twin loop & Josephson lattice | [CustodialTwinLoopAndJosephsonLattice](lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/CustodialTwinLoopAndJosephsonLattice.lean) |
| Cl(1,1) superbase & cut-rank | [Cl11SuperBaseAndEntanglementRank](lean/InfoGeometry/Clifford/Cl11SuperBaseAndEntanglementRank.lean) |
| Unbounded resolvent flow & C₀-group | [TripotentUnboundedResolventFlow](lean/InfoGeometry/OperatorAlgebra/TripotentUnboundedResolventFlow.lean) & [UnboundedHilbertResolvent](lean/InfoGeometry/OperatorAlgebra/UnboundedHilbertResolventAndC0GroupWitness.lean) |
| Elitzur lattice gauge & N-link chain | [ElitzurLatticeGaugeProjection](lean/InfoGeometry/OperatorAlgebra/ElitzurLatticeGaugeProjection.lean) & [NLinkElitzurChain](lean/InfoGeometry/OperatorAlgebra/NLinkElitzurChainAndCompactU1Gauge.lean) |
| Noncommutative GKSL & spin cumulants | [GKSLGibbsAndDuallyFlatSpinCumulants](lean/InfoGeometry/Modular/GKSLGibbsAndDuallyFlatSpinCumulants.lean) |
| Welded 3D quantum Spohn synthesis | [WeldedBlochQuantumSpohnSynthesis](lean/InfoGeometry/Modular/WeldedBlochQuantumSpohnSynthesis.lean) |
| 3D anisotropic BKM Hessian & multi-qubit | [AnisotropicBKMHessianAndMultiQubitSpohn](lean/InfoGeometry/Modular/AnisotropicBKMHessianAndMultiQubitSpohn.lean) |
| Bipartite rebit separability vs Peirce defect | [BipartiteSeparabilityAndPeirceEntanglement](lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/BipartiteSeparabilityAndPeirceEntanglement.lean) |
| UHF C*-algebra inductive limit completion | [UHFColimitCStarCompletion](lean/InfoGeometry/Algebra/UHFColimitCStarCompletion.lean) |
| Discrete Cantor Fourier uncertainty (FUP) | [DiscreteCantorFourierUncertainty](lean/InfoGeometry/Algebra/DiscreteCantorFourierUncertainty.lean) |
| Pin(5,5) nondegenerate Krein bridge | [Pin55NondegenerateKreinBridge](lean/InfoGeometry/Lie/Pin55NondegenerateKreinBridge.lean) |
| Weyl–Cartan split & Iwasawa KAN polar | [WeylCartanKANPolarEquivariance](lean/InfoGeometry/Algebra/WeylCartanKANPolarEquivariance.lean) & [ComplexSL2IwasawaAndHyperbolicPolar](lean/InfoGeometry/Algebra/ComplexSL2IwasawaAndHyperbolicPolar.lean) |
| Noncommutative Weyl–Cartan & polar equivariance | [NoncommutativeWeylCartanKANPolarEquivariance](lean/InfoGeometry/Algebra/NoncommutativeWeylCartanKANPolarEquivariance.lean) |
| Real KAN polar & Weyl trace equivariance | [WeylTraceKANPolarEquivariance](lean/InfoGeometry/Canonical/WeylTraceKANPolarEquivariance.lean) |
| Bloch-ball Umegaki & quantum Spohn dissipation | [BlochBallUmegakiAndQuantumSpohn](lean/InfoGeometry/Modular/BlochBallUmegakiAndQuantumSpohn.lean) |
| Schrödinger GKSL flow & semigroup bridge | [SchrodingerGKSLFlowBridge](lean/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean) & [src/ mirror](src/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean) |
| Hilbert boundary sewn anomaly cancellation | [ConcreteHilbertSewnAnomaly](lean/InfoGeometry/Canonical/ConcreteHilbertSewnAnomaly.lean) |
| Chebyshev prime counting & Hoeffding tail | [ChebyshevPrimeAndHoeffdingBounds](lean/InfoGeometry/Arithmetic/ChebyshevPrimeAndHoeffdingBounds.lean) |
| Solve et Coagula noncommutative causal poset | [SolveEtCoagulaPeirceAporiaPoset](lean/InfoGeometry/OperatorAlgebra/SolveEtCoagulaPeirceAporiaPoset.lean) |
| Lattice OS transfer semigroup & mass gap | [OsterwalderSchraderTransferSemigroupAndMassGap](lean/InfoGeometry/OperatorAlgebra/OsterwalderSchraderTransferSemigroupAndMassGap.lean) |
| Continuous L²([0,1]) Cantor FUP contraction | [ContinuousL2CantorFourierUncertainty](lean/InfoGeometry/Analysis/ContinuousL2CantorFourierUncertainty.lean) |
| Global SO(5,5) Lie group & conformal 3-grading | [SO55GlobalConformalPrecursors](lean/InfoGeometry/Lie/SO55GlobalConformalPrecursors.lean) |
| Logarithmic integral li(x) & ζ real-pole divergence | [RiemannZetaLogarithmicIntegralPrecursors](lean/InfoGeometry/Arithmetic/RiemannZetaLogarithmicIntegralPrecursors.lean) |

Search definitions, imports, instances, theorem statements, and consumers before
declaring a construction absent or identifying two mathematical presentations.
A module name or graph edge is a search aid. A formal comparison needs a stated
map and theorem on the relevant carriers.

## Representative mathematical results

These are selected entry points, not a completeness claim for their fields.
Each linked owner supplies the precise typeclasses and hypotheses.

| Area | Source-backed result | Owner |
|---|---|---|
| Peirce operator identities | Polynomial identities for an idempotent and arbitrary coefficients in an associative ring; A60 gives `τ₁ − τ₂ = −J − 2Σ` and `hProjSig(τ₁ − τ₂) = −16 V²Σ` | [CyclotomicBridge](lean/InfoGeometry/OperatorAlgebra/PeirceSpine/CyclotomicBridge.lean) |
| Five-grade parity | The grade ±1 projectors sum to the odd Peirce component; the −2, 0, +2 projectors sum to the even component | [TripotentParity](lean/InfoGeometry/OperatorAlgebra/PeirceSpine/TripotentParity.lean) |
| Chiral zero-mode restriction | Projector intertwiners from anticommutation, and an involutive linear equivalence on the kernel under the stated tripotence and involution hypotheses | [TripotentChiralRestriction](lean/InfoGeometry/Core/TripotentChiralRestriction.lean) |
| Noncommutative RPA blocks | Exact block squaring and Hadamard intertwining retaining `a*b - b*a` and both ordered products | [OperatorRPABlock](lean/InfoGeometry/Physics/OperatorRPABlock.lean) |
| Operator-weighted phonons | Mode-sum commutators with the correction terms `[Ωᵢ, X] * numberOpᵢ` retained | [NuclearPhononOperatorWeights](lean/InfoGeometry/Physics/NuclearPhononOperatorWeights.lean) |
| Matrix towers | Full-matrix algebraic direct limits, stage maps, and an induced star structure | [Cl11TensorTowerLimit](lean/InfoGeometry/Clifford/Cl11TensorTowerLimit.lean) |
| Categorical Zorn stages | A `ModuleCat ℂ` diagram and multiplication descended through its colimits | [ZornUHFColimit](lean/InfoGeometry/Categorical/ZornUHFColimit.lean) |
| Algebraic Cuntz shift | Injectivity of the existing canonical shift from a generator-level left inverse | [CuntzHoppingCantorLattice](lean/InfoGeometry/NCG/CuntzHoppingCantorLattice.lean) |
| Finite matrix Lax data | Trace cancellations and the determinant/nonzero-kernel equivalence | [LaxPairIsospectralMassGap](lean/InfoGeometry/NCG/LaxPairIsospectralMassGap.lean) |
| Split-octonion derivations | A stabilizer predicate and consequences for a parameterized derivation family | [GunaydinGurseySU3Stabilizer](lean/InfoGeometry/NCG/GunaydinGurseySU3Stabilizer.lean) |
| Parametric Cramér–Rao bound | Score mean zero, Fisher information $I(\theta) = \mathbb{E}[S_\theta^2]$, and variance lower bound $\mathrm{Var}(T) \ge 1 / I(\theta)$ (`cramer_rao_unbiased_lower_bound`) on finite sample spaces | [ParametricCramerRao](lean/InfoGeometry/InformationGeometry/ParametricCramerRaoAndCumulants.lean) |
| Csiszár divergence monotonicity | Convex $f$-divergence non-negativity and monotonicity under column-nondegenerate Markov kernels, with Petz recovery vector (`posteriorMarkovKernel`) | [CsiszarAlphaDivergence](lean/InfoGeometry/InformationGeometry/CsiszarAlphaDivergenceAndChentsovMonotonicity.lean) |
| Eguchi metric & dual curvature | KL divergence Hessian yielding Fisher metric `eguchi_kl_right_hasDerivAt`, third cumulant tensor, and dually flat affine connections | [EguchiMetrics](lean/InfoGeometry/InformationGeometry/EguchiMetricsAndDualFlatCurvature.lean) |
| Markov categories & colimits | Finite sample-space category `FinSampleSpace` with stochastic transition kernels, composition `compose`, and filtered colimit trace states `colimitNormalizedTrace` | [MarkovCategory](lean/InfoGeometry/Categorical/MarkovCategoryAndColimitInformation.lean) |
| Markov comonoids & Blackwell | Copying kernel `copyKernel`, discard, and swap forming Markov comonoids with categorical Blackwell sufficiency | [MarkovComonoid](lean/InfoGeometry/Categorical/MarkovComonoidAndBlackwellSufficiency.lean) |
| Quantum Kadison–Schwarz bound | Kadison–Schwarz inequality $\Phi(A)^* \Phi(A) \le \Phi(A^* A)$ for positive unital maps and SLD quantum Cramér–Rao variance lower bound `quantumVariance` | [KadisonSchwarz](lean/InfoGeometry/OperatorAlgebra/KadisonSchwarzAndQuantumCramerRao.lean) |
| GNS representation & Petz metrics | GNS Hilbert representation `gnsRep` from positive functionals, cyclic vector `gnsCyclicVec`, and Petz monotone Riemannian metric classification | [GNSRepresentation](lean/InfoGeometry/OperatorAlgebra/GNSRepresentationAndPetzMonotoneMetrics.lean) |
| Noncommutative Krein pairing | Krein indefinite inner product with fundamental symmetry $J$; positive-sector trace nonnegativity `positive_sector_krein_pairing_nonneg` and Zorn twisted Hilbert–Schmidt positivity | [NoncommutativeKrein](lean/InfoGeometry/Algebra/NoncommutativeKreinMathlibBridge.lean) |
| Krein–Peirce tower intertwining | Peirce $(1,1)$-sector positive Krein pairing `peirce11_positive_sector_krein_positivity_and_bianchi`, Bianchi curvature identity, and Berry–Chern curvature transport | [KreinPeirceTower](lean/InfoGeometry/Algebra/KreinPeirceTowerIntertwine.lean) |
| Peirce Tetraktys Krein bridge | Inductive stage inclusions preserving Peirce–Yang–Mills curvature, and Casimir operator stage trace nonnegativity `towerTrace_genV_nonneg` | [PeirceTetraktys](lean/InfoGeometry/Algebra/PeirceTetraktysKreinBridge.lean) |
| Kitaev sublattice cut & aporia | Sublattice cut idempotent `sublatticeCut_idem`, Majorana anticommutation `sublatticeCut_majC_noncommuting`, and parity intertwining | [KitaevPeirceAporia](lean/InfoGeometry/Algebra/KitaevPeirceAporiaEpistemicSynthesis.lean) |
| Heisenberg dissipator defect | Dissipator identities $D_L(1) = 0$ (`dissipatorTerm2_one`) and star-multiplication defect preservation `dissipatorTerm2_star_mul_defect` | [GKSLDissipation](lean/InfoGeometry/Modular/GKSLDissipationIdentity.lean) |
| Cyclic GKSL trace & spin cumulants | Division-free matrix cyclic-trace conservation `gksl_matrix_cyclic_trace_zero` over any ring with cyclic trace, Witt CAR bridge, KMS detailed balance, and Spohn relaxation `master_spohn_entropy_production_and_gibbs_relaxation` | [GKSLGibbs](lean/InfoGeometry/Modular/GKSLGibbsAndDuallyFlatSpinCumulants.lean) |
| Welded 3D quantum Spohn synthesis | Forward Kolmogorov ODE, open Bloch ball forward invariance iff $t \ge 0$, universal 3D `CFC.log`, 3-state Quantum Pythagorean identity `rung3_quantum_pythagorean_identity`, and Spohn–Jeffreys coherence-lag law `quantum_spohn_jeffreys_coherence_lag` | [WeldedBlochSpohn](lean/InfoGeometry/Modular/WeldedBlochQuantumSpohnSynthesis.lean) |
| 3D anisotropic BKM Hessian | Second directional derivative of Umegaki divergence on $\mathbb{B}^3$ equaling anisotropic BKM metric `bkmMetricTensor3_self`, coherence-lag identification, and multi-qubit product additivity | [AnisotropicBKMHessian](lean/InfoGeometry/Modular/AnisotropicBKMHessianAndMultiQubitSpohn.lean) |
| Peirce bi-sandwich core & defect | Ring idempotent $P^2=P$, defect $\delta(P)=P^2-P$, Casimir $V$, quartet $(\Phi, J, V, \Sigma)$, algebraic dictionary `peirceBiSandwich_spine_dictionary`, and idempotent characterization `delta_eq_zero_iff_isIdempotent` | [PeirceBiSandwich.Core](lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/Core.lean) |
| Pinched super-extension & BdG horizon | $M_8(\mathbb{Z})$ explicit operators $P_8, A_8, D_8, G_8$, Day convolution localization `DayRel`, on-shell Weyl reflection, and unitary defect law $u_0^* u_0 - 1 = \delta(V)$ (`integral_unitary_defect_law`) | [PinchedSuperExtension](lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/PinchedSuperExtension.lean) |
| Supertwistor 16 & Real Bloch | Kronecker lift $M_{16}(\mathbb{R}) \cong M_8(\mathbb{R}) \otimes M_2(\mathbb{R})$, real-rebit symmetric centralizer triviality `real_rebit_symmetric_centralizer_trivial`, polarized Fermi sea $P_{\mathrm{Fermi}}$, and pinched Gibbs marginal | [Supertwistor16](lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/Supertwistor16AndRealBloch.lean) |
| Klein Reynolds off-shell coercivity | Integer scale-4 Klein Reynolds projector `kleinReynolds4`, scale-8 factored projection `factoredReynolds8`, off-shell coercivity, and operator Pythagorean identity `operator_pythagorean` | [OffShellCoercivity](lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/OffShellCoercivityAndColimitGap.lean) |
| KMS bath & anisotropic Kubo–Mori | Inter-sector Kraus refeeding vanishing $L^T (Q_+ X Q_+) L = 0$ for $K_8, \Omega_8$, CPTP partial trace `partialTraceKKT` : $M_8(\mathbb{R}) \to M_2(\mathbb{R})$, KMS detailed balance, and anisotropic bounds $1 < \mathrm{artanh}(s)/s < 1/(1-s^2)$ (`artanh_deriv_and_anisotropic_kubo_mori_bounds`) | [KMSBath](lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/KMSBathAndAnisotropicKuboMori.lean) |
| Custodial twin loop protection | $\mathbb{Z}_2$ real freeze in $M_8(\mathbb{Z})$ ($D_1^T = D_1, D_2^T = -D_2$) vs. $U(1)$ BdG circle in $M_{16}(\mathbb{R})$; custodial twin $W_{\mathrm{twin}} = \Phi + P_0$ ($W^2 = 1, W D_1 W = -D_1$); all-loop odd-power vanishing `custodial_all_loop_odd_power_vanishing`; and 1-loop parity-odd birefringence | [CustodialTwinLoop](lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/CustodialTwinLoopAndJosephsonLattice.lean) |
| KMS complete positivity & Kraus flow | Full $k$-positivity of `partialTraceKKT` under arbitrary finite ancilla $\kappa$ (`partialTraceKKT_amplified_preserves_posSemidef`), 4-channel Kraus decomposition of thermal semigroup, and generator-flow identity `gkslFlow_eq_thermalSemigroupC` | [KMSCompletePositivity](lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/KMSCompletePositivityAndKrausSemigroup.lean) |
| Two-rebit bipartite separability | Unit two-rebit pure states $\psi$; exact equivalence $\mathrm{IsProductState}(\psi) \leftrightarrow \det(C_\psi) = 0 \leftrightarrow \delta(\mathrm{Tr}_B(|\psi\rangle\langle\psi|)) = 0$ (`isProductState_iff_det_zero`, `isProductState_iff_idempotencyDefect_zero`); and separation from single-cut Peirce defect | [BipartiteSeparability](lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/BipartiteSeparabilityAndPeirceEntanglement.lean) |
| Graded Clifford superbase & rank | Graded base superalgebra $(B, \theta_B)$ unrolling `superMatrixParity`, Koszul transpose law `koszulTransposeSign`, idempotent chains ($T_3^3 - \frac{1}{2} T_3^2 + \frac{1}{8} T_3 = 0$), two-sided cut-rank bounds, odd-dimension complex structure obstruction `odd_dim_no_complex_structure`, and tripotent zero-mode forcing | [Cl11SuperBase](lean/InfoGeometry/Clifford/Cl11SuperBaseAndEntanglementRank.lean) |
| Tripotent resolvent flow | Resolvent and Cayley transform commute with tripotent $S$ ($S^3=S$) and preserve 5 grades `resolvent_and_cayley_commute_and_preserve_fiveGrades`, and unbounded generator $\leftrightarrow$ bounded resolvent Kato–Trotter equivalence `unbounded_generator_commute_iff_resolvent_commute` | [TripotentUnboundedResolvent](lean/InfoGeometry/OperatorAlgebra/TripotentUnboundedResolventFlow.lean) |
| Hilbert $\ell^2$ unbounded generator | Tripotent $S_{\ell^2}$ on $\ell^2(\mathbb{N})$; dense subspace $D_{\mathrm{fin}}$ and maximal domain $D_{\mathrm{max}}$; operator-norm unbounded skew-adjoint generator $K_{\mathrm{max}}$; contractive resolvent $R_{\mathrm{unb}}$; isometric group $U_{\mathrm{unb}}(t)$; and non-trivial instances `unboundedResolventData`, `unboundedC0Group` | [UnboundedHilbertResolvent](lean/InfoGeometry/OperatorAlgebra/UnboundedHilbertResolventAndC0GroupWitness.lean) |
| Elitzur lattice gauge projection | Finite Haar–Reynolds Gibbs expectation invariance, Elitzur local gauge expectation vanishing for all couplings `elitzur_local_gauge_expectation_zero`, $\mathbb{Z}_2$ link-Higgs witness `z2_link_higgs_elitzur_vs_wilson_string`, and quantum physical projection $P_{\mathrm{phys}}$ | [ElitzurGauge](lean/InfoGeometry/OperatorAlgebra/ElitzurLatticeGaugeProjection.lean) |
| $N$-link gauge chain & $U(1)$ Haar | $N$-link gauge-Higgs chain on $\mathbb{Z}_2$, exact local gauge vanishing for all vertices, closed-form Wilson string $(\tanh J)^L$ with exponential mass-gap decay, and compact $U(1)$ Haar integral Elitzur vanishing for all non-zero charges `u1HaarAvg` | [NLinkElitzurChain](lean/InfoGeometry/OperatorAlgebra/NLinkElitzurChainAndCompactU1Gauge.lean) |
| $2^\infty$ UHF inductive limit completion | Unital block-doubling $\star$-embeddings $M_{2^n}(\mathbb{C}) \hookrightarrow M_{2^{n+1}}(\mathbb{C})$, strict $L^2$ operator-norm isometry `uhfStep_isometry`, inductive limit $2^\infty$ UHF $\star$-algebra `UHFAlg`, CStarRing, and metric completion `UHFCStar` | [UHFCompletion](lean/InfoGeometry/Algebra/UHFColimitCStarCompletion.lean) |
| Discrete Cantor Fourier uncertainty | Normalized unitary DFT matrix $D_N \in M_N(\mathbb{C})$, exact Hilbert–Schmidt identity for projection-restricted operator $P_\Omega D_N P_T$ (`fupOp_apply`), $L^2$ operator-norm bound $\le \sqrt{|\Omega| \cdot |T| / N}$, and multiscale exponential contraction on Cantor digit-restricted subsets | [DiscreteCantorFUP](lean/InfoGeometry/Algebra/DiscreteCantorFourierUncertainty.lean) |
| Nondegenerate Krein signature $(5,5)$ | Canonical signature $(5,5)$ diagonal metric $J_{5,5}$ on $\mathbb{R}^{10}$, strict nondegeneracy of Krein bilinear form $\langle x, y \rangle_K$ (`kreinForm55_nondegenerate`), positive/negative definite 5D sectors, 5D totally isotropic diagonal Witt subspace, and $\mathfrak{so}(5,5)$ Lie algebra invariance | [Pin55KreinBridge](lean/InfoGeometry/Lie/Pin55NondegenerateKreinBridge.lean) |
| Noncommutative Weyl–Cartan split & KAN | Noncommutative threefold matrix split $2 M = \text{weylScalePart}(M) + \text{tracelessSymPart}(M) + \text{tracelessAntisymPart}(M)$ (`weyl_cartan_split`), Plemelj–Newton trace-to-determinant identity, Iwasawa $K A N$ subgroups and Polar Gram reduction, unitary and symmetry equivariance, and closed-form $SL(2,\mathbb{R})$ Iwasawa $K A N$ existence/uniqueness `sl2_iwasawa_kan_exists_unique` | [WeylCartanKAN](lean/InfoGeometry/Algebra/WeylCartanKANPolarEquivariance.lean) |
| Complex $SL(2,\mathbb{C})$ Iwasawa & polar | Closed-form existence and uniqueness ($\exists!$) of complex $GL(2,\mathbb{C})$ and $SL(2,\mathbb{C})$ Iwasawa $K A N$ decompositions `sl2_complex_iwasawa_kan_exists_unique`, and closed-form existence and uniqueness of $GL(2,\mathbb{C})$ unitary polar decomposition `gl2_complex_polar_decomposition_closed_form` | [ComplexSL2Iwasawa](lean/InfoGeometry/Algebra/ComplexSL2IwasawaAndHyperbolicPolar.lean) |
| Chebyshev prime counting & Hoeffding | Hoeffding lemma for $[0,1]$ Bernoulli variables `hoeffding_bernoulli_mgf`, exponential binomial tail bound beating trivial cardinality bound `binomTailProb_le_two_mul_exp`, primorial bound $\prod_{p \le n} p \le 4^n$, Chebyshev's $\vartheta(n) \le (2\ln 2) n$, and constructive two-sided Erdős–Chebyshev prime-counting bounds $\Theta(n / \ln n)$ | [ChebyshevPrimeBounds](lean/InfoGeometry/Arithmetic/ChebyshevPrimeAndHoeffdingBounds.lean) |
| Solve et Coagula causal poset | 5-stage causal compilation chain ($\mathcal{E}\mathcal{C}_1 \prec \dots \prec \mathcal{E}\mathcal{C}_5$), characteristic-free binary cut grading laws `binary_cut_idempotent_and_grading_laws`, fourfold relational Peirce anatomy & quiver multiplication, transcendent quartet $(\Phi, J, V, \Sigma)$ with universal creation lock, Socratic aporia $\delta(X) = X^2 - X$, infinite non-periodic orbit in $M_2(M_2(\mathbb{Z}))$, Newton–Peirce tower and `ClTowerColimit` transport, and bounded acyclic causal poset `SolveEtCoagulaNode` | [SolveEtCoagula](lean/InfoGeometry/OperatorAlgebra/SolveEtCoagulaPeirceAporiaPoset.lean) |
| Peirce bi-sandwich umbrella synthesis | Comprehensive synthesis theorem `peirce_biSandwich_archetypes_synthesis` connecting core defects, custodial twin protection, KMS detailed balance and Kraus completeness, graded Clifford unrolling and cut-rank, unbounded resolvent flow and Elitzur lattice gauge, and the Solve et Coagula causal poset | [PeirceBiSandwich.All](lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/All.lean) |
| Real KAN polar & Weyl trace equivariance | Closed-form $GL_2^+(\mathbb{R})$ Iwasawa $K A N$ factorization `real_gl2_pos_iwasawa_factorization` and uniqueness `real_gl2_pos_kan_unique`, $SO(2) \times \mathrm{SPD}(2)$ polar factors `real_gl2_pos_polar_factorization`, positive definiteness `real_gl2_pos_polar_stretch_posDef`, uniqueness `real_gl2_pos_polar_unique`, conformal-orthogonal similarity equivariance `real_gl2_pos_polar_conjugation_equivariance`, Frobenius Pythagorean split `real_weyl_cartan_frobenius_pythagorean`, Gram bridge $P^2 = M^\top M = N^\top A^2 N$ (`real_iwasawa_polar_gram_bridge`), and pushed-metric polar factorization `relative_metric_polar_factorization` | [WeylTraceKANPolar](lean/InfoGeometry/Canonical/WeylTraceKANPolarEquivariance.lean) |
| Noncommutative Weyl–Cartan & Iwasawa KAN | Acyclic dependency poset `kpPoset_actual_dependencies` (`KP1 ≤ KP5`, `KP2 ≤ KP4`, `KP3 ≤ KP4`), threefold split $2 \bullet M = M_{\mathrm{Weyl}} + M_{\mathrm{sym}}^0 + M_{\mathrm{antisym}}^0$ with Plemelj–Newton identity `weyl_cartan_split_and_noncommutative_trace_to_det`, fiber center equivalence `fiberEmbed_central_iff` with $M_2(\mathbb{Z})$ non-central witness, Iwasawa $K, A, N$ subgroups with Polar Gram reduction and Schur complement recovery `iwasawa_kan_subgroups_and_polar_gram_reduction`, unitary symmetry equivariance `polar_decomposition_unitary_equivariance` / `polar_factorization_pushed_metric_naturality`, fourfold symmetry equivariance `iwasawa_kan_symmetry_equivariance`, and diamond synthesis `kan_polar_gram_fiber_unitary_equivariance` | [NoncommutativeWeylCartan](lean/InfoGeometry/Algebra/NoncommutativeWeylCartanKANPolarEquivariance.lean) |
| Bloch-ball Umegaki & quantum Spohn | Star-projection `spectralProjector ρ` of trace 1 and exact matrix logarithm `CFC.log ρ = twoSheet P (log ((1+r)/2)) (log ((1-r)/2))` (`spectralProjector_twoSheet_and_cfc_log`), modular Hamiltonian logarithm `gibbsDensityC_strictlyPositive_and_cfc_log`, trace formula and pinching Pythagorean decomposition $D_{\mathrm{Umegaki}}(\rho \| \rho_\theta) = (\phi(r) - \phi(z)) + D_\phi(z \| \eta_\theta)$ with non-negative coherence relative entropy and faithfulness (`umegakiKernel_trace_and_coherence_pythagoras`), Kolmogorov forward ODE `hasDerivAt_thermalSemigroupC_eq_lindbladian`, open Bloch-ball preservation `thermalSemigroupC_preserves_blochBall`, and three-channel KMS Spohn rate dissipation with asymptotic Gibbs relaxation `master_bloch_umegaki_spohn_and_gibbs_relaxation` / `master_welded_3d_quantum_semigroup_cumulant_spohn_synthesis` | [BlochBallUmegakiSpohn](lean/InfoGeometry/Modular/BlochBallUmegakiAndQuantumSpohn.lean) |
| Schrödinger GKSL flow & semigroup | Continuous linear generator assembly `generatorCLM` satisfying `generatorCLM_apply`, real continuous endomorphism `generatorEnd`, bounded exponential flow `gkslFlow`, operator-valued semigroup law `gkslFlow_add` ($T_{s+t} = T_s \circ T_t$), orbit derivative `hasDerivAt_gkslFlow_orbit` ($\frac{d}{dt} T_t(X) = \mathcal{L}(T_t(X))$), global Banach-space ODE uniqueness `gkslFlow_unique_of_ode` via Lipschitz continuous generator, and full matrix trace conservation `realTrace_gkslFlow` ($\operatorname{Re}\operatorname{Tr}(T_t(X)) = \operatorname{Re}\operatorname{Tr}(X)$) | [SchrodingerGKSLFlow](lean/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean) & [src/ mirror](src/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean) |
| Hilbert boundary sewn anomaly cancellation | Completed binary Cantor Hilbert boundary carrier $H_{lp}(E) = \ell^2(\text{Cantor}, E \times E)$, unitary modular swap isometry `J_lp_clm` ($J^2 = \mathrm{id}$) and chiral symmetry isometry `epsilon_lp_clm` ($\varepsilon^2 = \mathrm{id}$), $\mathrm{Cl}(1,1)$ Clifford anticommutation `J_lp_clm_comp_epsilon_lp_clm` ($J \varepsilon = K$) and `J_lp_clm_anticomm_epsilon_lp_clm` ($J \varepsilon = -\varepsilon J$), self-adjointness `inner_J_lp_clm_selfAdjoint`, Cuntz $O_2$ branch sewing invariance `S_left_lp_clm_sewn_invariant` / `S_right_lp_clm_sewn_invariant`, non-commutativity witness `S_left_right_lp_clm_noncomm` on vacuum `canonicalCantorSewnState`, and infinite-dimensional boundary anomaly cancellations: paired summand zero `infinite_hilbert_paired_chiral_summand_zero`, $J$-fixed state expectation zero `infinite_hilbert_sewn_chiral_expectation_zero`, and $J$-paired series chiral index vanishing `infinite_hilbert_tsum_chiral_index_zero` | [ConcreteHilbertSewnAnomaly](lean/InfoGeometry/Canonical/ConcreteHilbertSewnAnomaly.lean) |
| Lattice OS transfer semigroup & mass gap | Euclidean transfer matrix $T(J) \in M_2(\mathbb{R})$ (`transferMat`, `transferMat_posDef`), spectral projector decomposition $P_0 + (\tanh J) P_1$ (`normTransferMat_pow`), positive spectral mass gap $\Delta(J) = -\log(\tanh J) > 0$ (`spectralMassGap_pos`), exponential clustering $(\tanh J)^L = e^{-L\Delta(J)} \to 0$ (`normTransferMat_pow_eq_exp_gap`, `normTransferMat_clustering_tendsto_zero`), Elitzur Wilson string expectation bridge (`expect_wilson_from_transferMat`), and transfer-matrix-weighted 2-slice Osterwalder–Schrader reflection positivity (non-trivial time-reflection involution `osReflect`, Boltzmann partition expectation `osExpectation`, `os_reflection_positivity` for $J > 0$, antiferromagnetic $J < 0$ failure `os_reflection_positivity_fails_antiferro`, Cauchy–Schwarz `os_cauchy_schwarz`, and $L$-step semigroup positivity `os_semigroup_reflection_positivity`). *Boundary*: Discrete/lattice gauge model; continuum 4D Yang–Mills $a \to 0$ remains open | [OsterwalderSchraderTransfer](lean/InfoGeometry/OperatorAlgebra/OsterwalderSchraderTransferSemigroupAndMassGap.lean) |
| Continuous $L^2([0,1])$ Cantor FUP | Normalized continuous trigonometric modes `modeSin`, `modeCos`, exact pointwise energy $s_n(x)^2 + c_n(x)^2 = 2$ (`mode_sq_sum_eq_two`), interval energy $2(b-a)$ (`interval_energy_mode_pair`), wavepacket Cauchy–Schwarz pointwise and interval bounds (`wavepacket_pointwise_cauchy_schwarz`, `wavepacket_interval_energy_bound`), multiscale Cantor contraction $((b-m)^2/b)^k \to 0$ for $b-m < \sqrt{b}$ (`cantor_fup_ratio_lt_one`, `continuous_cantor_wavepacket_contraction`, `continuous_cantor_fup_tendsto_zero`), and witness at $b=4, m=3$ (`continuous_cantor_witness_b4_m3`). *Boundary*: Continuous $L^2([0,1])$ mode packets; full $L^2(\mathbb{R})$ FUP remains open | [ContinuousL2CantorFUP](lean/InfoGeometry/Analysis/ContinuousL2CantorFourierUncertainty.lean) |
| Global $SO(5,5)$ & conformal 3-grading | Global Lie group $SO(5,5)$ (`IsSO55GroupMatrix`: $M^T J_{5,5} M = J_{5,5} \wedge \det M = 1$), group closure & Krein isometry (`isSO55_one`, `isSO55_mul`, `isSO55_isometry`), 1-parameter non-compact hyperbolic boost subgroup $\Lambda(\xi)$ (`so55Boost`, `so55Boost_add`, `so55Boost_isSO55`, `so55Boost_unbounded`), null quadric boundary invariance (`nullQuadric_invariant`), and conformal parabolic 3-grading $[D, P_k] = P_k$, $[D, K_k] = -K_k$, $P_k^3 = 0$ (`bracket_genD_genP`, `bracket_genD_genK`, `genP_nilpotent3`). *Boundary*: Finite-matrix $SO(5,5)$ and $\mathfrak{so}(5,5)$; infinite-dimensional curved-manifold CFT representations remain open | [SO55GlobalConformal](lean/InfoGeometry/Lie/SO55GlobalConformalPrecursors.lean) |
| Logarithmic integral $\mathrm{li}(x)$ & $\zeta$ pole | FTC calculus $\mathrm{li}'(x) = 1/\log x$ (`hasDerivAt_li`, `li_two`, `li_pos`), integration-by-parts expansion $\mathrm{li}(x) = x/\log x - 2/\log 2 + \int_2^x 1/(\log t)^2$ (`fundamental_li_by_parts`), two-sided remainder bounds (`li_sub_div_log_pos`, `li_le_linear_over_log_sq`), Chebyshev-to-$\mathrm{li}$ prime counting bound (`primeCounting_le_chebyshev_li`), and real-pole divergence $\lim_{\sigma \to 1^+} \mathrm{Re}(\zeta(\sigma)) = +\infty$ (`tendsto_riemannZeta_one_right_atTop`). *Boundary*: Precursor bounds; full asymptotic PNT and RH remain open | [RiemannZetaLiPrecursors](lean/InfoGeometry/Arithmetic/RiemannZetaLogarithmicIntegralPrecursors.lean) |

For a concrete example, `OperatorRPABlock.rpa_square` retains the full operator
commutator when squaring `[[a,b],[-b,-a]]`. Its off-diagonal square vanishes
exactly when `a` and `b` commute. The corresponding chiral square contains the
distinct ordered products `(a-b)*(a+b)` and `(a+b)*(a-b)`.

The [CAR/Krein/projectivization note](README-CURRENT.md) and
[nuclear operator synthesis](docs/NUCLEAR_OPERATOR_SYNTHESIS.md) give additional
topic-specific maps and qualifications.

## Proof and interpretation boundaries

A Lean theorem establishes its formal conclusion under its stated assumptions.
Distinguish a definition, a conditional theorem, a constructed witness, and a
proved equivalence. An assumed interface needs an inhabitant before it can
serve as a realized model. A generator family needs independence and spanning
theorems before it is called a basis.

The repository develops compatible finite-stage systems, algebraic direct
limits, and categorical colimits. The category, bonding maps, and universal
property must be identified for each construction. Analytic completions,
positivity, spectral lower bounds, and physical continuum interpretations need
their own stated structures and proofs. In particular, a general-ring identity
with an operator-valued coefficient is not by itself a scalar spectral-gap
theorem.

New accepted proofs must satisfy the repository's source, compilation, and
axiom-review requirements. A source scan for proof holes, a successful module
build, and a declaration-level axiom audit are separate forms of evidence.
Intentional linter fixtures and recovered historical proofs have separate
roles; a blanket zero-debt claim about every tracked file would obscure them.
The [dated audit](docs/DOCUMENTATION_SOURCE_AUDIT_2026-11-03.md) records the exact
scope of the observed source scan and baseline CI results.

## Build and verify

Use the toolchain in [lean-toolchain](lean-toolchain), the dependency revisions
in [lake-manifest.json](lake-manifest.json), and the targets in
[lakefile.lean](lakefile.lean). The reviewed baseline pins Lean 4.34.1.
The [getting-started guide](docs/GETTING_STARTED.md) explains local path
dependencies and preflight checks.

From the checkout root, after checking that no other compilation is active:

```bash
# Verify the Peirce bi-sandwich umbrella and transitively imported archetypes
python3 tools/infra/run_locked_lake_build.py \
  --wait-for-build-lock InfoGeometry.OperatorAlgebra.PeirceBiSandwich.All

# Verify the core library umbrella integrating all 7 foundational pillars
python3 tools/infra/run_locked_lake_build.py \
  --wait-for-build-lock InfoGeometry.Foundations.InfoGeometryCoreLibrary

# Compile an individual changed module incrementally with zero-warning enforcement
python3 tools/infra/run_locked_lake_build.py \
  --wait-for-build-lock --wfail InfoGeometry.OperatorAlgebra.PeirceBiSandwich.KMSBathAndAnisotropicKuboMori
```

Use `run_locked_lean.py` for individual file elaboration when inspecting compiler output directly. A no-target invocation of the
build wrapper selects changed-owner mode; use `--all-default-targets` when an
all-default-target build is intended. `InfoGeometry.Foundations.InfoGeometryCoreLibrary` and `InfoGeometry.OperatorAlgebra.PeirceBiSandwich.All` are umbrella targets: compiling them verifies the transitively imported active modules under the shared build lock, which is a scoped kernel check rather than an unconditional CI rebuild of every tracked historical file or fixture.

Preserve build caches and pinned dependencies. Never run `lake clean` or
delete `.lake` caches. See the [cache policy](WARNING_DO_NOT_RUN_CACHE.md) for
the existing wrapper's empty-cache hydration behavior and recovery boundaries.

## Graphs and optional research tooling

Declaration DAGs, LeanTrail, Arango queries, semantic retrieval, and symbolic
witnesses help locate owners and candidate comparisons. They do not replace
Lean proofs. Runtime endpoints, database selection, source revisions, and
ingestion freshness must be observed in the configured deployment.

The [canonical pipeline](docs/CANONICAL_AGENT_PIPELINE.md) distinguishes the
available Python commands from optional Pi, Hive, oracle, and Archon setup.
The [infra guide](tools/infra/README.md) describes the required local DAG
configuration. Historical graph counts are snapshots rather than current
repository invariants.

## Research history and use

This repository retains exploratory notes, historical reports, and proposed
mathematics alongside maintained source. Use the
[documentation map](docs/README.md) to distinguish their roles. The
[21 October 2026 research review](docs/reviews/2026-10-21-research-and-agent-accessibility.md)
is preserved as a historical assessment.

The maintainers do not provide technical support or commit to reviewing
unsolicited contributions. Readers are welcome to clone, fork, explore, and
develop their own extensions. Citation metadata is maintained in
[CITATION.cff](CITATION.cff).

## License

The repository is licensed under [Apache License 2.0](LICENSE).
