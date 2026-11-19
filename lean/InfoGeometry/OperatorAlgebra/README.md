# Operator algebra: owner map and scope

> **Source review:** 2026-11-15 at [abd5826b](https://github.com/nickgou-nuke/info-geometry-lean/tree/abd5826b3676fab6231c66b646ec1cc5aeed6732)
> plus scoped working-tree kernel verification of
> `InfoGeometry.Foundations.InfoGeometryCoreLibrary` and
> `InfoGeometry.OperatorAlgebra.PeirceBiSandwich.All`. This is a navigation map to the
> current declarations and their assumptions, not a whole-repository CI rebuild certification.
> Validation of the nilpotent-calculus additions is recorded separately in
> [their theorem contract](../../../docs/PEIRCE_NILPOTENT_COLIMIT_CONTRACT.md).

This directory contains Peirce and Lie–Jordan algebra, square-zero and CAR
constructions, native superoperators, matrix and Hilbert-space results,
algebraic limit transport, and several domain bridges. Start from the owner
of the required statement and inspect its carrier, hypotheses, imports, and
consumers. [All.lean](All.lean) and [PeirceBiSandwich/All.lean](PeirceBiSandwich/All.lean)
are import and synthesis umbrellas; importing two
families together does not prove a relationship between their carriers.
The repository search procedure is
[REPO_DEEP_SEARCH_PROTOCOL.md](../../../docs/REPO_DEEP_SEARCH_PROTOCOL.md),
and contributor instructions are in [AGENTS.md](../../../AGENTS.md).

## Main owner families

This table is a practical entry map, not an exhaustive theorem inventory.

| Family | Entry points and concrete owners | What to check before reusing a result |
|---|---|---|
| Peirce operator spine | [PeirceSpine.lean](PeirceSpine.lean), [Basic.lean](PeirceSpine/Basic.lean), [Tetraktys.lean](PeirceSpine/Tetraktys.lean), [CyclotomicBridge.lean](PeirceSpine/CyclotomicBridge.lean) | The base is an associative ring with `P*P = P` and corners `P*A*(1-P)`, `(1-P)*C*P`. Star, scalar, or normalization assumptions belong to the specific extension. The [archetype ledger](../../../docs/PEIRCE_OPERATOR_ARCHETYPES.md) records owners and corrected formulas. |
| Peirce bi-sandwich umbrella | [PeirceBiSandwich/All.lean](PeirceBiSandwich/All.lean) | Umbrella theorem `peirce_biSandwich_archetypes_synthesis` connecting core defects, custodial twin protection, KMS detailed balance, graded Clifford unrolling, unbounded resolvent flows, and lattice gauge projections. Carrier: generic associative rings with star, finite integer/real matrices, and polynomial evaluations. |
| Peirce bi-sandwich core primitives | [PeirceBiSandwich/Core.lean](PeirceBiSandwich/Core.lean) | Abstract associative ring $B$ with idempotent $P$ (`delta P = 0`). Defines defect $\delta(P) = P^2 - P$, $\tau(P)$, Casimir $V = N_+ N_- + N_- N_+$, quartet $(\Phi, J, V, \Sigma)$, and establishes algebraic dictionary `peirceBiSandwich_spine_dictionary`. |
| Pinched super-extension & Day localization | [PeirceBiSandwich/PinchedSuperExtension.lean](PeirceBiSandwich/PinchedSuperExtension.lean) | $M_8(\mathbb{Z})$ explicit operators $P_8, A_8, D_8, G_8$. Proves Day-convolution equivalence `DayRel`, on-shell Weyl reflection, parity-inverted fermionic supercharge, and integral unitary defect law `integral_unitary_defect_law`. |
| Clifford-8 BdG horizon & bi-Day algebra | [PeirceBiSandwich/Clifford8BdGHorizon.lean](PeirceBiSandwich/Clifford8BdGHorizon.lean) | Bi-graded Day convolution `BiDayRel`, horizon spin operators $J_{8,\text{spin}}, K_8, \Omega_8, H_{\text{hor}}$, Cayley conjugacy, and jump operator completeness. |
| Real supertwistor & polarized Fermi sea | [Supertwistor16AndRealBloch.lean](PeirceBiSandwich/Supertwistor16AndRealBloch.lean) | Kronecker lift $M_{16}(\mathbb{R}) \cong M_8(\mathbb{R}) \otimes M_2(\mathbb{R})$; real-rebit symmetric centralizer triviality `real_rebit_symmetric_centralizer_trivial`; polarized Fermi sea $P_{\mathrm{Fermi}}$; and pinched Gibbs state marginal. |
| Off-shell coercivity & colimit gap | [OffShellCoercivityAndColimitGap.lean](PeirceBiSandwich/OffShellCoercivityAndColimitGap.lean) | Integer scale-4 Klein Reynolds projector `kleinReynolds4`, scale-8 factored projection `factoredReynolds8`, off-shell coercivity, corner projection blindness, and operator Pythagorean identity `operator_pythagorean`. |
| KMS bath & anisotropic Kubo–Mori | [KMSBathAndAnisotropicKuboMori.lean](PeirceBiSandwich/KMSBathAndAnisotropicKuboMori.lean) | Inter-sector Kraus refeeding vanishing $L^T (Q_+ X Q_+) L = 0$ for $K_8, \Omega_8$; CPTP partial trace `partialTraceKKT` : $M_8(\mathbb{R}) \to M_2(\mathbb{R})$ via 4 isometric blocks; KMS detailed balance; dually flat spin cumulant $\ln(2\cosh\|\theta\|)$; anisotropic Kubo–Mori bounds $1 < \mathrm{artanh}(s)/s < 1/(1-s^2)$ (`artanh_deriv_and_anisotropic_kubo_mori_bounds`). |
| Custodial twin loop & Josephson lattice | [CustodialTwinLoopAndJosephsonLattice.lean](PeirceBiSandwich/CustodialTwinLoopAndJosephsonLattice.lean) | $\mathbb{Z}_2$ real freeze in $M_8(\mathbb{Z})$ ($D_1^T = D_1, D_2^T = -D_2$) vs. $U(1)$ BdG circle in $M_{16}(\mathbb{R})$ ($[G_{U(1)}, D_1] = 2 D_2$); custodial twin $W_{\mathrm{twin}} = \Phi + P_0$ ($W^2 = 1, W^T = W, [W, H_{\mathrm{hor}}] = 0, W D_1 W = -D_1$); all-loop polynomial odd-power vanishing `custodial_all_loop_odd_power_vanishing`; and 1-loop parity-odd birefringence. |
| KMS complete positivity & Kraus semigroup | [KMSCompletePositivityAndKrausSemigroup.lean](PeirceBiSandwich/KMSCompletePositivityAndKrausSemigroup.lean) | Full $k$-positivity of `partialTraceKKT` under arbitrary finite ancilla $\kappa$ (`partialTraceKKT_amplified_preserves_posSemidef`); 4-channel time-dependent Kraus decomposition of thermal semigroup; and generator-flow identity `gkslFlow_eq_thermalSemigroupC`. |
| Two-rebit bipartite separability vs Peirce defect | [BipartiteSeparabilityAndPeirceEntanglement.lean](PeirceBiSandwich/BipartiteSeparabilityAndPeirceEntanglement.lean) | Unit two-rebit pure states $\psi$; exact equivalence $\mathrm{IsProductState}(\psi) \leftrightarrow \det(C_\psi) = 0 \leftrightarrow \delta(\mathrm{Tr}_B(|\psi\rangle\langle\psi|)) = 0$ (`isProductState_iff_det_zero`, `isProductState_iff_idempotencyDefect_zero`); and separation from single-cut Peirce defect via product and Bell witnesses. |
| Tripotent unbounded resolvent flows | [TripotentUnboundedResolventFlow.lean](TripotentUnboundedResolventFlow.lean) | Resolvent and Cayley transform commute with tripotent $S$ ($S^3=S$) and preserve 5 grades `resolvent_and_cayley_commute_and_preserve_fiveGrades`; Kato–Trotter equivalence `unbounded_generator_commute_iff_resolvent_commute`; and $C_0$-group domain intertwining. |
| Hilbert $\ell^2$ unbounded generator witness | [UnboundedHilbertResolventAndC0GroupWitness.lean](UnboundedHilbertResolventAndC0GroupWitness.lean) | Hilbert space $H_{\ell^2} = \ell^2(\mathbb{N}, \mathbb{R})$; tripotent $S_{\ell^2}$; dense subspace $D_{\mathrm{fin}}$ and maximal graph domain $D_{\mathrm{max}}$; operator-norm unbounded skew-adjoint generator $K_{\mathrm{max}}$ with $\|K_{\mathrm{max}} e_{2m}\| = m+1$; contractive resolvent $R_{\mathrm{unb}}$; isometric group $U_{\mathrm{unb}}(t)$; non-trivial `ResolventData` and `C0GroupGenerator` instances (`unboundedResolventData`, `unboundedC0Group`). |
| Elitzur lattice gauge projection | [ElitzurLatticeGaugeProjection.lean](ElitzurLatticeGaugeProjection.lean) | Finite Haar–Reynolds Gibbs expectation invariance; Elitzur local gauge expectation vanishing for all couplings `elitzur_local_gauge_expectation_zero`; $\mathbb{Z}_2$ link-Higgs witness `z2_link_higgs_elitzur_vs_wilson_string`; and quantum representation average physical projection $P_{\mathrm{phys}}$. |
| $N$-link gauge chain & compact $U(1)$ Haar | [NLinkElitzurChainAndCompactU1Gauge.lean](NLinkElitzurChainAndCompactU1Gauge.lean) | $N$-link gauge-Higgs chain on $\mathbb{Z}_2$; exact local gauge vanishing for all vertices; closed-form length-$L$ Wilson string expectation $(\tanh J)^L$ with exponential mass-gap decay; and compact $U(1)$ Haar integral Elitzur vanishing for all non-zero charges $q \ne 0$ (`u1HaarAvg`). |
| Osterwalder–Schrader transfer semigroup & mass gap | [OsterwalderSchraderTransferSemigroupAndMassGap.lean](OsterwalderSchraderTransferSemigroupAndMassGap.lean) | Euclidean transfer matrix $T(J) \in M_2(\mathbb{R})$ (`transferMat`, `transferMat_posDef`), spectral projector decomposition $P_0 + (\tanh J) P_1$ (`normTransferMat_pow`), strictly positive spectral mass gap $\Delta(J) = -\log(\tanh J) > 0$ (`spectralMassGap_pos`), exponential clustering $(\tanh J)^L = e^{-L\Delta(J)} \to 0$ (`normTransferMat_pow_eq_exp_gap`), bridge to Elitzur Wilson string expectation (`expect_wilson_from_transferMat`), T16 non-commutativity (`transferMat_noncomm_witness`), and transfer-matrix-weighted 2-slice Osterwalder–Schrader reflection positivity (non-trivial time-reflection involution `osReflect`, Boltzmann partition expectation `osExpectation`, `os_reflection_positivity` for $J > 0$, antiferromagnetic $J < 0$ failure `os_reflection_positivity_fails_antiferro`, Cauchy–Schwarz `os_cauchy_schwarz`, and $L$-step semigroup positivity `os_semigroup_reflection_positivity`). *Boundary*: Discrete/lattice model; continuum 4D Yang–Mills $a \to 0$ remains open. |
| Quantum Kadison–Schwarz & Cramér–Rao | [KadisonSchwarzAndQuantumCramerRao.lean](KadisonSchwarzAndQuantumCramerRao.lean) | Kadison–Schwarz inequality $\Phi(A)^* \Phi(A) \le \Phi(A^* A)$ for positive unital maps; symmetric logarithmic derivative (SLD) inner product `quantumSLDInner`; and noncommutative quantum Cramér–Rao variance lower bound `quantumVariance`. |
| GNS representation & Petz monotone metrics | [GNSRepresentationAndPetzMonotoneMetrics.lean](GNSRepresentationAndPetzMonotoneMetrics.lean) | Positive functional on C*-algebra induces GNS Hilbert space representation `gnsRep` and cyclic vector `gnsCyclicVec`; classification of Petz monotone Riemannian metrics on matrix states. |
| Epistemic compiler Solve et Coagula poset | [SolveEtCoagulaPeirceAporiaPoset.lean](SolveEtCoagulaPeirceAporiaPoset.lean) | 5-stage causal compilation chain ($\mathcal{E}\mathcal{C}_1 \prec \dots \prec \mathcal{E}\mathcal{C}_5$); characteristic-free binary cut grading laws `binary_cut_idempotent_and_grading_laws`; fourfold relational Peirce anatomy & quiver multiplication; transcendent quartet $(\Phi, J, V, \Sigma)$ with universal creation lock; Socratic aporia $\delta(X) = X^2 - X$; infinite non-periodic orbit in $M_2(M_2(\mathbb{Z}))$; Newton–Peirce tower and `ClTowerColimit` transport; bounded acyclic causal poset `SolveEtCoagulaNode`. |
| Noncommutative Weyl–Cartan split & Iwasawa KAN | [NoncommutativeWeylCartanKANPolarEquivariance.lean](../Algebra/NoncommutativeWeylCartanKANPolarEquivariance.lean), [WeylTraceKANPolarEquivariance.lean](../Canonical/WeylTraceKANPolarEquivariance.lean) | Over arbitrary ring $B$, decomposes $2 \bullet M = M_{\mathrm{Weyl}} + M_{\mathrm{sym}}^0 + M_{\mathrm{antisym}}^0$; Plemelj–Newton trace-to-determinant identity; $K A N$ subgroup multiplication and polar Gram reduction; unitary/symmetry equivariance; $GL^+(2,\mathbb{R})$ closed-form KAN and polar factorizations with uniqueness and Frobenius Pythagorean orthogonality. |
| Schrödinger GKSL flow & ODE uniqueness | [SchrodingerGKSLFlowBridge.lean](../Modular/SchrodingerGKSLFlowBridge.lean) | Continuous linear generator `generatorCLM` and real endomorphism `generatorEnd`; bounded 1-parameter exponential flow `gkslFlow`; semigroup law `gkslFlow_add`; ODE orbit derivative `hasDerivAt_gkslFlow_orbit`; ODE solution uniqueness `gkslFlow_unique_of_ode`; and real-trace conservation `realTrace_gkslFlow`. Carrier: finite complex matrix algebra $M_n(\mathbb{C})$. Boundary: does not assert complete positivity or Kraus decomposition. |
| Off-diagonal Bloch-ball Umegaki & quantum Spohn | [BlochBallUmegakiAndQuantumSpohn.lean](../Modular/BlochBallUmegakiAndQuantumSpohn.lean) | Open Bloch ball in $M_2(\mathbb{C})$; spectral projector and continuous functional calculus `CFC.log`; Pythagorean decomposition $D_{\mathrm{Umegaki}}(\rho \| \rho_\theta) = (\phi(r) - \phi(z)) + D_\phi(z \| \eta_\theta)$ with strictly positive off-diagonal coherence divergence; forward Kolmogorov ODE; 3-channel KMS Spohn dissipation rate `operator_spohn_rate_and_strict_coherent_dissipation` $\sigma_{\mathrm{KMS}} \ge 0$; and global relaxation. |
| Hilbert-space sewn boundary anomaly cancellation | [ConcreteHilbertSewnAnomaly.lean](../Canonical/ConcreteHilbertSewnAnomaly.lean) | Completed Hilbert space $H_{\ell^2}(E) = \ell^2(\mathrm{BinaryCantorBoundary}, \mathrm{DoubledSpace}\,E)$; modular swap involution `J_lp_clm` and spectral involution `epsilon_lp_clm`; $Cl(1,1)$ anticommutation; Cuntz $O_2$ branch sewing invariance; and infinite-dimensional chiral anomaly cancellation `infinite_hilbert_paired_chiral_summand_zero` and `infinite_hilbert_sewn_chiral_expectation_zero`. |
| Lie–Jordan and dissipator identities | [LieJordanDuality.lean](LieJordanDuality.lean), [PeirceLieJordanResolution.lean](PeirceLieJordanResolution.lean), [PeirceDissipatorTrinity.lean](PeirceDissipatorTrinity.lean) | Ring identities and linear endomorphism identities have different interfaces. Reflexive-pair results add `uvu = u`, `vuv = v` to square-zero assumptions; do not infer them from arbitrary corners. |
| Square-zero spectral superoperators | [SquareZeroPairSpectral.lean](SquareZeroPairSpectral.lean), [InnerDerivationSpectra.lean](SquareZeroPairSpectral/InnerDerivationSpectra.lean), [KleinHadamard.lean](SquareZeroPairSpectral/KleinHadamard.lean) | The quadratic coupling `V = uv + vu` is operator-valued. Action formulas and homogenized projector identities retain their `V` factors; scalar eigenvalues, nonzero eigenvectors, or a positive gap need additional results. |
| Square-zero polynomial calculus | [SquareZeroPolynomial.lean](SquareZeroPolynomial.lean), [PolynomialTrace.lean](PeirceSpine/PolynomialTrace.lean) | Native `Polynomial.aeval` in a noncommutative algebra: Taylor truncation requires the base to commute with the direction, whereas a Peirce shear has the separate coefficient `F(1)-F(0)`. The exponential result uses Mathlib's finite `IsNilpotent.exp`. Graded polynomial traces retain exactly their constant coefficient. |
| Peirce superoperators and matrix Hodge kernels | [PeirceSuperoperators.lean](PeirceSuperoperators.lean), [HodgeKernel.lean](PeirceSuperoperators/HodgeKernel.lean), [DoubleCommutator.lean](PeirceSuperoperators/DoubleCommutator.lean) | The Hodge/energy statements use the full finite complex matrix carrier with its Hilbert–Schmidt structure. For example, the Jordan Gram kernel is characterized by simultaneous left/right annihilation; the paired double-commutator owner has its own common-kernel and positivity statements. |
| Opposite-corner coupling | [PeirceCoupling.lean](PeirceCoupling.lean), [Algebra.lean](PeirceCoupling/Algebra.lean), [GramGeometry.lean](PeirceCoupling/GramGeometry.lean), [PeirceCartanColimit.lean](PeirceCartanColimit.lean) | The algebraic starting point has independently chosen opposite corners. Trace, adjoint, Gram, reflection, and direct-limit results add their own assumptions; positivity is not a consequence of a bare ring identity. |
| CAR and Clifford–Dirac operators | [CliffordCAR.lean](CliffordCAR.lean), [CARFermionParity.lean](CARFermionParity.lean), [CliffordDirac.lean](CliffordDirac.lean), [CliffordDirac/Operators.lean](CliffordDirac/Operators.lean) | Keep the concrete CAR carrier distinct from an arbitrary Clifford–Dirac endomorphism algebra. The latter retains mixed commutator defects unless the theorem assumes their vanishing. CAR parity factors anticommute with the corresponding odd generators. |
| Tripotent grades, parity, and kernel restriction | [TripotentParity.lean](PeirceSpine/TripotentParity.lean), [TripotentChiralRestriction.lean](../Core/TripotentChiralRestriction.lean), [NuclearFiveGradeParity.lean](../Physics/NuclearFiveGradeParity.lean) | Grade regrouping is polynomial; grade signs require `T³ = T`. The chiral kernel equivalence additionally requires `ΓT = -TΓ` and `Γ² = 1`. Nuclear block invariance requires the specified grades (or their projectors). These are separate actions on named carriers. |
| Algebraic full-matrix limit transport | [LieJordanPeirceColimit.lean](LieJordanPeirceColimit.lean), [MatrixColimitTransport.lean](PeirceSpine/MatrixColimitTransport.lean), [Cl11TensorTowerLimit.lean](../Clifford/Cl11TensorTowerLimit.lean) | These use the actual stage maps of the algebraic matrix direct limit. An algebraic limit theorem does not by itself supply a norm completion, a state, or a continuum field theory. |
| Matrix restriction and nilpotent colimit calculus | [Cl11ConditionalExpectation.lean](../Canonical/Cl11ConditionalExpectation.lean), [TensorPolynomialTrace.lean](../Canonical/TensorPolynomialTrace.lean), [TensorNilpotentCalculus.lean](../Canonical/TensorNilpotentCalculus.lean) | The existing normalized partial trace is positive and bimodular, with explicit discarded nonzero matrix units. The existing limit trace supports polynomial cancellation and real Cauchy–Schwarz. Coherent idempotents seeded at scalar stage zero are necessarily trivial; use a positive-stage seed for nonzero corners. See the [theorem contract](../../../docs/PEIRCE_NILPOTENT_COLIMIT_CONTRACT.md). |
| Operator Dirichlet and resolvent formulas | [OperatorDirichlet.lean](OperatorDirichlet.lean), [SpineResolvent.lean](OperatorDirichlet/SpineResolvent.lean), [MatrixLegendre.lean](OperatorDirichlet/MatrixLegendre.lean) | Resolvent results state the needed unit/inverse hypotheses; the characteristic value may be the operator `V`. Cyclotomic and Dirichlet labels do not themselves imply analytic zeta-function statements. |
| Complex bounded operators and GNS models | [ComplexBoundedOperators.lean](ComplexBoundedOperators.lean), [HilbertBasisParseval.lean](ComplexBoundedOperators/HilbertBasisParseval.lean), [GNSFiniteSupport.lean](ComplexBoundedOperators/GNSFiniteSupport.lean) | The umbrella exposes Hilbert-basis/Parseval adapters. The finite-support GNS owner uses the commutative algebra `Fin n → ℂ` and an explicit active support; inspect the specific model before transferring a kernel or quotient claim to another carrier. |
| Jones optics and material response | [OperatorialJonesCalculus.lean](OperatorialJonesCalculus.lean), [SusceptibilityHessian.lean](SusceptibilityHessian.lean), [StatisticalChannels.lean](OperatorialJonesCalculus/StatisticalChannels.lean), [HessianResponse.lean](SusceptibilityHessian/HessianResponse.lean) | These include data interfaces as well as theorems. For example, `PolarizationChannel` supplies a channel field, while Hessian regularity is defined by bijectivity of a supplied response operator; a physical evolution law is not inferred from those fields. |
| Affine and Virasoro bridges | [AffineVirasoroBridge.lean](AffineVirasoroBridge.lean), [VirasoroProjectBridge.lean](VirasoroProjectBridge.lean) | The abstract datum supplies modes and a central element. Concrete realization and bracket theorems, including the conditional Heisenberg construction, are described below. |

## Cross-directory bridges

- **Graded Clifford superbase & entanglement rank**: [`../Clifford/Cl11SuperBaseAndEntanglementRank.lean`](../Clifford/Cl11SuperBaseAndEntanglementRank.lean) unrolls graded base superalgebras $(B, \theta_B)$ into matrix blocks, establishing the factorwise Koszul transpose law, cubic idempotent chains, braid permutations, and two-sided cut-rank bounds.
- **Modular GKSL & quantum Spohn thermodynamics**: [`../Modular/GKSLGibbsAndDuallyFlatSpinCumulants.lean`](../Modular/GKSLGibbsAndDuallyFlatSpinCumulants.lean), [`../Modular/WeldedBlochQuantumSpohnSynthesis.lean`](../Modular/WeldedBlochQuantumSpohnSynthesis.lean), [`../Modular/SchrodingerGKSLFlowBridge.lean`](../Modular/SchrodingerGKSLFlowBridge.lean) (mirrored at [`../../../src/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean`](../../../src/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean)), [`../Modular/BlochBallUmegakiAndQuantumSpohn.lean`](../Modular/BlochBallUmegakiAndQuantumSpohn.lean), and [`../Modular/AnisotropicBKMHessianAndMultiQubitSpohn.lean`](../Modular/AnisotropicBKMHessianAndMultiQubitSpohn.lean) formalize noncommutative division-free cyclic trace conservation, operator-valued exponential GKSL flow with ODE uniqueness, off-diagonal Bloch-ball Umegaki divergence with coherence pinching Pythagoras, forward-positivity monoids, and the anisotropic Bogoliubov–Kubo–Mori Hessian metric.
- **Inductive C*-algebra completion & multiscale Cantor FUP**: [`../Algebra/UHFColimitCStarCompletion.lean`](../Algebra/UHFColimitCStarCompletion.lean) constructs the unital $2^\infty$ UHF inductive limit with strict $L^2$ isometry and uniform completion `UHFCStar`; [`../Algebra/DiscreteCantorFourierUncertainty.lean`](../Algebra/DiscreteCantorFourierUncertainty.lean) establishes multiscale exponential contraction of the Fourier uncertainty operator on discrete Cantor sets; and [`../Analysis/ContinuousL2CantorFourierUncertainty.lean`](../Analysis/ContinuousL2CantorFourierUncertainty.lean) establishes continuous $L^2([0,1])$ mode-pair energy $s_n^2 + c_n^2 = 2$, wavepacket Cauchy–Schwarz bounds, and multiscale Cantor contraction $((b-m)^2/b)^k \to 0$ (witnessed at $b=4, m=3$).
- **Krein signature $(5,5)$, global $SO(5,5)$ & Iwasawa KAN / polar equivariance**: [`../Lie/Pin55NondegenerateKreinBridge.lean`](../Lie/Pin55NondegenerateKreinBridge.lean) proves strict nondegeneracy of the $(5,5)$ Krein bilinear form; [`../Lie/SO55GlobalConformalPrecursors.lean`](../Lie/SO55GlobalConformalPrecursors.lean) formalizes global $SO(5,5)$ group invariance, a 1-parameter non-compact hyperbolic boost subgroup $\Lambda(\xi)$, null quadric boundary invariance, and conformal parabolic 3-grading $[D, P_k] = P_k$, $[D, K_k] = -K_k$, $P_k^3 = 0$; [`../Algebra/NoncommutativeWeylCartanKANPolarEquivariance.lean`](../Algebra/NoncommutativeWeylCartanKANPolarEquivariance.lean), [`../Canonical/WeylTraceKANPolarEquivariance.lean`](../Canonical/WeylTraceKANPolarEquivariance.lean), [`../Algebra/WeylCartanKANPolarEquivariance.lean`](../Algebra/WeylCartanKANPolarEquivariance.lean), and [`../Algebra/ComplexSL2IwasawaAndHyperbolicPolar.lean`](../Algebra/ComplexSL2IwasawaAndHyperbolicPolar.lean) construct closed-form Iwasawa $K A N$ and polar factorizations with uniqueness, Frobenius Pythagorean orthogonality, and unitary/symmetry equivariance for general rings, $SL(2,\mathbb{R})$, $GL^+(2,\mathbb{R})$, $SL(2,\mathbb{C})$, and $GL(2,\mathbb{C})$.
- **Infinite-dimensional Hilbert sewn boundary anomaly cancellation**: [`../Canonical/ConcreteHilbertSewnAnomaly.lean`](../Canonical/ConcreteHilbertSewnAnomaly.lean) lifts the modular swap involution `J_lp_clm` and spectral involution `epsilon_lp_clm` to the completed Hilbert space $H_{\ell^2}(E) = \ell^2(\mathrm{BinaryCantorBoundary}, \mathrm{DoubledSpace}\,E)$, establishing $Cl(1,1)$ anticommutation, self-adjointness wrt the `lp` inner product, Cuntz $O_2$ branch sewing invariance, and exact boundary anomaly cancellations `infinite_hilbert_paired_chiral_summand_zero` and `infinite_hilbert_sewn_chiral_expectation_zero`.
- **Arithmetic prime counting, Hoeffding bounds & $\mathrm{li}(x)$ / $\zeta$ precursors**: [`../Arithmetic/ChebyshevPrimeAndHoeffdingBounds.lean`](../Arithmetic/ChebyshevPrimeAndHoeffdingBounds.lean) formalizes genuine Hoeffding tail certificates and constructive two-sided Erdős–Chebyshev prime-counting bounds $\Theta(n / \ln n)$, and [`../Arithmetic/RiemannZetaLogarithmicIntegralPrecursors.lean`](../Arithmetic/RiemannZetaLogarithmicIntegralPrecursors.lean) proves $\mathrm{li}'(x) = 1/\log x$, integration-by-parts expansion, Chebyshev-to-$\mathrm{li}$ prime bounds, and $\lim_{\sigma \to 1^+} \mathrm{Re}(\zeta(\sigma)) = +\infty$.
- **Penrose & 4D colimit–continuum constructive unification**: [`../Twistor/PenroseMinkowskiTetradDyadBridge.lean`](../Twistor/PenroseMinkowskiTetradDyadBridge.lean) unites Minkowski `(1,3)`, Newman–Penrose tetrads, Pauli soldering, Penrose–Onsager–Yang spinor dyads (`rankOneKernel`), and the closed-form Moore–Penrose vs. oblique twistor projector defect; [`PenroseConformalAndInflationColimitBridge.lean`](PenroseConformalAndInflationColimitBridge.lean) constructs the concrete $(5,5)$ Dirac `AeonConformalCrossover` and the `FibonacciK0`–Penrose Kite/Dart ring morphism into `Cl(5,5)` Bott colimits; and [`../Categorical/FourDimColimitContinuumSynthesis.lean`](../Categorical/FourDimColimitContinuumSynthesis.lean) unifies `Hom(colim, K) ≃ lim Hom(-, K)` duality, `BidirectionalRetractionSectionTower`, a $16^n$-site 4D dyadic refinement colimit (`Field4DContinuum`), Amplituhedron boundary retracts, Balaban coarse-graining, Zorn UHF monoidal colimits, and GNS Hilbert colimits.
- **Core library umbrella**: [`../Foundations/InfoGeometryCoreLibrary.lean`](../Foundations/InfoGeometryCoreLibrary.lean) unifies the foundational pillars, four research-frontier precursor modules (`OsterwalderSchraderTransferSemigroupAndMassGap`, `ContinuousL2CantorFourierUncertainty`, `SO55GlobalConformalPrecursors`, `RiemannZetaLogarithmicIntegralPrecursors`), and the three Wave 3 Penrose & 4D colimit–continuum unification owners with concrete realization witnesses.

## Peirce bi-sandwich suite, unbounded resolvent flows, and lattice gauge projections

### 1. Peirce bi-sandwich architecture
The Peirce bi-sandwich suite (`PeirceBiSandwich/*`) investigates algebraic invariants of an associative ring $B$ equipped with an idempotent $P$ ($P^2 = P$).
The primary defect operator is $\delta(X) = X^2 - X$, vanishing exactly when $X$ is idempotent (`delta_eq_zero_iff_isIdempotent`).
The Casimir coupling $V = N_+ N_- + N_- N_+$ couples opposite Peirce corners $N_+ = P A (1-P)$ and $N_- = (1-P) C P$.
In [Core.lean](PeirceBiSandwich/Core.lean), the transcendent quartet $(\Phi, J, V, \Sigma)$ is defined with $\Phi = N_+ + N_-$, $J = N_+ - N_-$, $\Sigma = P_0 V P_0$.
The universal unitary defect law proves $u_0^* u_0 - 1 = \delta(V)$ where $u_0 = 1 + \Phi$ in [PinchedSuperExtension.lean](PeirceBiSandwich/PinchedSuperExtension.lean).
In [OffShellCoercivityAndColimitGap.lean](PeirceBiSandwich/OffShellCoercivityAndColimitGap.lean), the operator Pythagorean identity establishes $(1 - V)^2 - 4 J^2 = (1 + V)^2$ (`operator_pythagorean`).
Finite-matrix realizations in $M_8(\mathbb{Z})$ and $M_{16}(\mathbb{R})$ instantiate explicit projectors $P_8$, jump operators $A_8, D_8$, and the BdG horizon operators $J_{8,\text{spin}}, K_8, \Omega_8, H_{\text{hor}}$.
In [Supertwistor16AndRealBloch.lean](PeirceBiSandwich/Supertwistor16AndRealBloch.lean), the real-rebit symmetric centralizer theorem proves that real symmetric operators commuting with $J_2$ are scalar multiples of the identity (`real_rebit_symmetric_centralizer_trivial`), forcing the necessity of the 16-dimensional Kronecker product $M_{16}(\mathbb{R}) \cong M_8(\mathbb{R}) \otimes M_2(\mathbb{R})$.
Thermalization is achieved in [KMSBathAndAnisotropicKuboMori.lean](PeirceBiSandwich/KMSBathAndAnisotropicKuboMori.lean) through CPTP partial trace $\mathrm{Tr}_{\mathrm{KKT}}$ with 4 isometric injection blocks, KMS detailed-balance GKSL relaxation, dually flat spin cumulants, and anisotropic Kubo–Mori bounds $1 < \mathrm{artanh}(s)/s < 1/(1-s^2)$ (`artanh_deriv_and_anisotropic_kubo_mori_bounds`).
Complete positivity is established in [KMSCompletePositivityAndKrausSemigroup.lean](PeirceBiSandwich/KMSCompletePositivityAndKrausSemigroup.lean) via amplified Kraus blocks `W_KKT` preserving positive semidefiniteness for arbitrary finite ancillas $\kappa$ (`partialTraceKKT_amplified_preserves_posSemidef`), together with a 4-channel time-dependent Kraus decomposition.
Custodial loop protection is proved in [CustodialTwinLoopAndJosephsonLattice.lean](PeirceBiSandwich/CustodialTwinLoopAndJosephsonLattice.lean), where the custodial twin involution $W_{\mathrm{twin}} = \Phi + P_0$ ($W^2 = 1, W D_1 W = -D_1$) guarantees all-loop polynomial odd-power vanishing `custodial_all_loop_odd_power_vanishing` for all polynomials $F, G \in \mathbb{R}[X]$.
Separation of tensor entanglement from single-cut Peirce defects is established in [BipartiteSeparabilityAndPeirceEntanglement.lean](PeirceBiSandwich/BipartiteSeparabilityAndPeirceEntanglement.lean): on two-rebit pure states $\psi$, product state separability is equivalent to determinant vanishing and to partial trace idempotency defect vanishing (`isProductState_iff_det_zero`, `isProductState_iff_idempotencyDefect_zero`).

### 2. Unbounded resolvent flows & Hilbert $\ell^2$ $C_0$-groups
In [TripotentUnboundedResolventFlow.lean](TripotentUnboundedResolventFlow.lean), the algebraic resolvent $R = (1 - K)^{-1}$ and Cayley transform $C = (1 + K)(1 - K)^{-1}$ commute with any tripotent $S$ ($S^3 = S$) commuting with $K$, preserving all five adjoint grading subspaces $\mathfrak{g}_{-2}, \mathfrak{g}_{-1}, \mathfrak{g}_0, \mathfrak{g}_1, \mathfrak{g}_2$ (`resolvent_and_cayley_commute_and_preserve_fiveGrades`).
The Kato–Trotter equivalence `unbounded_generator_commute_iff_resolvent_commute` proves that an unbounded generator on a dense domain commutes with $S$ if and only if its bounded resolvent commutes with $S$.
In [UnboundedHilbertResolventAndC0GroupWitness.lean](UnboundedHilbertResolventAndC0GroupWitness.lean), this abstract structure is instantiated on the infinite-dimensional real Hilbert space $H_{\ell^2} = \ell^2(\mathbb{N}, \mathbb{R})$.
A tripotent operator $S_{\ell^2}$ is constructed by alternating signs on consecutive pairs $(2m, 2m+1)$.
The dense subspace of finitely supported sequences $D_{\mathrm{fin}}$ and the maximal graph domain $D_{\mathrm{max}} = \{x \in \ell^2 \mid K x \in \ell^2\}$ are defined.
The skew-symmetric generator $K_{\mathrm{max}}$ satisfies $\|K_{\mathrm{max}} e_{2m}\| = m + 1$, proving operator-norm unboundedness on $D_{\mathrm{max}}$.
Contractive resolvent operators $R_{\mathrm{unb}}$ ($\|R_{\mathrm{unb}} x\| \le \|x\|$) and isometric one-parameter groups $U_{\mathrm{unb}}(t)$ ($\|U_{\mathrm{unb}}(t) x\| = \|x\|$) are constructed, providing genuine non-trivial inhabitants `unboundedResolventData` and `unboundedC0Group` satisfying domain intertwining and 5-grade invariance.

### 3. Lattice gauge projections & Elitzur's theorem
In [ElitzurLatticeGaugeProjection.lean](ElitzurLatticeGaugeProjection.lean), local gauge symmetry is formalized for finite groups $G$ acting on configuration spaces.
The Haar–Reynolds average preserves Gibbs expectations for all gauge-invariant Hamiltonians.
Elitzur's theorem `elitzur_local_gauge_expectation_zero` proves that the expectation of any non-trivial gauge-variant local observable vanishes identically at all temperatures and couplings.
On a 2-site $\mathbb{Z}_2$ link-Higgs model, the bare matter expectation vanishes $\langle \sigma_0 \rangle = 0$, while the gauge-invariant Wilson string is strictly positive $\langle \sigma_0 U_{01} \sigma_1 \rangle = \tanh J > 0$ for $J > 0$ (`z2_link_higgs_elitzur_vs_wilson_string`).
The quantum physical projection $P_{\mathrm{phys}}$ onto gauge-invariant vectors is constructed via `Representation.averageMap`.
In [NLinkElitzurChainAndCompactU1Gauge.lean](NLinkElitzurChainAndCompactU1Gauge.lean), this is generalized to an $N$-link chain with local $\mathbb{Z}_2$ vertex gauge transformations.
Exact local gauge expectation vanishing is proved for all single-spin and two-point spin observables at distinct vertices.
The open Wilson-dressed string of length $L \le N$ is evaluated in closed form as $\mathbb{E}[W_{0,L}] = (\tanh J)^L$, exhibiting strict positivity for $J > 0$ and exponential mass-gap decay $(\tanh J)^L \to 0$ as $L \to \infty$.
Continuous compact $U(1)$ gauge invariance is formalized via interval Haar integration `u1HaarAvg`, proving that character expectations vanish for all non-zero integer charges $q \ne 0$.

### 4. Epistemic compiler Solve et Coagula causal poset
In [SolveEtCoagulaPeirceAporiaPoset.lean](SolveEtCoagulaPeirceAporiaPoset.lean), the 5-stage causal compilation chain ($\mathcal{E}\mathcal{C}_1 \prec \dots \prec \mathcal{E}\mathcal{C}_5$) is formalized:
- **$\mathcal{E}\mathcal{C}_1$ (Binary Cut)**: For any ring idempotent $P^2=P$, $Q = 1-P$ and $S = 2P-1$ satisfy $S^2 = 1$; the commutator $[P, X]$ vanishes if and only if both off-diagonal corners vanish (`binary_cut_commute_iff_corners_zero`), with explicit $M_2(\mathbb{Z})$ non-commutativity witness `cutMat2 * probeMat2 ≠ probeMat2 * cutMat2`.
- **$\mathcal{E}\mathcal{C}_2$ (Peirce Anatomy & Quiver)**: Direct sum decomposition $X = X_{11} + X_{10} + X_{01} + X_{00}$ is unique (`peirce_fourfold_direct_sum_unique`), and the quiver multiplication table preserves corner relations with strict order asymmetry.
- **$\mathcal{E}\mathcal{C}_3$ (Transcendent Quartet & Creation Lock)**: The quartet $(\Phi, J, V, \Sigma)$ satisfies $[J, \Phi] = 2\Sigma$, $\{J, \Phi\} = 0$, $\Phi^2 = V$, $J^2 = -V$; universal creation lock proves $V = 0 \leftrightarrow \Sigma = 0 \leftrightarrow N_+ N_- = 0 \land N_- N_+ = 0$; Bruhat tilt produces tilted idempotents with zero Maurer–Cartan Bianchi curvature.
- **$\mathcal{E}\mathcal{C}_4$ (Socratic Aporia & Newton–Peirce Tower)**: The idempotency defect $\delta(X) = X^2 - X$ applied to $P + \Phi$ yields $V$; under iteration, an infinite non-periodic orbit is constructed in $M_2(M_2(\mathbb{Z}))$ with strictly monotonic eigenvalues $a_{n+1} = a_n^2 - a_n \ge 4$; transport into Clifford towers and colimits preserves defect iterations.
- **$\mathcal{E}\mathcal{C}_5$ (Causal Poset & Master Synthesis)**: Acyclic causal poset `SolveEtCoagulaNode` with strict rank monotonicity and master synthesis theorem `master_solve_et_coagula_noncommutative_synthesis`.

### 5. Noncommutative Weyl–Cartan split, Iwasawa KAN & polar equivariance
In [`../Algebra/NoncommutativeWeylCartanKANPolarEquivariance.lean`](../Algebra/NoncommutativeWeylCartanKANPolarEquivariance.lean) and [`../Canonical/WeylTraceKANPolarEquivariance.lean`](../Canonical/WeylTraceKANPolarEquivariance.lean), the 4-stage poset $(\mathcal{K}\mathcal{P}, \preceq)$ formalizes:
- **$\mathcal{K}\mathcal{P}_1$ (Noncommutative Trace-to-Determinant & Cartan Split)**: For any $M \in M_2(B)$ over a ring $B$, the decomposition $2 \bullet M = M_{\mathrm{Weyl}} + M_{\mathrm{sym}}^0 + M_{\mathrm{antisym}}^0$ holds with traceless symmetric and skew parts, Lie brackets $[\gamma_1, \sigma] = -2\omega$, $[\omega, \gamma_1] = 2\sigma$, $[\omega, \sigma] = -2\gamma_1$, and Plemelj–Newton identity $(\operatorname{Tr} M)^2 - \operatorname{Tr}(M^2) = \mathrm{symDet}(M)$ (`weyl_cartan_split_and_noncommutative_trace_to_det`). Central scalar embeddings are characterized by $a \in Z(B)$ (`fiberEmbed_central_iff`) with a non-central witness in $M_2(M_2(\mathbb{Z}))$ (`weylScalePart_noncentral_witness`).
- **$\mathcal{K}\mathcal{P}_2$ (Iwasawa $K A N$ Subgroups & Polar Gram Reduction)**: Subgroup multiplication laws bridge to `IwasawaKANTriad`, and Polar Gram reduction $M^\dagger M = (A N)^\dagger (A N)$ eliminates unitary $K$, recovering noncommutative Schur complements $(M^\dagger M)_{11} - n^\star (M^\dagger M)_{00} n = a_-^\star a_-$ (`iwasawa_kan_subgroups_and_polar_gram_reduction`).
- **$\mathcal{K}\mathcal{P}_3$ (Unitary Equivariance of Polar Decomposition)**: Over any $\star$-ring $R$, unitary conjugation $M_G = G M G^{-1} = U_G P_G$ preserves $U_G^\star U_G = 1$, $P_G^\star = P_G$, and $M_G^\star M_G = P_G^2$ (`polar_decomposition_unitary_equivariance`).
- **$\mathcal{K}\mathcal{P}_4$ (KAN Symmetry Equivariance)**: Conformal equivariance of $K, A, N$ under diagonal scaling, fiber gauge, chirality parity, and Weyl reflection (`iwasawa_kan_symmetry_equivariance`).
- **$GL^+(2, \mathbb{R})$ Factorization, Uniqueness & Frobenius Geometry**: In `WeylTraceKANPolarEquivariance.lean`, closed-form factorizations and uniqueness are established for Iwasawa $K A N$ (`real_gl2_pos_iwasawa_factorization`, `real_gl2_pos_kan_unique`) and polar decomposition $M = K P$ (`real_gl2_pos_polar_factorization`, `real_gl2_pos_polar_unique`) for $\det M > 0$. Pairwise Frobenius orthogonality (`real_weyl_cartan_frobenius_orthogonality`) yields the Pythagorean norm split $\|M\|_F^2 = \|M_{\mathrm{scalar}}\|_F^2 + \|M_{\mathrm{sym}}^0\|_F^2 + \|M_{\mathrm{skew}}\|_F^2$ (`real_weyl_cartan_frobenius_pythagorean`). Orthogonal conjugation equivariance holds (`real_gl2_pos_polar_conjugation_equivariance`), but general $GL(2, \mathbb{R})$ conjugation fails equivariance (`real_gl2_euclidean_polar_not_equivariant_under_general_conjugation`).

### 6. Schrödinger GKSL flow, off-diagonal Bloch-ball Umegaki & quantum Spohn dissipation
In [`../Modular/SchrodingerGKSLFlowBridge.lean`](../Modular/SchrodingerGKSLFlowBridge.lean) (mirrored in `src/`) and [`../Modular/BlochBallUmegakiAndQuantumSpohn.lean`](../Modular/BlochBallUmegakiAndQuantumSpohn.lean):
- **Finite-Matrix Schrödinger GKSL Flow**: On $M_n(\mathbb{C})$, the generator continuous linear map `generatorCLM` and real endomorphism `generatorEnd` define the bounded exponential flow `gkslFlow`. Proves 1-parameter semigroup law `gkslFlow_add`, orbit ODE `hasDerivAt_gkslFlow_orbit`, ODE uniqueness `gkslFlow_unique_of_ode`, and real trace preservation `realTrace_gkslFlow`.
- **$\mathcal{G}_8$ Two-Sheet Spectral Projector & `CFC.log`**: For self-adjoint unit-trace states $\rho \in M_2(\mathbb{C})$ in the open Bloch ball ($r < 1$), constructs star projection $P$, proves strict positivity `IsStrictlyPositive ρ`, and evaluates continuous functional calculus `CFC.log ρ` (`spectralProjector_twoSheet_and_cfc_log`).
- **$\mathcal{G}_9$ Umegaki Coherence Pinching Pythagoras**: Evaluates $D_{\mathrm{Umegaki}}(\rho \| \rho_\theta) := \operatorname{Re}\operatorname{Tr}(\mathrm{umegakiKernel}\,\rho\,\rho_\theta)$ and proves the Pythagorean decomposition $D_{\mathrm{Umegaki}}(\rho \| \rho_\theta) = (\phi(r) - \phi(z)) + D_\phi(z \| \eta_\theta)$ (`umegakiKernel_trace_and_coherence_pythagoras`), with strictly positive off-diagonal coherence divergence $\phi(r) - \phi(z) \ge 0$ vanishing iff $\rho_{01} = 0$, and faithfulness.
- **$\mathcal{G}_{10}$ Kolmogorov Forward ODE, KMS Spohn Dissipation & Relaxation**: Proves entrywise ODE `hasDerivAt_thermalSemigroupC_eq_lindbladian`, open-Bloch-ball forward preservation for $t \ge 0$ (`thermalSemigroupC_preserves_blochBall`), forward-positivity monoid requiring $t \ge 0$ (`forward_monoid_positivity_iff_and_backward_aporia`), 3-channel KMS operator Spohn dissipation rate $\sigma_{\mathrm{KMS}}(\gamma, \theta, \sigma) \ge 0$ (`operator_spohn_rate_and_strict_coherent_dissipation`) with strictly positive dissipation whenever $\sigma_{01} \ne 0$, full-matrix Spohn derivative identity $\frac{d}{dt} D_{\mathrm{Umegaki}}(T_t(\rho) \| \rho_\theta) = -\sigma_{\mathrm{KMS}}(T_t(\rho))$, and global asymptotic relaxation to Gibbs density $\rho_\theta$ (`master_bloch_umegaki_spohn_and_gibbs_relaxation`).

### 7. Infinite-dimensional Hilbert sewn boundary anomaly cancellation on $H_{\ell^2}$
In [`../Canonical/ConcreteHilbertSewnAnomaly.lean`](../Canonical/ConcreteHilbertSewnAnomaly.lean):
- Lifts the modular swap involution `modular_j` and spectral involution `spectral_epsilon` from the fiber `DoubledSpace E := WithLp 2 (E × E)` onto the completed binary Cantor Hilbert boundary carrier $H_{\ell^2}(E) := \ell^2(\mathrm{BinaryCantorBoundary}, \mathrm{DoubledSpace}\,E)$.
- Constructs continuous linear maps `J_lp_clm` and `epsilon_lp_clm`, proving isometries `J_lp_clm_isometry`, `epsilon_lp_clm_isometry`, involutions `J_lp_clm_comp_self`, `epsilon_lp_clm_comp_self`, and $Cl(1,1)$ anticommutation `J_lp_clm_anticomm_epsilon_lp_clm` ($J \epsilon = -\epsilon J$) with `J_lp_clm_comp_epsilon_lp_clm = K_lp_clm`.
- Proves self-adjointness `inner_J_lp_clm_selfAdjoint` wrt Mathlib's `lp.instInnerProductSpace`.
- Proves Cuntz $O_2$ branch sewing invariance `S_left_lp_clm_sewn_invariant` and `S_right_lp_clm_sewn_invariant` ($J S_i J = S_i$), together with Cuntz noncommutativity `S_left_right_lp_clm_noncomm` on $H_{\ell^2}(\mathbb{R})$.
- Constructs canonical non-zero sewn vacuum state `canonicalCantorSewnState` ($J \psi_{\mathrm{sewn}} = \psi_{\mathrm{sewn}}$).
- Proves infinite-dimensional boundary anomaly cancellation theorems:
  * Paired chiral expectation cancellation: $\langle v, \epsilon B v \rangle + \langle J v, \epsilon B (J v) \rangle = 0$ (`infinite_hilbert_paired_chiral_summand_zero`) for every $J$-sewn bounded operator $B$ ($J B J = B$).
  * Chiral expectation vanishing: $\langle \psi, \epsilon B \psi \rangle = 0$ (`infinite_hilbert_sewn_chiral_expectation_zero`) on every $J$-fixed state $\psi$.
  * Infinite-series chiral index vanishing: $\sum_{i \in \iota} \langle e_i, \epsilon B e_i \rangle = 0$ (`infinite_hilbert_tsum_chiral_index_zero`) for every $J$-paired family $(e_i)_{i \in \iota}$ with summable diagonal expectation.
  * Concrete non-zero sewn Cantor vacuum chiral expectation vanishing: `canonicalCantorSewnState_chiral_zero`.

## Reversible gates and native differentiation

[ReversibleGateVariation.lean](PeirceSpine/ReversibleGateVariation.lean) reuses
the ordered shear `epistemicCornerShear P A C = (1+conePlus P A)*(1+coneMinus P C)`
and its reverse-ordered inverse. It proves midpoint/input reconstruction,
the exact right-trivialized parameter variation, and the output-coordinate
tangent formula in an arbitrary associative ring. The finite-update formula
retains the mixed quadratic remainder. A separate finite-list theorem shows
that words using only one fixed upper corner depend on the sum of their
parameters and cannot distinguish permutations.
An explicit construction in native `Units` specializes nested-word reduction
to the actual mixed-corner shear and its polynomial inverse.

[PeirceReversibleDifferential.lean](../Analysis/PeirceReversibleDifferential.lean)
constructs the full continuous linear differential in the independent
parameters `(A,C,x)` and proves native `HasFDerivAt` / `fderiv` statements.
[PeirceReversibleMatrixPullback.lean](../Analysis/PeirceReversibleMatrixPullback.lean)
proves the cotangent pullback on full finite complex matrices, differentiated
over the reals, using the existing positive definite real trace pairing.
The projector is fixed and self-adjoint. The file includes a scalar-loss
chain rule and a concrete half trace-square loss.

[NestedGroupWords.lean](../Algebra/NestedGroupWords.lean) constructs labeled
words from native binary trees, identifies their erasure with Mathlib Dyck
words, and proves reduction to the empty word before evaluating in an
arbitrary group. It also proves that balanced-word evaluation is not an
injective encoding of trees when a label exists.
[ZornTripleContraction.lean](../Canonical/ZornTripleContraction.lean) proves
the precisely bracketed upper-sector triple anticommutator with a native
`Matrix.det` coefficient using the existing full nonassociative split-octonion
product. Its carrier is distinct from the associative gate algebra.

The [theorem contract](../../../docs/PEIRCE_REVERSIBLE_DIFFERENTIAL_CONTRACT.md)
records the source, assumptions and validation scope. These results do not
construct a Yangian RTT algebra or supply an algorithmic memory bound.

## Reading algebraic and spectral claims

### Ordered resolvent transforms

[ResolventTransform.lean](ResolventTransform.lean) proves the unit-domain
equivalence for `1-A*C` and `1-C*A`, inverse intertwining, and the exact finite
difference and quadratic remainder of `eta C A = Ring.inverse (1-A*C) * A` in
an arbitrary associative ring.
[PeirceSpine/Resolvent.lean](PeirceSpine/Resolvent.lean) supplies the corrected
two-corner conjugation, chart commutator, and full/corner inverse-sandwich
identities for arbitrary Peirce variations.

The native analytic derivatives live in
[ResolventTransformDifferential.lean](../Analysis/ResolventTransformDifferential.lean)
and [PeirceResolventDifferential.lean](../Analysis/PeirceResolventDifferential.lean).
They use `HasFDerivAt` on a complete real normed algebra, keep the lower
coordinate fixed, and preserve noncommutative multiplication order. The
[theorem contract](../../../docs/PEIRCE_RESOLVENT_DIFFERENTIAL_CONTRACT.md)
records the exact inverse hypotheses and the additional obligations behind
the proposed metric, Berezinian, and supermanifold interpretations.

### Polynomial and spectral interpretations

For the Peirce pair, `genV = N₊*N₋ + N₋*N₊` belongs to the same operator
ring as the generators. In particular, a formula `D(J) = -4 • (genV * J)`
keeps an ordered operator product. It supplies a scalar eigenvalue only after
an additional theorem identifies multiplication by `genV` with the required
scalar action on a specified nonzero element. A physical gap additionally
needs a stated operator, representation, spectrum, and lower-bound theorem.

Likewise, [CyclotomicBridge.lean](PeirceSpine/CyclotomicBridge.lean) proves
A58–A60 as polynomial identities for an idempotent in an arbitrary ring.
The A58/A59 root-of-unity and group relations specialize on the unit shell
`genV P A C = 1`; the general formulas retain the defect and coupling factors.
A60 uses `s3Refl1 - s3Refl2 = -genJ - 2 • genSig` and the negative
`-16 • ((genV * genV) * genSig)` tomography term. These polynomial identities
do not alone prove a faithful group realization.

The `peirce_nf hP` macro in [Basic.lean](PeirceSpine/Basic.lean) combines a
selected `simp only` rewrite set with `abel`. Callers supply the definitions
to unfold beyond that set. Successful use proves the individual goal; a
claim that it decides every ring identity, or that a proposed Knuth–Bendix
completion is complete, would require a separately stated metatheorem.

## Ordered Peirce words and unitary balance

[WilsonPlaquette.lean](PeirceSpine/WilsonPlaquette.lean) owns the exact
four-factor expansion `W = 1 + Sigma - V*J + Qplus^2`.
[WilsonPlaquetteCriteria.lean](PeirceSpine/WilsonPlaquetteCriteria.lean)
characterizes `W=1` by vanishing of both mixed products and `W=1+Sigma`
by vanishing of both directed cubic round trips. These are arbitrary-ring
results with an idempotent cut; the higher terms cannot be discarded merely
because each individual corner is square-zero.

[SquareZeroUnitary.lean](SquareZeroUnitary.lean) proves that a square-zero
perturbation `1+N` in a C*-ring is unitary exactly when `N=0`. Its analytic
corollary uses the actual complex Banach-algebra exponential. A unitary
left factor preserves this obstruction without a commutation hypothesis.

The [conformal-balance theorem contract](../../../docs/CONFORMAL_BALANCE_OBSTRUCTION_CONTRACT.md)
records the source claims, existing owners, exact hypotheses, and verification
scope. These operator theorems do not construct Connes fusion or identify a
Peirce word with categorical double braiding. Non-rationality of a unitary
conformal net does not supply a nontrivial unitary Jordan perturbation.

## Virasoro bridge details and reusable notes

[AffineVirasoroBridge.lean](AffineVirasoroBridge.lean) defines `VirasoroDatum`
as modes and a central element. Its bracket/centrality projection lemmas take
the relevant laws as explicit hypotheses. The concrete
[VirasoroProjectBridge.lean](VirasoroProjectBridge.lean) connects this datum to
the imported [VirasoroAlgebra implementation](../External/Virasoro/VirasoroAlgebra.lean):

- `VirasoroProjectRealizes` identifies the witness's modes and central element
  with the concrete generators. `virasoro_project_has_realized_datum` proves
  existence of that specified witness; `virasoro_project_is_certified` is a
  compatibility theorem name for the same proposition, not a CI status.
- `virasoroProjectVirasoroDatum_central_commutes` and
  `virasoroProjectVirasoroDatum_bracket` prove the concrete bracket laws.
- `heisenbergSugawaraDatum` sets `level = 1`, `dimG = 1`, `hDual = 0`, and
  `centralCharge = 1`; `heisenbergSugawaraDatum_sugawara` verifies the scalar
  central-charge formula for that calibration.
- The stronger `currentHeisenbergVirasoroDatum_bracket` constructs the
  endomorphism-valued Virasoro bracket from a supplied `CurrentHeisenbergRep ℝ V`,
  via [CurrentSugawaraBridge.lean](../Canonical/CurrentSugawaraBridge.lean).
  Retain that representation hypothesis when describing the result.

Two proof-engineering notes from the earlier bridge README remain useful:

1. **Central-term scaling.** When a goal differs by whether scalar
   multiplication sits inside an `if`, try `rw [← smul_ite_zero]` or
   `simp only [smul_ite, smul_zero]`. Compare the actual normalized bracket
   formula first; the current concrete proof also splits on `m + n = 0`.
2. **A witness must identify its implementation.** Follow the concrete
   `VirasoroProjectRealizes` pattern rather than replacing a realization
   statement by a vacuous existential such as `∃ D, True`.

## Validation records

Report build results with the revision, exact targets, command, and outcome.
The former `CERTIFIED`/`STABLE` table is replaced by the theorem-level source
map above because a historical label does not establish a present build.
Follow the root [AGENTS.md](../../../AGENTS.md) for locked build commands and
the scope of proof-hygiene checks. A documentation edit or a source scan does
not substitute for compiling a named target and, when required, inspecting
its declaration axioms.
