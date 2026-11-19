# Open Debt Problems — Exhaustive Deep-Search Audit

> **Historical audit date**: 2026-07-24
> **Source review**: 2026-11-15 against `abd5826b3676fab6231c66b646ec1cc5aeed6732` plus scoped working-tree kernel verification of `InfoGeometry.Foundations.InfoGeometryCoreLibrary` and `InfoGeometry.OperatorAlgebra.PeirceBiSandwich.All` (this scoped check covers the named targets and is not a whole-repository CI rebuild).
> **Current status**: Historical debt note updated against present owners. Sections 2.A through 2.F are constructively closed by kernel-verified modules; active open mathematical and document frontiers are explicitly delimited in Section 4.

This document is a historical debt note, not an exhaustive current audit. Names and status below are corrected only for the inspected owner files; no repository-wide gap count is asserted.

---

## 1. Closed Sectors (100% Proved / Verifiable)

The following sectors have been fully solved, with all stubs and `sorry` keywords eliminated in favor of genuine proofs checked by the Lean 4 kernel:

| Sector | Description / Notes |
| :--- | :--- |
| **Gell-Mann Basis** | Fully proved Gell-Mann basis matrix product tables, trace identities, and commutator properties in `SU3GellMannLieAlgebra.lean`. |
| **Cuntz-Fibonacci** | Fully proved the Cuntz-Fibonacci Five Hypotheses in `CuntzFibonacciFiveHypotheses.lean`, verifying representation, shift commutativity, and braid non-commutativity. |
| **Grover Bound** | Proved Grover optimal success probability lower bound using real analysis mono bounds. |
| **Golden Mean Shift** | All stubs (`X_root`, `braid_flow_noncomm`, `subalgebra_isomorphic_to_golden_quotient`) have been fully proved or resolved in the live codebase and synchronized in the sandbox. |
| **Chevalley Spinors** | Fully proved the coordinate-free Chevalley spinor representation machinery natively in `ChevalleySpinorBlueprint.lean` with exactly zero axioms and zero sorries, using Mathlib's `contractLeft` and `ι` maps. |
| **Chebyshev Prime & Hoeffding Bounds** | Constructively closed formerly open debt in `GenuineBounds.lean` via [`ChebyshevPrimeAndHoeffdingBounds.lean`](../lean/InfoGeometry/Arithmetic/ChebyshevPrimeAndHoeffdingBounds.lean): proved Hoeffding's Bernoulli lemma, binomial tail Chernoff bound, certificate beating trivial cardinality, and constructive two-sided Erdős–Chebyshev $\Theta(n / \log n)$ prime-counting bounds. |
| **Nondegenerate $Pin(5,5)$ Krein Bridge** | Constructively closed formerly open debt in `Pin55KreinConformalBridge.lean` via [`Pin55NondegenerateKreinBridge.lean`](../lean/InfoGeometry/Lie/Pin55NondegenerateKreinBridge.lean): proved canonical signature $(5,5)$ matrix $J_{5,5}$, strict nondegeneracy of `kreinForm55`, positive/negative definite 5D sectors, 5D isotropic Witt subspace, and $\mathfrak{so}(5,5)$ Lie algebra invariance with non-commuting generators. |
| **Infinite-Dimensional Hilbert Sewn Boundary Anomaly Cancellation** | Constructively closed boundary anomaly cancellation and Krein deficit via [`ConcreteHilbertSewnAnomaly.lean`](../lean/InfoGeometry/Canonical/ConcreteHilbertSewnAnomaly.lean): proved infinite-dimensional $H_{\ell_2}$ binary Cantor boundary carrier, lifted modular swap $J_{\ell_2}$ and chiral symmetry $\varepsilon_{\ell_2}$ with $\mathrm{Cl}(1,1)$ anticommutation $J \circ \varepsilon = -(\varepsilon \circ J)$, self-adjointness, non-commuting Cuntz $O_2$ branch sewing invariance ($J \circ S_i \circ J = S_i$), and complete boundary anomaly cancellation $\langle v, \varepsilon(B v) \rangle + \langle J v, \varepsilon(B(J v)) \rangle = 0$ for all $J$-sewn bounded operators $B$, with $\langle \psi, \varepsilon(B \psi) \rangle = 0$ for $J$-fixed states. |
| **Noncommutative Weyl–Cartan Split & Iwasawa $K A N$ / Polar Equivariance** | Constructively closed across [`NoncommutativeWeylCartanKANPolarEquivariance.lean`](../lean/InfoGeometry/Algebra/NoncommutativeWeylCartanKANPolarEquivariance.lean) and [`WeylTraceKANPolarEquivariance.lean`](../lean/InfoGeometry/Canonical/WeylTraceKANPolarEquivariance.lean): proved arbitrary-ring 2-sheet Cartan decomposition $2 \bullet M = M_{\mathrm{Weyl}} + M_{\mathrm{sym}}^0 + M_{\mathrm{antisym}}^0$, Plemelj–Newton trace-to-determinant identity, Iwasawa $K, A, N$ subgroup multiplication, polar Gram reduction eliminating unitary $K$, Schur complement recovery, 4-way $K A N$ conjugation equivariance, and on $GL^+(2, \mathbb{R})$ global existence and uniqueness of $K A N$ and polar factorizations. |
| **Off-Diagonal Bloch-Ball Umegaki Relative Entropy & Quantum Spohn Dissipation** | Constructively closed in [`BlochBallUmegakiAndQuantumSpohn.lean`](../lean/InfoGeometry/Modular/BlochBallUmegakiAndQuantumSpohn.lean): proved two-sheet spectral projector decomposition, continuous functional calculus $\mathrm{CFC}.\log$ on the open Bloch ball, full noncommutative Umegaki divergence decomposition $D_{\mathrm{Umegaki}}(\rho \| \rho_\theta) = (\phi(r) - \phi(z)) + D_\phi(z \| \eta_\theta)$ with strictly positive off-diagonal coherence dissipation, forward Kolmogorov generator ODE, strict open-ball preservation for $t \ge 0$, and global relaxation to the Gibbs state. |
| **Schrödinger GKSL Bounded Exponential Flow & ODE Uniqueness** | Constructively closed in [`SchrodingerGKSLFlowBridge.lean`](../lean/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean) (and [`src/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean`](../src/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean)): proved operator-valued GKSL exponential flow on $M_n(\mathbb{C})$, flow semigroup property, orbit derivative ODE, real trace conservation, and Picard–Lindelöf ODE uniqueness. |

---

## 2. Constructively Closed Status of the Formerly Listed Targets

The former claim that these were active `sorry` declarations was historically inaccurate (none contained `sorry`), but earlier formulations left substantive mathematical gaps: `GenuineBounds.lean` provided only trivial cardinality bounds, `Pin55KreinConformalBridge.lean` assumed compatibility and provided only a degenerate zero bilinear form, earlier Krein modules lacked infinite-dimensional Hilbert boundary anomaly cancellation, the Cartan/KAN split lacked ring-general trace-to-determinant and global uniqueness proofs, and modular spin models lacked off-diagonal Bloch coherence and operator flow uniqueness. All of these gaps are now **constructively closed** by kernel-verified modules with exact proved scope:

### A. [GenuineBounds.lean](../lean/InfoGeometry/Arithmetic/GenuineBounds.lean) — Constructively Closed by [ChebyshevPrimeAndHoeffdingBounds.lean](../lean/InfoGeometry/Arithmetic/ChebyshevPrimeAndHoeffdingBounds.lean)
`GenuineBounds.lean` historically contained only the trivial cardinality inequality `primeCounting_le_add_one` (`Nat.primeCounting x ≤ x + 1`) and nonnegativity of error scales. This gap is now **constructively closed** in [`lean/InfoGeometry/Arithmetic/ChebyshevPrimeAndHoeffdingBounds.lean`](../lean/InfoGeometry/Arithmetic/ChebyshevPrimeAndHoeffdingBounds.lean) (`namespace InfoGeometry.Arithmetic.ChebyshevPrimeAndHoeffdingBounds`):
- **Hoeffding Bernoulli MGF & Chernoff Tail Bounds**: Proves `hoeffding_bernoulli_mgf` ($\mathbb{E}[e^{t(X-p)}] \le e^{t^2/8}$ for Bernoulli $p \in [0, 1]$) and `binomTailProb_le_two_mul_exp` (two-sided binomial tail bound $\le 2 e^{-2 Q \varepsilon^2}$).
- **Non-Trivial Fluctuation Certificate**: Instantiates `GenuineBounds.GenuineFiniteFluctuationCertificate` via `cert100_beats_trivial_card`, proving `cert100.bound < (Nat.primeCounting 100 : ℝ)`, strictly beating the trivial finite-cardinality bound on primes up to 100.
- **Constructive Two-Sided Erdős–Chebyshev Prime-Counting Bounds ($\Theta(n / \log n)$)**:
  - `primorial_product_le_four_pow`: primorial upper bound $\prod_{p \le n} p \le 4^n$ proved by strong induction via central binomial coefficients.
  - `chebyshevTheta_le_linear`: Chebyshev $\vartheta(n) \le (2 \log 2) n$.
  - `primeCounting_le_chebyshev_upper`: non-trivial upper bound $\pi(n) \le \sqrt{n} + (4 \log 2) \frac{n}{\log n}$ for all $n \ge 4$.
  - `erdos_chebyshev_primeCounting_lower`: constructive lower bound $\frac{n \log 4 - \log(2n+1)}{\log(2n)} \le \pi(2n)$ for all $n \ge 1$ via prime-power factorization of $\binom{2n}{n}$.
  - `primeCounting_div_tendsto_zero`: asymptotic zero density $\pi(n) / n \to 0$ as $n \to \infty$.
- *Remaining open frontier*: Constructive logarithmic-integral calculus, integration-by-parts asymptotic expansion, Chebyshev-to-$\mathrm{li}$ prime bounds, and the real-pole divergence $\lim_{\sigma \to 1^+} \mathrm{Re}(\zeta(\sigma)) = +\infty$ are now proved in [`RiemannZetaLogarithmicIntegralPrecursors.lean`](../lean/InfoGeometry/Arithmetic/RiemannZetaLogarithmicIntegralPrecursors.lean); the full asymptotic Prime Number Theorem $\pi(x) \sim \mathrm{li}(x)$ with Riemann-hypothesis optimal error $O(\sqrt{x} \log x)$ remains open (see Section 4.4).

### B. [Pin55KreinConformalBridge.lean](../lean/InfoGeometry/Lie/Pin55KreinConformalBridge.lean) — Constructively Closed by [Pin55NondegenerateKreinBridge.lean](../lean/InfoGeometry/Lie/Pin55NondegenerateKreinBridge.lean)
`Pin55KreinConformalBridge.lean` took `Pin55FiniteCarrierCompatibility` as an unproved hypothesis and defined a degenerate zero form `B_concrete_zero`. This gap is now **constructively closed** in [`lean/InfoGeometry/Lie/Pin55NondegenerateKreinBridge.lean`](../lean/InfoGeometry/Lie/Pin55NondegenerateKreinBridge.lean) (`namespace InfoGeometry.Lie.Pin55NondegenerateKreinBridge`):
- **Canonical Signature (5,5) Matrix & Nondegenerate Krein Form**:
  - `J55 := Matrix.diagonal (fun i => if i.val < 5 then 1 else -1)` with $J_{5,5}^2 = 1$ and $J_{5,5}^T = J_{5,5}$ (`J55_sq`, `J55_transpose`).
  - `kreinForm55 x y := dotProduct x (J55.mulVec y)`: strictly nondegenerate (`kreinForm55_nondegenerate`: $(\forall y, \langle x, y \rangle_{5,5} = 0) \leftrightarrow x = 0$) and certified via Mathlib's native `LinearMap.BilinForm.Nondegenerate` (`kreinBilinForm55_nondegenerate`).
- **Definite Sectors & Witt Isotropic Subspace**:
  - Positive definite on the first 5 coordinates (`kreinForm55_posSector_pos`: $x \ne 0 \to 0 < \langle x, x \rangle_{5,5}$) and negative definite on the last 5 coordinates (`kreinForm55_negSector_neg`: $x \ne 0 \to \langle x, x \rangle_{5,5} < 0$).
  - Explicit 5D totally isotropic diagonal Witt subspace `wittSubspace` ($x_{i+5} = x_i$) where $\langle x, y \rangle_{5,5} = 0$ identically (`kreinForm55_witt_isotropic`).
- **$\mathfrak{so}(5,5)$ Lie Algebra Invariance & Non-Commutative Generators**:
  - Krein-skew-adjointness $A^T J_{5,5} + J_{5,5} A = 0 \leftrightarrow J_{5,5} A J_{5,5} = -A^T$ (`isSO55_iff_J55_mul_mul_eq_neg_transpose`), infinitesimal invariance $\langle Ax, y \rangle_{5,5} + \langle x, Ay \rangle_{5,5} = 0$ (`kreinForm55_skew_adjoint`), and native `LieSubalgebra` closure `so55KreinLieSubalgebra`.
  - Concrete OpenGauss T16 non-commuting generators `genX`, `genY` in $\mathfrak{so}(5,5)$ with $X Y \ne Y X$ and $[X, Y] \ne 0$ (`genX_genY_noncomm`, `genX_genY_bracket_ne_zero`).
- *Remaining open frontier*: Global $SO(5,5)$ matrix group invariance, the 1-parameter non-compact hyperbolic boost subgroup $\Lambda(\xi)$, null quadric boundary invariance, and the conformal parabolic 3-grading of $\mathfrak{so}(5,5)$ are now proved in [`SO55GlobalConformalPrecursors.lean`](../lean/InfoGeometry/Lie/SO55GlobalConformalPrecursors.lean); infinite-dimensional conformal field theory representations on curved Lorentzian manifolds remain open (see Section 4.3).

### C. [ConcreteHilbertSewnAnomaly.lean](../lean/InfoGeometry/Canonical/ConcreteHilbertSewnAnomaly.lean) — Constructive Closure of Infinite-Dimensional Sewn Boundary Anomaly Cancellation & Krein Deficit
Earlier formulations of the two-sheet Krein boundary and Cuntz $O_2$ algebra operated at finite stages or constant diagrams, leaving open the cancellation of chiral boundary anomalies on completed infinite-dimensional Hilbert spaces. This gap is now **constructively closed** in [`lean/InfoGeometry/Canonical/ConcreteHilbertSewnAnomaly.lean`](../lean/InfoGeometry/Canonical/ConcreteHilbertSewnAnomaly.lean) (`namespace InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly`):
- **Completed Hilbert Space Carrier $H_{\ell_2}$**:
  - `H_lp E := lp (fun _ : BinaryCantorBoundary => DoubledSpace E) 2` where `DoubledSpace E := WithLp 2 (E × E)`, endowed with Mathlib's native `lp.instInnerProductSpace`.
- **Lifted Modular Swap $J_{\ell_2}$, Chiral Symmetry $\varepsilon_{\ell_2}$ & $\mathrm{Cl}(1,1)$ Anticommutation**:
  - Pointwise actions `J_raw` and `epsilon_raw` lifted to continuous linear operators `J_lp_clm` and `epsilon_lp_clm`.
  - Isometric involutions: `J_lp_clm_isometry`, `J_lp_clm_comp_self` ($J^2 = 1$), `epsilon_lp_clm_isometry`, `epsilon_lp_clm_comp_self` ($\varepsilon^2 = 1$).
  - Product identity $J \circ \varepsilon = K$ (`J_lp_clm_comp_epsilon_lp_clm`) and $\mathrm{Cl}(1,1)$ anticommutation $J \circ \varepsilon = -(\varepsilon \circ J)$ (`J_lp_clm_anticomm_epsilon_lp_clm`).
  - Self-adjointness: $\langle J \psi, \varphi \rangle = \langle \psi, J \varphi \rangle$ (`inner_J_lp_clm_selfAdjoint`).
- **Cuntz $O_2$ Branch Sewing Invariance & Non-Commutative Witness**:
  - Cuntz branch generators $S_{\mathrm{left}}, S_{\mathrm{right}}$ commute with $J$ and $\varepsilon$ (`S_left_lp_clm_commutes_J_lp_clm`, `S_right_lp_clm_commutes_J_lp_clm`, `S_left_lp_clm_commutes_epsilon_lp_clm`, `S_right_lp_clm_commutes_epsilon_lp_clm`).
  - Sewing invariance $J \circ S_i \circ J = S_i$ (`S_left_lp_clm_sewn_invariant`, `S_right_lp_clm_sewn_invariant`).
  - OpenGauss T16 non-commutativity witness: $S_{\mathrm{left}} \circ S_{\mathrm{right}} \ne S_{\mathrm{right}} \circ S_{\mathrm{left}}$ (`S_left_right_lp_clm_noncomm`).
  - Canonical non-zero $J$-fixed Cantor boundary vacuum state `canonicalCantorSewnState` (`canonicalCantorSewnState_ne_zero`, `canonicalCantorSewnState_fixed`).
- **Infinite-Dimensional Boundary Anomaly Cancellation Theorems**:
  - `infinite_hilbert_paired_chiral_summand_zero`: For every $J$-sewn bounded operator $B$ ($J \circ B \circ J = B$) and any $v \in H_{\ell_2}$, $\langle v, \varepsilon(B v) \rangle + \langle J v, \varepsilon(B(J v)) \rangle = 0$.
  - `infinite_hilbert_sewn_chiral_expectation_zero`: For every $J$-sewn bounded operator $B$ and every $J$-fixed state $\psi$ ($J \psi = \psi$), the chiral expectation $\langle \psi, \varepsilon(B \psi) \rangle = 0$.
  - `infinite_hilbert_tsum_chiral_index_zero`: For any $J$-paired family $(e_i)_{i \in \iota}$ with summable diagonal entries, the infinite-series chiral index $\sum'_{i \in \iota} \langle e_i, \varepsilon(B e_i) \rangle = 0$.
  - `canonicalCantorSewnState_chiral_zero`: $\langle \psi_{\mathrm{sewn}}, \varepsilon(B \psi_{\mathrm{sewn}}) \rangle = 0$ on the concrete non-zero Cantor state.
- *Remaining open frontier*: Continuous 4D Lorentzian quantum field theory anomaly cancellation and index theorems on smooth non-compact spacetimes.

### D. [NoncommutativeWeylCartanKANPolarEquivariance.lean](../lean/InfoGeometry/Algebra/NoncommutativeWeylCartanKANPolarEquivariance.lean) & [WeylTraceKANPolarEquivariance.lean](../lean/InfoGeometry/Canonical/WeylTraceKANPolarEquivariance.lean) — Constructive Closure of Noncommutative Weyl–Cartan Split, Iwasawa $K A N$, and Polar Equivariance
The relations between the diagonal Weyl trace scale, the Cartan decomposition, the Iwasawa $K A N$ factorization, and polar decomposition were previously known only in commuting or coordinate-restricted settings, without arbitrary-ring Plemelj–Newton trace formulas, Polar Gram reduction, or global $GL^+(2, \mathbb{R})$ uniqueness. This gap is now **constructively closed** in [`lean/InfoGeometry/Algebra/NoncommutativeWeylCartanKANPolarEquivariance.lean`](../lean/InfoGeometry/Algebra/NoncommutativeWeylCartanKANPolarEquivariance.lean) and [`lean/InfoGeometry/Canonical/WeylTraceKANPolarEquivariance.lean`](../lean/InfoGeometry/Canonical/WeylTraceKANPolarEquivariance.lean):
- **Dependency Poset $(\mathcal{K}\mathcal{P}, \preceq)$**:
  - Explicit 5-node causal dependency poset `WeylCartanKANPolarArchetype` (`KP1 ≤ KP5`, `KP2 ≤ KP4`, `KP3 ≤ KP4`) in `kpPoset_actual_dependencies` and `kpPosetLE_iff`.
- **Ring-General Weyl–Cartan Split & Trace-to-Determinant ($\mathcal{K}\mathcal{P}_1$)**:
  - Over any associative ring `[Ring B]`, decomposes $2 \bullet M = M_{\mathrm{Weyl}}(M) + M_{\mathrm{sym}}^0(M) + M_{\mathrm{antisym}}^0(M)$ (`weyl_cartan_split_and_noncommutative_trace_to_det`, `noncommutative_weyl_cartan_trace_determinant`).
  - Proves vanishing trace of symmetric and skew components, transposition symmetries, and the noncommutative Plemelj–Newton trace-to-symmetrized-determinant identity: $(\mathrm{Tr} M)^2 - \mathrm{Tr}(M^2) = \mathrm{symDet} M$.
  - Lie brackets: $[\gamma_1, \sigma] = -2\omega$, $[\omega, \gamma_1] = 2\sigma$, $[\omega, \sigma] = -2\gamma_1$.
  - Proves `fiberEmbed_central_iff` (diagonal embedding is central iff $a$ is central in $B$) and supplies explicit non-central witness over $B = M_2(\mathbb{Z})$ (`weylScalePart_noncentral_witness`).
- **Iwasawa $K A N$ Subgroups & Polar Gram Reduction ($\mathcal{K}\mathcal{P}_2$)**:
  - Over any star-ring `[Ring B] [StarRing B]`, proves $K, A, N$ subgroup composition laws (bridging to `InfoGeometry.Canonical.IwasawaKANTriad`), $N(n) N(-n) = 1$, and Polar Gram elimination of unitary $K$: $M^\dagger M = (A N)^\dagger (A N)$ under $K^\dagger K = 1$ (`iwasawa_kan_subgroups_and_polar_gram_reduction`, `kan_gram_formula`).
  - Proves noncommutative Schur complement recovery: $(M^\dagger M)_{11} - n^\star (M^\dagger M)_{00} n = a_-^\star a_-$ (`kan_gram_schur_complement`).
- **Unitary Symmetry Equivariance of Polar Decomposition ($\mathcal{K}\mathcal{P}_3$)**:
  - Over any star-ring $R$, proves $G M G^{-1} = (G U G^{-1})(G P G^{-1})$ preserves unitarity $U_G^\star U_G = 1$ and self-adjointness $P_G^\star = P_G$ whenever $G^\star = G^{-1}$ (`polar_decomposition_unitary_equivariance`, `polar_matrix_unitary_equivariance`).
- **Symmetry Equivariance of Iwasawa $K A N$ under $G(\cdot)G^{-1}$ ($\mathcal{K}\mathcal{P}_4$)**:
  - Proves 4-channel conjugation equivariance under diagonal Borelian $A(g_+, g_-)$, non-Abelian fiber gauge $\iota(g)$, chirality parity $\gamma_1$, and Weyl reflection $\sigma$ (`iwasawa_kan_symmetry_equivariance`), synthesized in `kan_polar_gram_fiber_unitary_equivariance`.
- **Global Existence & Uniqueness on $GL^+(2, \mathbb{R})$ ($\mathcal{K}\mathcal{P}_5$)**:
  - Proves global existence and uniqueness of Iwasawa $K A N$ factorization (`real_gl2_pos_iwasawa_factorization`, `real_gl2_pos_kan_unique`), frame-push relative Iwasawa factorization (`relative_iwasawa_factorization`, `relative_iwasawa_unique`), and polar decomposition (`real_gl2_pos_polar_factorization`, `real_gl2_pos_polar_unique`, `real_gl2_pos_metric_polar_unique`) with positive-definite symmetric factor $P$, metric polar uniqueness, and orthogonal conjugation equivariance.
- *Remaining open frontier*: Global infinite-dimensional diffeomorphism group factorizations and gauge group Sobolev orbit spaces.

### E. [BlochBallUmegakiAndQuantumSpohn.lean](../lean/InfoGeometry/Modular/BlochBallUmegakiAndQuantumSpohn.lean) — Constructive Closure of Off-Diagonal Bloch-Ball Umegaki Relative Entropy & Quantum Spohn Dissipation
Earlier GKSL modules formalizing spin cumulants (`GKSLGibbsAndDuallyFlatSpinCumulants.lean`) treated only diagonal binary KL / longitudinal spin divergences $\eta \in (-1, 1)$, leaving open the full noncommutative off-diagonal $M_2(\mathbb{C})$ relative entropy and Spohn dissipation rate. This gap is now **constructively closed** in [`lean/InfoGeometry/Modular/BlochBallUmegakiAndQuantumSpohn.lean`](../lean/InfoGeometry/Modular/BlochBallUmegakiAndQuantumSpohn.lean) (`namespace InfoGeometry.Modular.BlochBallUmegakiAndQuantumSpohn`):
- **Exact Continuous Functional Calculus on Open Bloch Ball ($\mathcal{G}_8$)**:
  - On full self-adjoint unit-trace states $\rho \in M_2(\mathbb{C})$ inside the open Bloch ball $\|\vec{r}(\rho)\|^2 = z^2 + 4|\rho_{01}|^2 < 1$, constructs `spectralProjector ρ`, proves $\rho = \mathrm{twoSheet}\ P\ \frac{1+r}{2}\ \frac{1-r}{2}$, proves `IsStrictlyPositive ρ`, and evaluates `CFC.log ρ` and `CFC.log (gibbsDensityC θ)` (`spectralProjector_twoSheet_and_cfc_log`, `gibbsDensityC_strictlyPositive_and_cfc_log`).
- **Noncommutative Umegaki Divergence & Coherence Pinching Pythagoras ($\mathcal{G}_9$)**:
  - Evaluates $( \mathrm{Tr}(\mathrm{umegakiKernel}\ \rho\ \rho_\theta) )_{\mathrm{re}}$ and proves $D_{\mathrm{Umegaki}}(\rho \| \rho_\theta) = (\phi(r) - \phi(z)) + D_\phi(z \| \eta_\theta)$ (`umegakiKernel_trace_and_coherence_pythagoras`).
  - Proves strict non-negativity of off-diagonal coherence contribution $\phi(r) - \phi(z) \ge 0$ (vanishing iff $\rho_{01} = 0$) and faithfulness ($D_{\mathrm{Umegaki}}(\rho \| \rho_\theta) = 0 \leftrightarrow \rho = \rho_\theta$).
- **Kolmogorov ODE, Three-Channel KMS Spohn Rate & Relaxation ($\mathcal{G}_{10}$)**:
  - Proves entrywise forward Kolmogorov ODE: `hasDerivAt_thermalSemigroupC_eq_lindbladian`.
  - Proves strict open-Bloch-ball invariance and positivity preservation for $t \ge 0$ (`thermalSemigroupC_preserves_blochBall`).
  - Proves operator Spohn entropy production rate $-\mathrm{Re}\mathrm{Tr}(\mathcal{L}(\sigma)(\log\sigma - \log\rho_\theta)) = \sigma_{\mathrm{KMS}}(\gamma, \theta, \sigma) \ge 0$ as a sum of three positive fluxes with **strictly positive** dissipation whenever off-diagonal coherence $\sigma_{01} \ne 0$ (`operator_spohn_rate_and_strict_coherent_dissipation`).
  - Proves full-matrix Spohn derivative identity $\frac{d}{dt} D_{\mathrm{Umegaki}}(\rho(t) \| \rho_\theta) = -\sigma_{\mathrm{KMS}}(\rho(t))$ and asymptotic global relaxation to Gibbs state (`master_bloch_umegaki_spohn_and_gibbs_relaxation`).
  - Proves forward-positivity monoid characterization with explicit backward-time failure witness for every $t < 0$ (`forward_monoid_positivity_iff_and_backward_aporia`).
- *Remaining open frontier*: Infinite-dimensional von Neumann algebra quantum dynamical semigroups and non-Markovian memory kernels.

### F. [SchrodingerGKSLFlowBridge.lean](../lean/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean) — Constructive Closure of Finite-Matrix Schrödinger GKSL Exponential Flow & ODE Uniqueness
Prior formalizations of the Schrödinger GKSL generator in `SchrodingerGKSL.lean` defined the instantaneous infinitesimal generator but did not establish the continuous linear operator exponential flow or prove Picard–Lindelöf ODE uniqueness. This gap is now **constructively closed** in [`lean/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean`](../lean/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean) (co-located in [`src/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean`](../src/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean)) (`namespace InfoGeometry.Modular.SchrodingerGKSLFlowBridge`):
- **Continuous Linear Map GKSL Generator**:
  - Constructs `generatorCLM H V : Matrix n n ℂ →L[ℂ] Matrix n n ℂ` using continuous left/right multiplication operators, proving `generatorCLM_apply`: `generatorCLM H V X = schrodingerLindbladian H V X`.
  - Restricts scalars to real linear endomorphism `generatorEnd H V : Matrix n n ℂ →L[ℝ] Matrix n n ℂ`.
- **Bounded Exponential Flow & Semigroup Law**:
  - Defines `gkslFlow H V t := flow (generatorEnd H V) t`.
  - Proves group semigroup property: `gkslFlow H V (s + t) = gkslFlow H V s * gkslFlow H V t` (`gkslFlow_add`).
  - Proves orbit differential equation: `hasDerivAt_gkslFlow_orbit` ($\frac{d}{dt} \mathrm{gkslFlow}\ H\ V\ t\ X = \mathrm{schrodingerLindbladian}\ H\ V\ (\mathrm{gkslFlow}\ H\ V\ t\ X)$).
- **Picard–Lindelöf ODE Uniqueness**:
  - Proves `gkslFlow_unique_of_ode` via `ODE_solution_unique_univ`, establishing that any globally differentiable solution $f : \mathbb{R} \to M_n(\mathbb{C})$ of $\dot{f}(t) = \mathcal{L}(f(t))$ with $f(0) = X$ is uniquely given by $f(t) = \mathrm{gkslFlow}\ H\ V\ t\ X$.
- **Full Matrix Real Trace Conservation**:
  - Proves `realTrace_gkslFlow`: $(\mathrm{Tr}(\mathrm{gkslFlow}\ H\ V\ t\ X))_{\mathrm{re}} = (\mathrm{Tr}\ X)_{\mathrm{re}}$ using trace-zero property of the Lindblad generator.
- *Remaining open frontier*: Unbounded generators on infinite-dimensional Hilbert spaces with non-trivial domain subtleties.

---

## 3. Audit Scope

This correction is based on current source inspection of the named owners and their direct references. It does not certify the entire repository's placeholder status or build state. A current global debt inventory requires a fresh exhaustive scan, dependency/taint analysis, and the repository's locked verification pipeline.

---

## 4. Explicit Active Open Frontiers (Strict Epistemic Boundaries)

In accordance with `docs/MarkdownCorpusGovernance.md` and `AGENTS.md`, the repository maintains strict epistemic honesty by clearly distinguishing proved finite-algebraic, lattice, continuous-$L^2([0,1])$, Lie-group, and $\mathrm{li}(x)/\zeta$ precursor theorems from active open research frontiers:

1. **Frontier 1 — Continuum 4D Wightman/Osterwalder–Schrader Non-Abelian Yang–Mills & Mass Gap**:
   - *Proved in repository*: Discrete/lattice Euclidean transfer matrix semigroup $T(J) \in M_2(\mathbb{R})$ (`transferMat`, `normTransferMat`), spectral decomposition $P_0 + (\tanh J) P_1$, positive-definiteness (`transferMat_posDef`), strictly positive spectral mass gap $\Delta(J) = -\log(\tanh J) = \log(\coth J) > 0$ (`spectralMassGap_pos`), exponential clustering $(\tanh J)^L = e^{-L\Delta(J)} \to 0$ (`normTransferMat_pow_eq_exp_gap`, `normTransferMat_clustering_tendsto_zero`), bridge to the Elitzur Wilson string expectation (`expect_wilson_from_transferMat`), and transfer-matrix-weighted 2-slice Osterwalder–Schrader reflection positivity (non-trivial time-reflection involution `osReflect`, Boltzmann partition expectation `osExpectation`, `os_reflection_positivity` for $J > 0$, antiferromagnetic $J < 0$ failure `os_reflection_positivity_fails_antiferro`, Cauchy–Schwarz `os_cauchy_schwarz`, and $L$-step semigroup positivity `os_semigroup_reflection_positivity`) in [`OsterwalderSchraderTransferSemigroupAndMassGap.lean`](../lean/InfoGeometry/OperatorAlgebra/OsterwalderSchraderTransferSemigroupAndMassGap.lean) — building on algebraic matrix exterior-algebra connection curvature (`SelfDualConnectionCurvatureYangMillsBridge.lean`), Peirce Maurer–Cartan self-dual Bianchi identities (`PeirceDefectBridge.lean`), inductive UHF/tensor-tower colimit trace coercivity (`PeirceTetraktysColimitCoercivity.lean`), discrete lattice gauge invariance with Elitzur projection ([`ElitzurLatticeGaugeProjection.lean`](../lean/InfoGeometry/OperatorAlgebra/ElitzurLatticeGaugeProjection.lean), [`NLinkElitzurChainAndCompactU1Gauge.lean`](../lean/InfoGeometry/OperatorAlgebra/NLinkElitzurChainAndCompactU1Gauge.lean)), and infinite-dimensional Cantor boundary Hilbert sewing anomaly cancellation ([`ConcreteHilbertSewnAnomaly.lean`](../lean/InfoGeometry/Canonical/ConcreteHilbertSewnAnomaly.lean)).
   - *Open frontier*: Constructing a continuous 4D non-Abelian quantum gauge field theory on Minkowski/Euclidean spacetime $\mathbb{R}^4$ in the continuum limit $a \to 0$ satisfying all Wightman or Osterwalder–Schrader axioms with a strictly positive continuum spectral mass gap remains OPEN.

2. **Frontier 2 — Continuous $L^2(\mathbb{R})$ Bourgain–Dyatlov Fractal Uncertainty Principle (FUP)**:
   - *Proved in repository*: Continuous $L^2([0, 1])$ trigonometric mode pairs (`modeSin`, `modeCos`), exact pointwise energy identity $s_n(x)^2 + c_n(x)^2 = 2$ (`mode_sq_sum_eq_two`), exact interval energy $\int_a^b (s_n(x)^2 + c_n(x)^2)\,dx = 2(b-a)$ (`interval_energy_mode_pair`), wavepacket Cauchy–Schwarz pointwise and interval energy bounds (`wavepacket_pointwise_cauchy_schwarz`, `wavepacket_interval_energy_bound`), multiscale Cantor contraction $((b-m)^2/b)^k \to 0$ for $b-m < \sqrt{b}$ (`cantor_fup_ratio_lt_one`, `continuous_cantor_wavepacket_contraction`, `continuous_cantor_fup_tendsto_zero`), and concrete witness at $b = 4, m = 3$ (`continuous_cantor_witness_b4_m3`, ratio $1/4$) in [`ContinuousL2CantorFourierUncertainty.lean`](../lean/InfoGeometry/Analysis/ContinuousL2CantorFourierUncertainty.lean), building on discrete multiscale Cantor FUP on $\mathbb{C}^N$ ([`DiscreteCantorFourierUncertainty.lean`](../lean/InfoGeometry/Algebra/DiscreteCantorFourierUncertainty.lean)).
   - *Open frontier*: The full Bourgain–Dyatlov fractal uncertainty principle on $L^2(\mathbb{R})$ for arbitrary $\delta$-regular fractal sets with an exponent $\beta > 0$ under the continuous Fourier transform remains OPEN.

3. **Frontier 3 — Global Non-Compact $SO(5,5)$ Curved-Manifold CFT Representations**:
   - *Proved in repository*: Global Lie group $SO(5,5)$ (`IsSO55GroupMatrix`: $M^T J_{5,5} M = J_{5,5} \wedge \det M = 1$), group closure (`isSO55_one`, `isSO55_mul`), Krein isometry (`isSO55_isometry`), explicit 1-parameter non-compact hyperbolic boost subgroup $\Lambda(\xi)$ (`so55Boost`, `so55Boost_add`, `so55Boost_isSO55`, `so55Boost_unbounded`), conformal null quadric boundary invariance (`nullQuadric_invariant`), and conformal parabolic 3-grading of $\mathfrak{so}(5,5)$ ($[D, P_k] = P_k$, $[D, K_k] = -K_k$, $P_k^3 = 0$ via `bracket_genD_genP`, `bracket_genD_genK`, `genP_nilpotent3`) in [`SO55GlobalConformalPrecursors.lean`](../lean/InfoGeometry/Lie/SO55GlobalConformalPrecursors.lean), building on [`Pin55NondegenerateKreinBridge.lean`](../lean/InfoGeometry/Lie/Pin55NondegenerateKreinBridge.lean).
   - *Open frontier*: Infinite-dimensional curved-manifold conformal field theory (CFT) representations on Lorentzian spacetimes remain OPEN.

4. **Frontier 4 — Complex-Analytic Riemann-Zeta $\mathrm{li}(x)$ Error Bounds & Prime Number Theorem**:
   - *Proved in repository*: Calculus of $\mathrm{li}(x) = \int_2^x \frac{dt}{\log t}$ (`li_two`, `continuousOn_one_div_log`, `intervalIntegrable_one_div_log`, `hasDerivAt_li` establishing $\mathrm{li}'(x) = 1/\log x$, `li_pos`), integration-by-parts expansion $\mathrm{li}(x) = x/\log x - 2/\log 2 + \int_2^x \frac{dt}{(\log t)^2}$ (`fundamental_li_by_parts`), two-sided $\Theta(x/\log x)$ and remainder bounds (`li_sub_div_log_pos`, `integral_one_div_log_sq_le`, `li_le_linear_over_log_sq`), constructive Chebyshev-to-$\mathrm{li}$ prime counting bound (`primeCounting_le_chebyshev_li`), and complex-analytic real-pole divergence $\lim_{\sigma \to 1^+} \mathrm{Re}(\zeta(\sigma)) = +\infty$ (`tendsto_riemannZeta_one_right_atTop`) in [`RiemannZetaLogarithmicIntegralPrecursors.lean`](../lean/InfoGeometry/Arithmetic/RiemannZetaLogarithmicIntegralPrecursors.lean), building on [`GenuineBounds.lean`](../lean/InfoGeometry/Arithmetic/GenuineBounds.lean) and [`ChebyshevPrimeAndHoeffdingBounds.lean`](../lean/InfoGeometry/Arithmetic/ChebyshevPrimeAndHoeffdingBounds.lean).
   - *Open frontier*: The full asymptotic Prime Number Theorem $\pi(x) \sim \mathrm{li}(x)$ with the Riemann Hypothesis square-root error bound $O(\sqrt{x} \log x)$ remains OPEN.

5. **HTTP 404 Drive Document Recovery**:
   - *Current status*: External Google Drive research documents referenced in historical transcripts (`cached/drive_docs/`, `cached/qms_audit_drive_docs/`) that return HTTP 404 cannot be recovered from broken links. All formal mathematical definitions, theorems, and proofs in this repository are grounded strictly in the kernel-checked `.lean` source files and local cached artifacts, with zero reliance on missing external URLs.
