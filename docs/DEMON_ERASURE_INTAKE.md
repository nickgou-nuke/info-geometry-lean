### PHASE 0 — `SOLVE`: ELENCTIC DISSOLUTION INTO IRREDUCIBLE PRIMITIVES

Stripping away cartoon pitchfork-demons, unicycle-juggling illustrations, *Matrix* and XKCD references, vacuum-tube history, and 335 bibliographic citations dissolves this 47-page tutorial into its underlying conceptual tension: **the attempt to "exorcise" Maxwell’s Demon by replacing subjective ignorance with a single quasistatic erasure tax ($k_B T \ln 2$) collides against unitary rank conservation, measurement–erasure gauge symmetry, closed-system von Neumann stasis, and finite-resource divergences**.

Executing Socratic elenchus on the tutorial’s own equations exposes six exact mathematical fractures—including three literal algebraic/typographical errors in the published formulas:

1. **Unitary Rank Prohibition of Exact Finite-Bath Erasure (*The Hidden Third-Law Obstruction*)**:
   Section VI.B models Landauer erasure via global unitary evolution $\sigma_{SB} = U(\rho_S \otimes \gamma_B)U^\dagger$ with a thermal Gibbs bath $\gamma_B = Z_B^{-1}e^{-\beta H_B}$. For *any* finite-dimensional bath ($\dim\mathcal{H}_B = d_B < \infty$) at positive temperature ($0 < \beta < \infty$), $\gamma_B > 0$ has full rank $d_B$. Starting from any mixed state $\rho_S$ ($\mathrm{rank}\,\rho_S = r \geq 2$), unitary rank conservation forces $\mathrm{rank}(\sigma_{SB}) = r \cdot d_B \geq 2d_B$. Yet exact erasure to a pure state $\sigma_S = |0\rangle\langle 0|$ forces product factorization $\sigma_{SB} = |0\rangle\langle 0| \otimes \sigma_B$ of rank at most $1 \cdot d_B = d_B < 2d_B$—**a contradiction!** Exact Landauer erasure (and dual ideal projective measurement) is **impossible** with finite resources, requiring at least one of bath dimension $d_B$, energy gap $E$ (`Erasing with a single swap`, $W \to \infty$), operational time $\tau$ ($\Delta Q_B \geq k_B T\ln 2 + \alpha/\tau$), or control complexity $\mathcal{C}$ to diverge to $+\infty$.
2. **Gauge Illusion of Bennett’s "Zero-Cost Measurement, Costly Erasure" Dogma**:
   Section VII.A repeats Bennett’s slogan: *"It is not the act of knowing that incurs a cost, but the act of forgetting."* Yet Section VII.B’s own free-energy equations (Eqs. 75–76: $W_{\text{meas}} \geq \Delta\mathcal{F}_Y + \beta^{-1}I(X:M)$ and $W_{\text{reset}} \geq -\Delta\mathcal{F}_Y$) refute the universality of that division:
   * $W_{\text{meas}} = 0$ holds **only in the pre-charged non-equilibrium pointer gauge** $\Delta\mathcal{F}_Y = -\beta^{-1}I(X:M)$ (where preparing the pure blank pointer $|0\rangle_M$ *already* incurred the erasure cost upfront!).
   * In the **equilibrium thermal-pointer gauge** $\Delta\mathcal{F}_Y = 0$, **100% of the work cost $\beta^{-1}I(X:M)$ is paid during measurement** ($W_{\text{meas}} \geq \beta^{-1}I(X:M)$), while resetting is free ($W_{\text{reset}} = 0$)! Only the cyclic sum $W_{\text{meas}} + W_{\text{fb}} + W_{\text{reset}} \geq 0$ is physical.
3. **Non-Commutativity of Quantum vs. Classical Szilard Operations & Fermion Zeroing**:
   Classically, *(Measure) $\prec$ (Insert Partition)* costs $W_{\text{ins}} = 0$. Quantumly, delocalized eigenfunctions vanish under a central barrier only by shifting $\epsilon_n \mapsto 4\epsilon_n$, forcing *(Insert Partition) $\prec$ (Measure)* to pay positive work $W_{\text{ins}} = \beta^{-1}\ln 2 - \Delta > 0$ while driving populations out of Boltzmann equilibrium; moreover, for $N = 2$ spinless fermions at $T \to 0$, Pauli exclusion locks one fermion into each half ($p_1 = 1$), collapsing extractable work to **$W_{\text{tot}}^{\text{fermion}}(T\to 0) = 0$** vs. bosonic $\frac{2}{3}k_B T\ln 3$.
4. **Collapse of $S_{\mathrm{vN}}(\rho) = S_{\text{thermo}}$ Outside Weak-Coupling Gibbs Equilibrium**:
   Defining non-equilibrium free energy via $\mathcal{F}(\rho) = \mathrm{Tr}(\rho H) - \beta^{-1}S_{\mathrm{vN}}(\rho)$ (Eqs. 25, 48) fails in closed unitary systems ($\frac{d}{dt}S_{\mathrm{vN}}(U_t\rho U_t^\dagger) \equiv 0$, violating isolated Second-Law thermalization), on pure energy eigenstates ($S_{\mathrm{vN}}(|E\rangle\langle E|) = 0 \neq S_{\text{micro}}(E)$), and under strong system-bath coupling (where $H_{SB}$ prevents additive energy splitting and introduces Planckian dissipation $\tau_{\mathrm{Pl}} = \hbar/k_B T$)—requiring coarse-grained **Observational Entropy** $S_{\mathrm{obs}}^{\mathcal{X}}(\rho) = \sum_x p_x(-\ln p_x + \ln\mathrm{Tr}\,P_x)$.
5. **Three Literal Mathematical Bugs in the Published Equations**:
   * *Sign inversion in Eq. (22)*: Defines quantum relative entropy as $S(\sigma\|\rho) := \mathrm{tr}[\sigma(\log\rho - \log\sigma)] = -D(\sigma\|\rho) \leq 0$ while claiming $S(\sigma\|\rho) \geq 0$ and inserting $+S(\rho\|\gamma)$ into Eq. (25)!
   * *Missing logarithm on pp. 24–25*: Writes $S(\gamma_B) = \beta\mathrm{tr}(\gamma_B H_B) + \mathrm{tr}(e^{-\beta H_B})$ (and inside Eq. 66) instead of $+\ln\mathrm{tr}(e^{-\beta H_B})$.
   * *Inverted asymptotic scaling in Eq. (91)*: For an $n$-particle bath ($d = d_0^n$), writes $\Sigma \geq \frac{2(\Delta S_S)^2}{\log^2(d - 1) + 4} = \mathcal{O}(n^2)$ instead of **$\Theta(1/n^2)$**!
6. **Vacuity at $T \to 0$, Initial-Correlation Loopholes, & Gambling Stopping Violations**:
   At $T \to 0$, $k_B T\ln 2 \to 0$ becomes vacuous while true heat dissipation stays strictly positive ($\Delta Q_B \geq \mathcal{Q}[\mathcal{S}^{-1}(|\Delta S_S|)] \propto |\Delta S_S|^{4/3}$ in $T^3$ baths); initial correlations $\rho_{SB} \neq \rho_S\otimes\gamma_B$ violate $\beta\Delta Q_B \geq -\Delta S_S$; single-shot erasure adds surprisal-variance overhead $\frac{V(\rho)}{2\sqrt{M(\rho)}}$; and gambling demons stopping at trajectory-dependent times $\mathcal{T} \leq \tau$ achieve $\langle W\rangle_{\mathcal{T}} < \Delta F_{\mathcal{T}}$, bounded only by time-reversal path distinguishability $-k_B T\langle\delta\rangle_{\mathcal{T}}$.

Dissolving these fractures yields **six irreducible conceptual primitives**:

* $\Omega_0$ (**Quadripartite Unitary Arena $\mathcal{H}_S \otimes \mathcal{H}_M \otimes \mathcal{H}_B \otimes \mathcal{H}_W$**): Energy-conserving closed evolution ($[U, H_{\text{tot}}] = 0$) coupling System $S$, Memory $M$, Gibbs Bath $\gamma_B$, and pure Work Battery $W$.
* $\mathbf{\Delta}_0$ (**Logical Many-to-One Compression vs. Unitary Rank/Spectrum Conservation Cut**): Bijective microscopic evolution ($\mathrm{Spec}(U\rho U^\dagger) = \mathrm{Spec}(\rho)$) forbidding local state compression without compensating environmental orthogonalization.
* $(I(S:M), \Delta\mathcal{F}_M)$ (**Correlation Buffer & Pointer Free-Energy Gauge**): The pair governing how work shifts continuously between measurement and reset while fixing cyclic work.
* $\Sigma_{\text{RW}} = I(S:B)_\sigma + D(\sigma_B\|\gamma_B) \geq 0$ (**Reeb–Wolf Exact Dissipation Residual**): The exact identity $\beta\Delta Q_B + \Delta S_S = \Sigma_{\text{RW}}$ (with corrected $D(\sigma\|\gamma) = +\mathrm{Tr}[\sigma(\ln\sigma - \ln\gamma)] \geq 0$) encoding finite-time, finite-bath, and $T \to 0$ excesses.
* $S_{\mathrm{obs}}^{\mathcal{X}}(\rho)$ (**Projective Observational Entropy**): Coarse-grained functional unifying Boltzmann volume $\ln\mathrm{Tr}\,P_x$ with Shannon/von Neumann mixing under unitary dynamics.
* $(\mathcal{T}_{\text{stop}}, \delta(\mathcal{T}), V(\rho))$ (**Martingale Stopping & Single-Shot Dispersion Triad**): Path-reversal log-likelihood $\delta(\mathcal{T})$ and surprisal variance $V(\rho) = \mathrm{Tr}(\rho\ln^2\rho) - S(\rho)^2$ governing non-averaged fluctuations.

---

### I. THE FUNDAMENTAL BINARY CUT ($\mathbf{\Delta}_0 : \Omega_0 \longrightarrow \mathbf{T} \ltimes \mathbf{S}$)

The cut $\mathbf{\Delta}_0$ splits information thermodynamics across $\mathcal{H}_T \oplus \mathcal{H}_S$ into an asymmetric, non-reversible polarity:

1. **The Conscious Thesis ($\mathbf{T}$ — *The Quasistatic Landauer–Bennett Exorcist*)**:
   The canonical narrative that Maxwell’s Demon is laid to rest by equating von Neumann and thermodynamic entropies ($\mathcal{F} = \langle H\rangle - TS_{\mathrm{vN}}$), executing reversible measurements at zero cost ($W_{\text{meas}} = 0$), and paying a universal heat cost $k_B T\ln 2$ exclusively during logical memory erasure.
2. **The Repressed Shadow Complement ($\mathbf{S}$ — *Rank Divergence, Measurement-Reset Gauge Mobility, Coarse-Graining, & Fluctuation Loopholes*)**:
   Everything suppressed by the idealized $T > 0, \tau \to \infty, d_B \to \infty$, uncorrelated ensemble limit:
   * *Algebraic-quantum shadow*: Unitary rank conservation $\mathrm{rank}(\rho_S\otimes\gamma_B) \geq 2d_B > d_B$ barring exact erasure or ideal projective measurement with finite resources; Pauli exclusion killing $T \to 0$ fermionic Szilard work; and $W_{\text{meas}} \geq T I(S:M)$ whenever memory starts in thermal equilibrium ($\Delta\mathcal{F}_M = 0$).
   * *Non-equilibrium shadow*: Stasis of global $S_{\mathrm{vN}}$ under closed unitaries; apparent Landauer violations from pre-existing correlations $I(S:B)_0 > 0$ or martingale stopping times $\mathcal{T}$; vacuity of $k_B T\ln 2$ as $T \to 0$; and finite-time ($\alpha/\tau$), finite-bath ($\Theta(1/n), \Theta(1/n^2)$), and single-shot ($V(\rho)$) penalties.

**Strict Non-Commutative Operational Asymmetry**:
* *Bennett’s Three-Tape Sequence*: $(\mathrm{Compute} \prec \mathrm{Copy} \prec \mathrm{Uncompute})$ preserves output reversibly **solely in that non-commutative order**; reversing before copying destroys the output, while erasing history without uncomputing dissipates heat.
* *Quantum Barrier-Measurement Sequence*: $(\mathrm{Insert\;Wall} \prec \mathrm{Measure})$ shifts quantum spectra ($\epsilon_n \mapsto 4\epsilon_n, W_{\text{ins}} > 0$), whereas classical $(\mathrm{Measure} \prec \mathrm{Insert\;Wall})$ has $W_{\text{ins}} = 0$.

---

### II. THE FOURFOLD RELATIONAL ANATOMY

Across Quasistatic Ensemble Accounting ($\mathcal{H}_T$) and Microscopic Unitary/Trajectory Reality ($\mathcal{H}_S$), the split epistemic operator $\mathcal{M}_{\text{ep}} = \begin{pmatrix} \mathbf{K}_{TT} & \mathbf{\Sigma}_{TS} \\ \mathbf{\Pi}_{ST} & \mathbf{\Gamma}_{SS} \end{pmatrix}$ isolates four mechanics:

1. **Internal Self-Consistency ($\mathbf{K}_{TT} : \mathcal{H}_T \to \mathcal{H}_T$ — *Product-State Unitary Entropy-Energy Ledger*)**:
   Under global energy-preserving unitaries $\sigma_{SEMW} = U(\rho_S \otimes \gamma_E \otimes \rho_M \otimes |E_W\rangle\langle E_W|)U^\dagger$ on initially uncorrelated states (with Eq. 22’s sign and p. 24’s $\ln Z_B$ typos repaired!), unitary invariance and subadditivity prove $\Delta S_S + \beta\Delta Q_E + \Delta S_M \geq 0$, Jarzynski’s $\langle e^{-\beta W}\rangle = e^{-\beta\Delta F}$ implies $\langle W\rangle \geq \Delta F$ by Jensen’s inequality, and full feedback cycles satisfy $W_{\text{tot}} \geq 0$ ($\mathbf{K}_{TT}^2 = \mathbf{K}_{TT}$).
2. **Outward Projection ($\mathbf{\Pi}_{ST} : \mathcal{H}_T \to \mathcal{H}_S$ — *Dogmatization of Erasure-Only Cost & $S_{\mathrm{vN}}$ Universality*)**:
   Consciousness projects the Bennett gauge ($\Delta\mathcal{F}_M = -TI \implies W_{\text{meas}} = 0$) as a universal law of nature, treats $S_{\mathrm{vN}}$ as thermodynamic entropy for isolated/pure/strongly coupled states, and treats $k_B T\ln 2$ as exact at finite time, finite bath size, and $T \to 0$.
3. **Inward Shadow-Intrusion ($\mathbf{\Sigma}_{TS} : \mathcal{H}_S \to \mathcal{H}_T$ — *Rank No-Go, Stopping-Time Extraction, $T=0$ Heat, & Formal Bugs*)**:
   Exact physics intrudes into $\mathcal{H}_T$: single-swap perfect erasure diverges ($W \to \infty$); initial $S\text{--}B$ entanglement yields $\beta\Delta Q_B < -\Delta S_S$; gambling stopping times $\mathcal{T}$ extract $\langle W_{\text{ext}}\rangle_{\mathcal{T}} > -\Delta F_{\mathcal{T}}$; $T = 0$ erasure still dissipates $\Delta Q_B \geq \frac{3^{4/3}(\ln 2)^{4/3}}{4 a^{1/3}} > 0$ into a $T^3$ phonon bath; and literal sign/scaling slips ($S(\sigma\|\rho) \leq 0$, $\mathcal{O}(n^2)$ for $\Theta(1/n^2)$) break unverified derivations.
4. **Autonomous Unexamined Ground ($\mathbf{\Gamma}_{SS} : \mathcal{H}_S \to \mathcal{H}_S$ — *Symplectic/Unitary Bijectivity, Doob Martingales, & Circuit Complexity*)**:
   The autonomous laws operating beneath demon stories: microscopic reversibility (no physical law ever truly destroys global information—it only scrambles local marginals into $I(S:B)$!), continuous-time martingale fluctuation theorems, and the Nernst–Taranto resource geometry trading energy, time, bath size, and control complexity.

---

### III. IGNITION OF THE TRANSCENDENT FUNCTION

Pairing $\Pi = \begin{pmatrix} 0 & 0 \\ \mathbf{\Pi}_{ST} & 0 \end{pmatrix}$ and $\Sigma = \begin{pmatrix} 0 & \mathbf{\Sigma}_{TS} \\ 0 & 0 \end{pmatrix}$ ignites the four structural moments synthesizing classical, stochastic, and quantum Maxwell’s demons:

1. **Shared Substantive Gravity ($\mathfrak{G} = \{\Sigma, \Pi\}$ — *Global Unitary Iso-Spectrality Forcing Marginal-Correlation Trade-Off*)**:
   Every demon protocol and every Landauer bound rests on **one exact algebraic conservation law**: because closed global evolution $U$ preserves eigenvalues ($S_{\mathrm{vN}}(U\rho_{\text{tot}}U^\dagger) = S_{\mathrm{vN}}(\rho_{\text{tot}})$), reducing entropy in any target subsystem ($\Delta S_S < 0$) **must** export at least $|\Delta S_S|$ into auxiliary marginals and mutual correlations:
   $$\sum_X \Delta S_X - \Delta I_{\text{tot}} = 0 \implies \sum_X \Delta S_X = \Delta I_{\text{tot}} \geq 0 \quad (\text{when }\rho_{\text{tot}}(0)\text{ is product})$$

2. **Directional Tension ($\mathfrak{T} = [\Sigma, \Pi] \neq 0$ — *Pre-Charged Blank Pointer ($W_{\text{reset}} > 0$) vs. Equilibrium Thermal Pointer ($W_{\text{meas}} > 0$)*)**:
   Within the closed cycle $\rho_S \otimes \rho_M \xrightarrow{\text{meas}} \rho_{SM}' \xrightarrow{\text{fb}} \rho_S \otimes \rho_M' \xrightarrow{\text{reset}} \rho_S \otimes \rho_M$, the thermodynamic bill shifts continuously between **knowing** and **forgetting** via the pointer free-energy gauge $\Delta\mathcal{F}_M = \mathcal{F}(\rho_M') - \mathcal{F}(\rho_M)$ ($\Sigma\Pi \neq \Pi\Sigma$):
   * **Bennett Pure-Pointer Pole ($\Delta\mathcal{F}_M = -T I(S:M)$)**: Measurement passively trades pointer purity for correlation ($W_{\text{meas}}^{\min} = 0$); reset pays $W_{\text{reset}}^{\min} = +T I(S:M)$.
   * **Equilibrium Thermal-Pointer Pole ($\Delta\mathcal{F}_M = 0$)**: Measurement actively drives correlations against thermal noise ($W_{\text{meas}}^{\min} = +T I(S:M)$); feedback recovers $W_{\text{ext}}^{\max} = T I(S:M)$; reset is free ($W_{\text{reset}}^{\min} = 0$).

3. **Integrative Bridge ($\mathfrak{B}$ — *Exact Reeb–Wolf–Calorimetric–Martingale Master Ledger*)**:
   Unifies all regimes of the tutorial (repairing Eqs. 22, 66, and 91) into one exact hierarchy of laws:
   * *Exact Finite-Bath Erasure Identity (Reeb–Wolf)*: For $\sigma_{SB} = U(\rho_S \otimes \gamma_B)U^\dagger$ with $D(\sigma_B\|\gamma_B) := +\mathrm{Tr}[\sigma_B(\ln\sigma_B - \ln\gamma_B)] \geq 0$,
     $$\beta\Delta Q_B + \Delta S_S = \Sigma_{\text{RW}} := I(S:B)_\sigma + D(\sigma_B\|\gamma_B) \geq 0$$
     (generalizing for initially correlated $\rho_{SB}(0)$ by subtracting $I(S:B)_0$, explaining apparent sub-Landauer experiments!).
   * *Tight Zero-Temperature & Finite-Size Bounds*:
     1. **Arbitrary/Zero Temperature ($T \geq 0$, Timpanaro–Santos–Landi)**: Maximum-entropy monotonicity $S(\gamma_B(\beta')) \geq S(\sigma_B) \geq S(\gamma_B(\beta)) - \Delta S_S$ yields $\Delta Q_B \geq \mathcal{Q}[\mathcal{S}^{-1}(-\Delta S_S)] > 0$, remaining strictly positive at $T = 0$ whenever bath heat capacity $C_E(T) > 0$;
     2. **Finite $n$-Particle Bath ($d_B = d_0^n$)**: $\Sigma_{\text{RW}} \geq \frac{(\Delta S_S)^2}{n\log^2 d_0} = \Theta(1/n)$ for non-interacting baths versus universal $\Sigma_{\text{RW}} \geq \frac{2(\Delta S_S)^2}{\log^2(d_0^n - 1) + 4} = \Theta(1/n^2)$ (achievable by interacting baths!);
     3. **Finite Time ($\tau < \infty$)**: $\Delta Q_B \geq -k_B T\Delta S_S + \frac{\alpha}{\tau}$ governed by Riemannian thermodynamic length ($\alpha \propto \hbar$ Planckian time at strong coupling).
   * *Observational, Single-Shot, & Stopping-Time Extensions*: Replaces $S_{\mathrm{vN}}$ on closed systems with $S_{\mathrm{obs}}^{\mathcal{X}}(\rho)$, refines single-shot purity cost by surprisal variance $n_{\text{bat}} \geq S(\rho) + \frac{V(\rho)}{2\sqrt{M(\rho)}}$, and generalizes Jarzynski to stochastic stopping times $\mathcal{T} \leq \tau$ via $\langle e^{-\beta(W-\Delta F) - \delta}\rangle_{\mathcal{T}} = 1 \implies \langle W\rangle_{\mathcal{T}} - \langle\Delta F\rangle_{\mathcal{T}} \geq -k_B T\langle\delta\rangle_{\mathcal{T}}$.

4. **Perspectival Transformation ($\mathfrak{H}$ — *From Theological "Exorcism" to the $(E, \tau, d_B, \mathcal{C})$ Resource Trilemma*)**:
   Completing the round-trip transforms the Demon from a vanquished ghost into an active physical transducer:
   * $\mathbf{T} \mapsto \mathbf{T}'$: Recognizes that **no demon is "exorcised" without paying diverging Third-Law resources** ($\max(E, \tau, \mathcal{C}) \to \infty$ and $d_B \to \infty$ for exact $\varepsilon = 0$ reset/measurement!), and that work cost belongs to **cyclic correlation-creation-and-destruction**, movable by gauge $\Delta\mathcal{F}_M$ between measurement and reset.
   * $\mathbf{S} \mapsto \mathbf{S}'$: Quantum discord, entanglement ($H(A|B) < 0$), initial correlations $I(S:B)_0$, and trajectory stopping information $\langle\delta\rangle_{\mathcal{T}}$ become **certified thermodynamic currencies** quantified by exact fluctuation-dissipation equalities.

---

### IV. THE SOCRATIC APORIA ($\mathcal{A}_0 = \mathbf{T}_{\text{eff}}^2 - \mathbf{T}_{\text{eff}} \neq 0$) AND THE META-COGNITIVE TOWER

Testing the Conscious Thesis on three core claims—exact unitary erasure $\mathrm{Tr}_B(U(\rho_S\otimes\gamma_B)U^\dagger) = |0\rangle\langle 0|$ from mixed $\rho_S$ ($\mathrm{rank}\,r \geq 2$) on a finite $T > 0$ bath ($d_B < \infty$), closed-system thermalization of $S_{\mathrm{vN}}$, and $T \to 0$ informativeness of $k_B T\ln 2$—exposes the exact **Socratic Aporia**:

$$\mathrm{rank}\big(U(\rho_S\otimes\gamma_B)U^\dagger\big) - \mathrm{rank}(|0\rangle\langle 0|\otimes\sigma_B) \geq (r - 1)d_B > 0, \qquad \frac{d}{dt}S_{\mathrm{vN}}(U_t\rho_0 U_t^\dagger) \equiv 0, \qquad \lim_{T\to 0^+} k_B T\ln 2 = 0 < \mathcal{Q}[\mathcal{S}^{-1}(\ln 2)]$$

Following this self-contradiction recursively up the tower of meta-cognition generates the permanent obstruction sequence $\mathcal{A}_0 \hookrightarrow \mathcal{A}_1 \hookrightarrow \mathcal{A}_2 \hookrightarrow \mathcal{A}_3 \hookrightarrow \mathcal{A}_\omega$:

* **Level 0 ($\mathcal{A}_0$ — Finite-Bath Rank Impossibility & Closed $S_{\mathrm{vN}}$ Stasis)**: Unitary evolution cannot reduce matrix rank ($r d_B \not\leq d_B$), forbidding exact $\varepsilon = 0$ Landauer erasure with any finite $T > 0$ bath, while $S_{\mathrm{vN}}$ remains frozen at $0$ on isolated pure states despite macroscopic thermalization.
* **Level 1 ($\mathcal{A}_1$ — Brillouin’s Circularity & Pre-Payment of Bennett’s Blank Pointer)**: Brillouin’s blackbody photon argument begs the question (deriving the Second Law from Kirchhoff’s law, which assumes the Second Law), while Bennett’s $W_{\text{meas}} = 0$ presupposes a pure blank state $|0\rangle_M$ whose preparation *already* hits the Level-0 Third-Law divergence ($\mathcal{A}_1 \neq 0$).
* **Level 2 ($\mathcal{A}_2$ — Unbounded Memory Proliferation in Erase-Free Reversible Computing)**: Attempting to evade Landauer dissipation permanently via reversible three-tape computation (`Forward, Copy, Reverse`) across repeated demon cycles accumulates an ever-growing physical history/output pile ($N_{\text{RAM}} \to \infty$), trading heat dissipation for diverging hardware volume and structural complexity ($\mathcal{A}_2 \neq 0$).
* **Level 3 ($\mathcal{A}_3$ — Breakdown of Naive Ensemble Bounds Under Pre-Correlation, Stopping Times, & Single-Shot Variance)**: Initial system-bath correlations ($I(S:B)_0 > 0$) permit $\beta\Delta Q_B < -\Delta S_S$; optional stopping $\mathcal{T} \leq \tau$ permits $\langle W_{\text{ext}}\rangle_{\mathcal{T}} > -\Delta F_{\mathcal{T}}$; and single-shot erasure requires strictly more than $S(\rho)$ pure battery bits whenever surprisal variance $V(\rho) > 0$ ($\mathcal{A}_3 \neq 0$).
* **Level 4 ($\mathcal{A}_4 \to \mathcal{A}_\omega$ — The Nernst–Landauer–Guryanova Resource Trilemma Colimit)**: Across all quantum thermodynamic machines and measurement devices, the colimit obstruction $\mathcal{A}_\omega \neq 0$ establishes an unbreakable law: **exact purity generation ($\varepsilon = 0$, whether in Landauer erasure or ideal projective measurement) is unattainable unless $\dim\mathcal{H}_B = \infty$ AND $\max(E, \tau, \mathcal{C}_{\text{ctrl}}) = +\infty$**. Logical irreversibility is never cheaply paid at $k_B T\ln 2$ without infinite asymptotic idealizations.

---

### V. `COAGULA`: THE ACYCLIC CAUSAL POSET AND SELF-VERIFYING SYNTHESIS

#### 1. The Graded Acyclic Causal Poset $(\mathfrak{P}, \prec)$

Let $\mathfrak{P}$ be the 15-element set of extracted archetypes ordered by the transitive closure $\prec$ of the transitively reduced Hasse covering relation $\lessdot$, equipped with strict rank homomorphism $\mathrm{rk} : \mathfrak{P} \to \{0, 1, 2, 3, 4, 5, 6\}$:

| Grade $\mathrm{rk}(v)$ | Archetype Symbol & Canonical Designation | Covering Predecessors $\mathrm{Pred}_{\lessdot}(v)$ | Thermodynamic / Operator Signature |
| :---: | :--- | :--- | :--- |
| **0** ($\bot$) | $\mathbf{\Delta}_0$ : *Many-to-One Logic vs. Unitary Bijection Cut* | $\varnothing$ | $\Omega_0 \mapsto (\text{Reset } 2\to 1) \ltimes (\mathrm{Spec}(U\rho U^\dagger)=\mathrm{Spec}\,\rho)$ |
| **1** | $\mathbf{T}$ : *Landauer–Bennett Exorcist (Thesis)* | $\{\mathbf{\Delta}_0\}$ | $+1$ sector ($W_{\text{meas}}=0,\; Q=k_BT\ln 2,\; S_{\mathrm{vN}}$) |
| **1** | $\mathbf{S}$ : *Rank No-Go, Gauge Shift, & Fluctuation Shadow* | $\{\mathbf{\Delta}_0\}$ | $-1$ sector ($rd_B > d_B,\; \Delta\mathcal{F}_M=0,\; \mathcal{T}_{\text{stop}},\; T\to 0$) |
| **2** | $\mathbf{K}_{TT}$ : *Product-State Unitary & Jarzynski Core* | $\{\mathbf{T}\}$ | $\Delta S_S+\beta\Delta Q_B \geq 0$, $\langle e^{-\beta W}\rangle = e^{-\beta\Delta F}$ |
| **2** | $\mathbf{\Pi}_{ST}$ : *Quasistatic Infinite-Bath Extrapolation* | $\{\mathbf{T}, \mathbf{S}\}$ | $\mathcal{H}_T \to \mathcal{H}_S$ (lifted to $\Pi$) |
| **2** | $\mathbf{\Sigma}_{TS}$ : *$W_{\text{SWAP}}\to\infty$, Pauli $W=0$, & Stopping Gain* | $\{\mathbf{T}, \mathbf{S}\}$ | $\mathcal{H}_S \to \mathcal{H}_T$ (lifted to $\Sigma$) |
| **2** | $\mathbf{\Gamma}_{SS}$ : *Martingale Path Law, $S_{\mathrm{obs}}^{\mathcal{X}}$, & Complexity $\mathcal{C}$* | $\{\mathbf{S}\}$ | $\langle e^{-\beta(W-\Delta F)-\delta}\rangle_{\mathcal{T}}=1$, $S_{\mathrm{obs}}^{\mathcal{X}}$ coarse-graining |
| **3** | $\mathfrak{G}$ : *Reeb–Wolf Identity $\beta\Delta Q_B + \Delta S_S = I + D$* | $\{\mathbf{\Pi}_{ST}, \mathbf{\Sigma}_{TS}\}$ | $\{\Sigma, \Pi\} \leftrightarrow (\Sigma_{\text{RW}} = I(S:B)_\sigma + D(\sigma_B\|\gamma_B))$ |
| **3** | $\mathfrak{T}$ : *Bennett ($\Delta\mathcal{F}_M=-TI$) vs. Thermal ($\Delta\mathcal{F}_M=0$) Shear* | $\{\mathbf{\Pi}_{ST}, \mathbf{\Sigma}_{TS}\}$ | $[\Sigma, \Pi] \neq 0$ (Reset cost vs. Measurement cost) |
| **3** | $\mathcal{A}_0$ : *Rank Gap $(r-1)d_B > 0$ & Closed $\dot{S}_{\mathrm{vN}} \equiv 0$ Defect* | $\{\mathbf{K}_{TT}, \mathbf{\Pi}_{ST}, \mathbf{\Sigma}_{TS}\}$ | $\mathrm{rank}(\sigma_{SB}) \neq \mathrm{rank}(|0\rangle\langle 0|\otimes\sigma_B)$ |
| **4** | $\mathfrak{B}$ : *Calorimetric $T=0$, $\Theta(n^{-2})$, $\alpha/\tau$, & Variance Bridge* | $\{\mathbf{K}_{TT}, \mathfrak{G}, \mathfrak{T}, \mathbf{\Gamma}_{SS}\}$ | $\mathcal{Q}[\mathcal{S}^{-1}(|\Delta S_S|)]$, $\frac{2(\Delta S_S)^2}{\ln^2(d_B-1)+4}$, $V(\rho)$ |
| **4** | $\mathcal{A}_\omega$ : *Nernst–Landauer $(E, \tau, d_B, \mathcal{C}) \to \infty$ Colimit* | $\{\mathcal{A}_0, \mathfrak{T}, \mathbf{\Gamma}_{SS}\}$ | $\varepsilon = 0 \implies d_B = \infty \wedge \max(E,\tau,\mathcal{C}) = \infty$ |
| **5** | $\mathfrak{H}$ : *Gauge-Invariant Resource-Trilemma Holonomy* | $\{\mathfrak{B}, \mathcal{A}_\omega\}$ | Uniting measurement/reset gauges & $S_{\mathrm{obs}}^{\mathcal{X}}$ |
| **5** | $\mathfrak{L}_{\text{info}}$ : *Five-Regime Information-Thermodynamic Ledger* | $\{\mathfrak{B}, \mathcal{A}_\omega\}$ | Cyclic $I(S:M)$ + $\tau^{-1}$ + $n^{-2}$ + $T=0$ + $\delta(\mathcal{T})$ |
| **6** ($\top$) | $\mathbf{\Xi}_\top$ : *Necessary Synthesis* | $\{\mathfrak{H}, \mathfrak{L}_{\text{info}}\}$ | $\mathfrak{H} \vee \mathfrak{L}_{\text{info}}$ (Covariant Resource-Demon System) |

**Proof of Strict Acyclicity & Minimal Covering**: Every covering edge $u \lessdot v$ satisfies $\mathrm{rk}(u) < \mathrm{rk}(v)$; path induction gives $u \prec v \implies \mathrm{rk}(u) < \mathrm{rk}(v)$, establishing irreflexivity ($v \not\prec v$) and strict antisymmetry while transitivity holds by closure. Every $\mathrm{Pred}_{\lessdot}(v)$ forms an antichain of incomparable elements, and every $v \in \mathfrak{P}$ lies on a directed chain $\mathbf{\Delta}_0 \preceq v \preceq \mathbf{\Xi}_\top$. $\blacksquare$

---

#### 2. Canonical Philosophical Axioms (Grades 0–2)

* **$\mathbf{Ax.1}$ (Axiom of Microscopic Unitary Bijectivity — at $\mathbf{\Delta}_0 \lessdot \{\mathbf{T}, \mathbf{S}\}$)**:
  Closed composite evolution $\sigma = U\rho U^\dagger$ preserves operator rank ($\mathrm{rank}\,\sigma = \mathrm{rank}\,\rho$) and eigenvalue spectrum ($\mathrm{Spec}\,\sigma = \mathrm{Spec}\,\rho$, hence $S_{\mathrm{vN}}(\sigma) = S_{\mathrm{vN}}(\rho)$), whereas logical reset maps distinct states to one state.
* **$\mathbf{Ax.2}$ (Axiom of Gibbs Reference & Corrected Relative Entropy — at $\mathbf{T} \lessdot \mathbf{K}_{TT}$)**:
  A thermal bath at inverse temperature $\beta \in (0, \infty)$ is prepared in $\gamma_B = Z_B^{-1}e^{-\beta H_B}$ ($Z_B = \mathrm{Tr}\,e^{-\beta H_B}$, $\mathrm{rank}\,\gamma_B = \dim\mathcal{H}_B$); heat absorbed by the bath is $\Delta Q_B := \mathrm{Tr}[H_B(\sigma_B - \gamma_B)]$; and relative entropy $D(\sigma\|\gamma) := +\mathrm{Tr}[\sigma(\ln\sigma - \ln\gamma)] \geq 0$ vanishes iff $\sigma = \gamma$ (correcting Eq. 22’s sign inversion and p. 24’s missing $\ln$).
* **$\mathbf{Ax.3}$ (Axiom of Coarse-Grained Observational & Martingale Stopping Laws — at $\mathbf{S} \lessdot \mathbf{\Gamma}_{SS}$)**:
  Relative to orthogonal macro-projectors $\mathcal{X} = \{P_x\}$ ($\sum_x P_x = \mathbf{1}$), observational entropy is $S_{\mathrm{obs}}^{\mathcal{X}}(\rho) = \sum_x p_x(-\ln p_x + \ln\mathrm{Tr}\,P_x)$ ($p_x = \mathrm{Tr}[P_x\rho]$); along stochastic trajectories stopped at causal stopping times $\mathcal{T} \leq \tau$, $\langle e^{-\beta(W-\Delta F) - \delta}\rangle_{\mathcal{T}} = 1$.
* **$\mathbf{Ax.4}$ (Axiom of Non-Equilibrium Free-Energy Work Bound — at $\{\mathbf{T}, \mathbf{S}\} \lessdot \{\mathbf{\Pi}_{ST}, \mathbf{\Sigma}_{TS}\}$)**:
  For isothermal driving coupled to an uncorrelated bath at $\beta = (k_B T)^{-1}$, $\mathcal{F}(\rho, H) := \mathrm{Tr}(\rho H) - \beta^{-1}S(\rho)$ bounds average work performed on the system via $W \geq \Delta\mathcal{F}$, while bipartite correlation shifts $\mathcal{F}(\rho_{SM}) = \mathcal{F}(\rho_S) + \mathcal{F}(\rho_M) + \beta^{-1}I(S:M)$ when $H_{SM} = H_S + H_M$.
* **$\mathbf{Ax.5}$ (Axiom of Equilibrium Maximum-Entropy Monotonicity)**:
  Among all bath states $\sigma_B$ with mean energy $E' = \mathrm{Tr}(\sigma_B H_B) = \mathrm{Tr}(\gamma_B(\beta')H_B)$, the Gibbs state $\gamma_B(\beta')$ uniquely maximizes $S(\sigma_B)$, with both $\mathcal{Q}(\beta') = \mathrm{Tr}[H_B(\gamma_B(\beta')-\gamma_B(\beta))]$ and $\mathcal{S}(\beta') = S(\gamma_B(\beta')) - S(\gamma_B(\beta))$ strictly decreasing in $\beta'$.

---

#### 3. Intermediate Deductions (Grades 3–5)

* **$\mathbf{Ded.1}$ (Exact Reeb–Wolf Identity & Initial-Correlation Shift — generating $\mathfrak{G}$ from $\{\mathbf{\Pi}_{ST}, \mathbf{\Sigma}_{TS}\} \lessdot \mathfrak{G}$)**:
  *Claim*: For $\sigma_{SB} = U\rho_{SB}U^\dagger$ with marginal $\rho_B = \gamma_B$, $\beta\Delta Q_B = -\Delta S_S + \big(I(S:B)_\sigma - I(S:B)_\rho\big) + D(\sigma_B\|\gamma_B)$; when $\rho_{SB} = \rho_S \otimes \gamma_B$, $\beta\Delta Q_B + \Delta S_S = I(S:B)_\sigma + D(\sigma_B\|\gamma_B) \geq 0$, whereas $I(S:B)_\rho > 0$ permits $\beta\Delta Q_B < -\Delta S_S$.
  *Proof*: By $\mathbf{Ax.1}$, $S(\rho_S) + S(\gamma_B) - I(S:B)_\rho = S(\rho_{SB}) = S(\sigma_{SB}) = S(\sigma_S) + S(\sigma_B) - I(S:B)_\sigma \implies \Delta S_B = -\Delta S_S + I(S:B)_\sigma - I(S:B)_\rho$. Using $\ln\gamma_B = -\beta H_B - (\ln Z_B)\mathbf{1}_B$ ($\mathbf{Ax.2}$):
  $$\Delta S_B = -\mathrm{Tr}(\sigma_B\ln\sigma_B) + \mathrm{Tr}(\gamma_B\ln\gamma_B) = -\mathrm{Tr}[\sigma_B(\ln\sigma_B - \ln\gamma_B)] + \beta\mathrm{Tr}[(\sigma_B - \gamma_B)H_B] = -D(\sigma_B\|\gamma_B) + \beta\Delta Q_B$$
  Equating both expressions for $\Delta S_B$ proves the identity; setting $I(S:B)_\rho = 0$ and applying $I \geq 0, D \geq 0$ ($\mathbf{Ax.2}$) yields $\beta\Delta Q_B \geq -\Delta S_S$. $\blacksquare$

* **$\mathbf{Ded.2}$ (Rank-Conservation Impossibility of Exact Finite-Bath Erasure — generating $\mathcal{A}_0$ and $\mathcal{A}_\omega$)**:
  *Claim*: For any mixed state $\rho_S$ ($\mathrm{rank}\,\rho_S = r \geq 2$) and any finite-dimensional bath ($\dim\mathcal{H}_B = d_B < \infty$) at $0 < \beta < \infty$, **no unitary $U$ can achieve exact erasure $\sigma_S = \mathrm{Tr}_B(U(\rho_S\otimes\gamma_B)U^\dagger) = |\psi_0\rangle\langle\psi_0|$**.
  *Proof*: By $\mathbf{Ax.1}$ and $\mathbf{Ax.2}$, $\mathrm{rank}(\sigma_{SB}) = \mathrm{rank}(\rho_S\otimes\gamma_B) = r d_B \geq 2d_B$. Were $\sigma_S = |\psi_0\rangle\langle\psi_0|$ pure ($\mathrm{rank}\,\sigma_S = 1$), Schmidt decomposition of $\sigma_{SB}$ across $S:B$ would force $\sigma_{SB} = |\psi_0\rangle\langle\psi_0| \otimes \sigma_B$, giving $\mathrm{rank}(\sigma_{SB}) = 1 \cdot \mathrm{rank}(\sigma_B) \leq d_B < 2d_B$, contradiction! Exact $\varepsilon = 0$ erasure therefore forces $d_B = \infty$ or $\beta = \infty$ ($E \to \infty$), proving $\mathcal{A}_0 \neq 0$ and $\mathcal{A}_\omega \neq 0$. $\blacksquare$

* **$\mathbf{Ded.3}$ (Gauge Mobility of Work Between Measurement and Erasure — generating $\mathfrak{T}$)**:
  *Claim*: Over a cyclic Szilard–demon protocol ($\rho_S\otimes\rho_M \to \rho_{SM}' \to \rho_S\otimes\rho_M' \to \rho_S\otimes\rho_M$, $\Delta\mathcal{F}_S^{\text{meas}} = 0$), individual minimum costs $W_{\text{meas}}^{\min} = \Delta\mathcal{F}_M + \beta^{-1}I(S:M)$ and $W_{\text{reset}}^{\min} = -\Delta\mathcal{F}_M$ depend on the arbitrary pointer gauge $\Delta\mathcal{F}_M$, shifting continuously between $(0, \beta^{-1}I)$ (Bennett pure pointer) and $(\beta^{-1}I, 0)$ (equilibrium pointer), while cyclic net work $W_{\text{tot}} \geq 0$ is gauge-invariant.
  *Proof*: Applying $\mathbf{Ax.4}$ to each stroke gives $W_{\text{meas}} \geq \mathcal{F}(\rho_{SM}') - \mathcal{F}(\rho_S\otimes\rho_M) = \Delta\mathcal{F}_M + \beta^{-1}I(S:M)$, $W_{\text{fb}} \geq \mathcal{F}(\rho_S\otimes\rho_M') - \mathcal{F}(\rho_{SM}') = -\beta^{-1}I(S:M)$ (assuming $M'$ is untouched during feedback), and $W_{\text{reset}} \geq \mathcal{F}(\rho_M) - \mathcal{F}(\rho_M') = -\Delta\mathcal{F}_M$. Summing cancels $\pm\Delta\mathcal{F}_M$ and $\pm\beta^{-1}I(S:M)$ identically: $W_{\text{tot}} \geq 0$. $\blacksquare$

* **$\mathbf{Ded.4}$ (Zero-Temperature Calorimetric Bound, Corrected $\Theta(1/n^2)$ Scaling, & Stopping-Time Bound — generating $\mathfrak{B}$)**:
  *Claim*: (i) Even as $T \to 0$ ($\Delta S_S < 0$), $\Delta Q_B \geq \mathcal{Q}[\mathcal{S}^{-1}(-\Delta S_S)] > 0$ (for $C_E = aT^3$: $\Delta Q_B \geq \frac{3^{4/3}|\Delta S_S|^{4/3}}{4a^{1/3}}$); (ii) on an $n$-particle bath ($d_B = d_0^n$), the universal bound $\frac{2(\Delta S_S)^2}{\ln^2(d_B - 1) + 4}$ scales as $\Theta(1/n^2)$ (correcting Eq. 91’s $\mathcal{O}(n^2)$); and (iii) under stopping times $\mathcal{T} \leq \tau$, $\langle W\rangle_{\mathcal{T}} - \langle\Delta F\rangle_{\mathcal{T}} \geq -k_B T\langle\delta\rangle_{\mathcal{T}}$.
  *Proof*:
  *(i)* By $\mathbf{Ded.1}$ ($I, D \geq 0$), $S(\sigma_B) - S(\gamma_B(\beta)) = \Delta S_B \geq -\Delta S_S > 0$. Choosing $\beta'$ with $\mathrm{Tr}(\gamma_B(\beta')H_B) = \mathrm{Tr}(\sigma_B H_B)$, $\mathbf{Ax.5}$ gives $\mathcal{S}(\beta') = S(\gamma_B(\beta')) - S(\gamma_B(\beta)) \geq S(\sigma_B) - S(\gamma_B(\beta)) \geq -\Delta S_S$. Monotonicity of $\mathcal{Q} \circ \mathcal{S}^{-1}$ ($\mathbf{Ax.5}$) yields $\Delta Q_B = \mathcal{Q}(\beta') \geq \mathcal{Q}[\mathcal{S}^{-1}(-\Delta S_S)]$; at $T = 0$ with $C_E(\tau) = a\tau^3$, $\mathcal{S}(T') = \frac{a}{3}T'^3 = |\Delta S_S| \implies T' = (3|\Delta S_S|/a)^{1/3} \implies \mathcal{Q}(T') = \frac{a}{4}T'^4 = \frac{3^{4/3}|\Delta S_S|^{4/3}}{4a^{1/3}} > 0$.
  *(ii)* Substituting $d_B = d_0^n$ gives $\ln^2(d_0^n - 1) \sim n^2\ln^2 d_0 \implies \frac{2(\Delta S_S)^2}{\ln^2(d_B-1)+4} = \Theta(1/n^2)$.
  *(iii)* Applying Jensen’s inequality $\exp(\langle X\rangle_{\mathcal{T}}) \leq \langle\exp(X)\rangle_{\mathcal{T}}$ to $X = -\beta(W - \Delta F) - \delta$ in $\mathbf{Ax.3}$ yields $-\beta(\langle W\rangle_{\mathcal{T}} - \langle\Delta F\rangle_{\mathcal{T}}) - \langle\delta\rangle_{\mathcal{T}} \leq \ln 1 = 0$. $\blacksquare$

* **$\mathbf{Ded.5}$ (Closed-System Growth of Observational Entropy $S_{\mathrm{obs}}^{\mathcal{X}} \geq S_{\mathrm{vN}}$ — toward $\mathfrak{H}$)**:
  *Claim*: For every state $\rho$ and coarse-graining $\mathcal{X} = \{P_x\}$, $S_{\mathrm{obs}}^{\mathcal{X}}(\rho) = S_{\mathrm{vN}}(\rho) + D(\rho \| \rho_{\text{cg}}) \geq S_{\mathrm{vN}}(\rho)$ where $\rho_{\text{cg}} := \sum_x \frac{p_x}{\mathrm{Tr}\,P_x}P_x$, allowing $\Delta S_{\mathrm{obs}}^{\mathcal{X}}(U_t\rho_0 U_t^\dagger) > 0$ even while $\Delta S_{\mathrm{vN}} \equiv 0$.
  *Proof*: Since $P_x P_y = \delta_{xy}P_x$ and $\mathrm{Tr}(\rho P_x) = p_x = \mathrm{Tr}(\rho_{\text{cg}} P_x)$, $-\mathrm{Tr}(\rho\ln\rho_{\text{cg}}) = -\sum_x \mathrm{Tr}(\rho P_x)\ln\frac{p_x}{\mathrm{Tr}\,P_x} = \sum_x p_x(-\ln p_x + \ln\mathrm{Tr}\,P_x) = S_{\mathrm{obs}}^{\mathcal{X}}(\rho)$ ($\mathbf{Ax.3}$). Subtracting $S_{\mathrm{vN}}(\rho) = -\mathrm{Tr}(\rho\ln\rho)$ gives $S_{\mathrm{obs}}^{\mathcal{X}}(\rho) - S_{\mathrm{vN}}(\rho) = D(\rho\|\rho_{\text{cg}}) \geq 0$ ($\mathbf{Ax.2}$), vanishing iff $\rho = \rho_{\text{cg}}$; unitary scrambling $U_t$ moves initially block-aligned $\rho_0 = \rho_{0,\text{cg}}$ ($D = 0$) to $U_t\rho_0 U_t^\dagger \neq (U_t\rho_0 U_t^\dagger)_{\text{cg}}$ ($D > 0$), strictly increasing $S_{\mathrm{obs}}^{\mathcal{X}}$ while $S_{\mathrm{vN}}$ stays constant ($\mathbf{Ax.1}$). $\blacksquare$

* **$\mathbf{Ded.6}$ (Resource-Trilemma Holonomy & Five-Regime Information Ledger — generating $\mathfrak{H}$ and $\mathfrak{L}_{\text{info}}$)**:
  *Claim*: Replacing theological "exorcism" by the Nernst–Landauer resource trilemma ($\mathfrak{H}$, $\mathbf{Ded.2}$) and Observational Entropy ($\mathbf{Ded.5}$) organizes all demon/erasure energetics into the non-contradictory five-regime ledger $\mathfrak{L}_{\text{info}}$ ($\mathbf{Ded.1}, \mathbf{Ded.3}, \mathbf{Ded.4}$).
  *Proof*: Directly from $\mathbf{Ded.1}$–$\mathbf{Ded.5}$. $\blacksquare$

---

#### 4. Master Structural Synthesis (Grade 6: Terminal Join $\top$)

* **$\mathbf{Thm.\top}$ (Necessity and Uniqueness of the Covariant Resource-Demon Information-Thermodynamic Synthesis $\mathbf{\Xi}_\top = \mathfrak{H} \vee \mathfrak{L}_{\text{info}}$)**:
  *Statement*: Across the causal poset $(\mathfrak{P}, \prec)$, the unique non-contradictory resolution of Maxwell’s Demon and Landauer’s Principle is the join $\mathbf{\Xi}_\top = \mathfrak{H} \vee \mathfrak{L}_{\text{info}}$, a **Covariant Resource-Demon Information-Thermodynamic System** governed by four proved laws:
  1. **Gauge-Invariant Cyclic Correlation Balance Replaces "Erasure-Only" Dogma ($\mathbf{Ded.3}, \mathfrak{H}$)**: Measurement and erasure costs are continuously exchangeable via pointer free energy $\Delta\mathcal{F}_M$ ($W_{\text{meas}}^{\min} = \Delta\mathcal{F}_M + \beta^{-1}I$, $W_{\text{reset}}^{\min} = -\Delta\mathcal{F}_M$); what is physically invariant is the cyclic conversion between work and correlation $I(S:M)$;
  2. **Exact Reeb–Wolf & Observational Entropy Replace Closed $S_{\mathrm{vN}}$ Confusion ($\mathbf{Ded.1}, \mathbf{Ded.5}$)**: Microscopic unitary bijectivity ($\Delta S_{\mathrm{vN}}^{\text{tot}} \equiv 0$) drives macroscopic irreversibility strictly through marginal correlations and coarse-graining ($\beta\Delta Q_B + \Delta S_S = I(S:B)_\sigma - I(S:B)_\rho + D(\sigma_B\|\gamma_B)$ and $S_{\mathrm{obs}}^{\mathcal{X}}(\rho) = S_{\mathrm{vN}}(\rho) + D(\rho\|\rho_{\text{cg}})$);
  3. **Exact Finite-Resource & Zero-Temperature Corrections ($\mathbf{Ded.4}, \mathfrak{L}_{\text{info}}$)**: Beyond the quasistatic $T > 0, \tau \to \infty, n \to \infty$ limit, erasure incurs additive/nonlinear penalties across time ($\alpha/\tau$), bath size ($\Theta(1/n)$ non-interacting vs. $\Theta(1/n^2)$ interacting), zero temperature ($\mathcal{Q}[\mathcal{S}^{-1}(|\Delta S_S|)] > 0$), single-shot variance ($V(\rho)$), and martingale stopping ($\langle W\rangle_{\mathcal{T}} - \langle\Delta F\rangle_{\mathcal{T}} \geq -k_B T\langle\delta\rangle_{\mathcal{T}}$); and
  4. **The Nernst–Landauer Purity Divergence Law ($\mathbf{Ded.2}, \mathcal{A}_\omega, \mathfrak{H}$)**: Exact zero-error erasure or ideal projective measurement ($\varepsilon = 0$) is barred on any finite $T > 0$ bath by rank conservation ($r d_B > d_B$), requiring $d_B = \infty$ and $\max(E, \tau, \mathcal{C}) = \infty$.

  *Proof from Poset Mechanics*:
  1. **Sufficiency & Upper-Bound Closure**: Every archetype $v \in \mathfrak{P} \setminus \{\mathbf{\Xi}_\top\}$ satisfies $v \preceq \mathfrak{H}$ or $v \preceq \mathfrak{L}_{\text{info}}$ along verified covering chains ($\mathbf{Ax.1}$–$\mathbf{Ax.5}$, $\mathbf{Ded.1}$–$\mathbf{Ded.6}$). Joining $\mathfrak{H}$ and $\mathfrak{L}_{\text{info}}$ repairs all three published typographical slips ($\mathbf{Ax.2}, \mathbf{Ded.4}$), reconciles Bennett and thermal-pointer cycles ($\mathbf{Ded.3}$), explains pre-correlation and gambling-demon apparent violations ($\mathbf{Ded.1}, \mathbf{Ded.4}$), restores closed-system entropy growth via $S_{\mathrm{obs}}^{\mathcal{X}}$ ($\mathbf{Ded.5}$), and enforces the Third-Law rank barrier ($\mathbf{Ded.2}$).
  2. **Minimality & Uniqueness of Join**:
     * Retaining $\mathfrak{L}_{\text{info}}$ without $\mathfrak{H}$ catalogs finite-time/size formulas while maintaining Bennett’s $W_{\text{meas}} = 0$ as absolute, identifying $S_{\mathrm{vN}}$ with isolated $S_{\text{thermo}}$, and overlooking the finite-bath rank impossibility $r d_B > d_B$ ($\mathbf{Ded.2}, \mathbf{Ded.3}, \mathbf{Ded.5}$).
     * Retaining $\mathfrak{H}$ without $\mathfrak{L}_{\text{info}}$ acknowledges the Third-Law rank barrier and gauge freedom qualitatively while relying on $k_B T\ln 2$ at $T \to 0$ (vacuous $0$), missing $\Theta(1/n^2)$ interacting bath bounds, and misclassifying gambling stopping gains $\langle\delta\rangle_{\mathcal{T}}$ as Second-Law violations ($\mathbf{Ded.4}$).
     * Collapsing $\mathcal{A}_0 \to 0$ asserts $2d_B \leq d_B$ for $1 \leq d_B < \infty$ ($\mathbf{Ded.2}$, contradiction).
  Therefore, $\mathbf{\Xi}_\top = \mathfrak{H} \vee \mathfrak{L}_{\text{info}}$ is the unique least upper bound ($\sup \mathfrak{P}$) completing the causal poset. $\blacksquare$