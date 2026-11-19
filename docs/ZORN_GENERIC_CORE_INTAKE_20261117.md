### PHASE 0 — `SOLVE`: ELENCTIC DISSOLUTION INTO IRREDUCIBLE PRIMITIVES

Stripping away PR numbers, Git commit hashes, GitHub Actions URLs, and status boilerplate exposes a high-precision epistemic event: **translating informal physics papers and speculative prose into exact algebraic types forces hidden mathematical contradictions out into the open—even prior to final compiler lock**. Executing Socratic elenchus across the PR #382 cosmological formalization, the PR #384 Zorn-associator formalization, and the repository’s reusable interfaces dissolves five exact confabulations between *intended narrative claims* and *actual mathematical consequences*:

1. **Three Cosmological Narrative-vs.-Formula Contradictions (PR #382)**:
   * *Radiation Mistaken for Pressureless Dust*: For the rank-1 gradient stress tensor $T_{\mu\nu} = \lambda\big(v_\mu v_\nu - \frac{1}{2}\eta_{\mu\nu}\eta^{\alpha\beta}v_\alpha v_\beta\big)$ in signature $(-+++)$ ($\eta^{\alpha\beta}v_\alpha v_\beta = -u^2 + q$), energy density is $\rho = \frac{\lambda}{2}(u^2 + q)$ and mean spatial stress is $\bar{p} = \frac{\lambda}{2}u^2 - \frac{\lambda}{6}q$, satisfying $3\bar{p} - \rho = \lambda(u^2 - q)$. Thus null equipartition $q = u^2$ yields **relativistic radiation ($3\bar{p} = \rho$), not dark-matter dust**, while dust ($\bar{p} = 0$) requires spacelike $q = 3u^2$, and anisotropic dyads $v_i v_j$ fail to commute or define an isotropic pressure without ensemble averaging.
   * *Double-Counted Entropic Source Residual ($-3H\lambda\Gamma \neq 0$)*: Differentiating $\rho = \frac{\lambda}{2}u^2$ along $u' + 3Hu = \Gamma$ yields $\rho' + 6H\rho = \lambda u\Gamma$ (stiff pressure $p_{\text{kin}} = +\rho$ with source $\lambda u\Gamma$). Simultaneously inserting a modified pressure $p = \rho - \lambda\Gamma$ *while retaining* $\lambda u\Gamma$ on the right-hand side violates energy balance by $\rho' + 3H(\rho + p) - \lambda u\Gamma = -3H\lambda\Gamma \neq 0$.
   * *Singular $1/r$ Cusp Mistaken for a Cored Halo*: Simplifying the printed halo mass interpolation to $M(r) = \frac{2\eta s r^2}{r + s} = O(r^2)$ ($r \to 0^+$) forces $\rho(r) = \frac{M'(r)}{4\pi r^2} = \frac{\eta s(r + 2s)}{2\pi r(r + s)^2} \sim \frac{\eta}{\pi r} \to +\infty$: **an NFW-like $1/r$ central cusp divergence, never a finite central core** (which requires $M(r) = O(r^3)$).
2. **Nucleus ($\mathbb{R}\cdot\mathbf{1}$) vs. Associative Subalgebra ($\mathbb{H}$) in the Ambient Zorn Gram Form (PR #384)**:
   Summing the squared associator $\mathcal{G}_{\text{amb}}(X, X) = \sum_{i,j \in I_8} B_+([X, e_i, e_j], [X, e_i, e_j])$ over **all $64$ ambient basis pairs** of Zorn’s split-octonion algebra $Z = \mathbb{O}_s$ tests whether $X$ associates with *the entire octonion algebra*—selecting the **1D scalar nucleus** $\mathrm{Nuc}(\mathbb{O}_s) = \mathbb{R}\cdot\mathbf{1}$, **not** a 4D quaternion subalgebra $\mathbb{H} \subset \mathbb{O}_s$ ($\mathcal{G}_{\text{amb}}(i, i) > 0$ because $e_i, e_j$ probe cross-octonionic modes $[i, j, \ell] \neq 0$!). Vanishing on an associative subregister $\mathcal{S} \cong \mathbb{H}$ holds *only* when the probing basis pairs $(e_i, e_j)$ are projected onto $\mathcal{S}$ as well.
3. **The Injective-Symplectic GENERIC No-Go ($\ker L = \{0\} \implies dS = 0$)**:
   On any non-degenerate symplectic manifold $(M, \omega)$ (such as Para-Kähler $S^+ \times S^-$ with $|\det(\partial_+\partial_-\Psi)| = e^\sigma > 0$), the reversible Poisson operator $L = \omega^{-1} : T^*M \to TM$ is **injective** ($\ker L = \{0\}$). Enforcing the strong GENERIC/metriplectic Casimir condition $L(dS) = 0$ immediately forces **$dS = 0 \implies M(dS) = 0$ (identically zero entropy production!)**. Non-zero dissipation requires a **degenerate** reversible Poisson operator ($\ker L \neq \{0\}$).
4. **Singular Null-Current Spinors & Pointwise QFT Energy Negativity**:
   Non-zero even spinors $\psi \in \mathcal{K}_{4,4}$ with $\Omega_1 = \Omega_2 = 0$ (e.g., $\psi = \mathbf{1} + \sigma_1$, Lounesto singular flagpole/Weyl spinors) generate **null/lightlike currents** $J(\psi)^2 = (\Omega_1^2 + \Omega_2^2)\mathbf{1} = 0$ (rather than timelike $J^2 > 0$), while second-quantized Fock positivity $H = \int :T^{00}: d^3x \geq 0$ still admits locally negative pointwise densities $:T^{00}(x): < 0$ bounded only by Quantum Energy Inequalities.
5. **Pre-Commit Source Audit vs. Completed Kernel Acceptance**:
   Matching local/remote Git trees and passing static vacuity/placeholder gates remains strictly distinct from completed Lean kernel compilation and axiom verification (`queued CI`, shared local build lock, open root integration).

Dissolving these confabulations yields **six irreducible real conceptual primitives**:

* $\mathcal{V}_{\text{lock}}$ (**Kernel-Compilation Gate**): The strict epistemic boundary separating reviewed candidate ASTs from compiler-certified theorems.
* $(T_{\mu\nu}^{\text{grad}}, p_{\text{eff}}, \alpha_{\text{halo}})$ (**Exact Cosmological Balance Triad**): Rank-1 gradient stress ($3\bar{p} - \rho = \lambda(u^2 - q)$), exact effective pressure $p_{\text{eff}} = \rho - \frac{\lambda u\Gamma}{3H}$, and mass-scaling exponent $M(r) \sim r^\alpha \implies \rho(r) \sim r^{\alpha - 3}$.
* $\mathcal{G}_{\text{amb}}$ vs. $\mathcal{G}_{\mathcal{S}}$ (**Nucleus vs. Subregister Associator Gram Bilinear Forms**): Ambient 64-pair probe ($\ker = \mathbb{R}\cdot\mathbf{1}$) versus channel-projected probe ($\ker = \mathcal{S} \cong \mathbb{H}$).
* $\widetilde{L} = \omega^{-1} \oplus 0_S$ (**Corank-1 Extended GENERIC Poisson Operator**): Degenerate reversible structure on $M \times \mathbb{R}_S$ ($\ker\widetilde{L} = \mathrm{Span}\{dS\} \neq \{0\}$) unlocking non-zero entropy covectors.
* $\widetilde{M}_{\text{GENERIC}}(D)$ (**Denominator-Free Energy-Conserving Friction Matrix**): Coupled $(2n+1)\times(2n+1)$ positive-semidefinite operator satisfying $\widetilde{M}(d\widetilde{H}) \equiv 0$ and $\dot{S} \geq 0$ even at critical points $dH_0 = 0$.
* $\mathcal{K}_{4,4}^{\text{reg}} \sqcup \mathcal{K}_{4,4}^{\text{sing}}$ (**Regular Timelike vs. Singular Lightlike Spinor Partition**): Partitioning $\psi \neq 0$ by $\Omega_1^2 + \Omega_2^2 > 0$ ($J^2 > 0$) versus $\Omega_1 = \Omega_2 = 0$ ($J^2 = 0, J \neq 0$).

---

### I. THE FUNDAMENTAL BINARY CUT ($\mathbf{\Delta}_0 : \Omega_0 \longrightarrow \mathbf{T} \ltimes \mathbf{S}$)

The cut $\mathbf{\Delta}_0$ splits the formalization program across $\mathcal{H}_T \oplus \mathcal{H}_S$ into an asymmetric, non-reversible opposition:

1. **The Conscious Thesis ($\mathbf{T}$ — *Narrative Paper & Prose Intended Semantics*)**:
   The informal theoretical narrative asserting that rank-1 entropic gradients mimic pressureless dust at $q = u^2$ with conserved pressure $p = \rho - \lambda\Gamma$ and cored $r^2/(r+s)$ halos, while ambient Zorn Gram forms vanish on quaternion subalgebras and non-degenerate Para-Kähler symplectic manifolds directly support GENERIC entropy growth.
2. **The Repressed Shadow Complement ($\mathbf{S}$ — *Literal Symbolic Consequences & Degeneracy Constraints*)**:
   Everything uncovered the instant those prose assertions are compiled into literal symbolic definitions:
   * *Cosmological & spinor shadow*: Radiation $3\bar{p} = \rho$ at $q = u^2$, conservation error $-3H\lambda\Gamma \neq 0$, singular $1/r$ halo density cusps, Lounesto null-current spinors ($J^2 = 0$), and local QFT negative energy densities.
   * *Algebraic & verification shadow*: Strict positivity $\mathcal{G}_{\text{amb}}(i, i) > 0$ outside the 1D scalar nucleus, vanishing of GENERIC entropy covectors whenever $L$ is injective, and the pending status of queued CI kernel runs.

**Strict Non-Commutative Asymmetry**:
* *Computing derivatives, kernels, and limits FIRST from the literal formula and THEN assigning physical names* ($\mathrm{Formula} \prec \mathrm{Derive} \prec \mathrm{Interpret}$, the method of PR #382 and PR #384!) catches $-3H\lambda\Gamma$, $1/r$ cusps, and $\mathcal{G}_{\text{amb}}(i,i) > 0$;
* *Assigning physical interpretations FIRST ("dust," "cored halo," "quaternion kernel") and assuming the formulas obey them* ($\mathrm{Interpret} \prec \mathrm{Assume}$) entrenches false implications in published literature.

---

### II. THE FOURFOLD RELATIONAL ANATOMY

Across Audited Candidate Definitions ($\mathcal{H}_T$) and Unconstructed Dynamical/Analytical Closures ($\mathcal{H}_S$), the split epistemic operator $\mathcal{M}_{\text{ep}} = \begin{pmatrix} \mathbf{K}_{TT} & \mathbf{\Sigma}_{TS} \\ \mathbf{\Pi}_{ST} & \mathbf{\Gamma}_{SS} \end{pmatrix}$ isolates four mechanics:

1. **Internal Self-Consistency ($\mathbf{K}_{TT} : \mathcal{H}_T \to \mathcal{H}_T$ — *Exact Algebraic & Differential Candidate Ledger*)**:
   Within their explicit types, the PR #382 and PR #384 modules establish exact, placeholder-free deductive chains: full $4\times 4$ noncommuting scalar-stress matrices, `HasDerivAt` kinetic balance, exact $r \to 0^+$ and $r \to \infty$ density asymptotics, and the 64-pair `LinearMap.BilinForm ℝ Z` proving $\mathcal{G}_{\text{amb}}(X, X) = 0 \iff X \in \mathbb{R}\cdot\mathbf{1}$ alongside existing fixed-$\gamma_0$ positivity and injective-$L$ GENERIC theorems ($\mathbf{K}_{TT}^2 = \mathbf{K}_{TT}$).
2. **Outward Projection ($\mathbf{\Pi}_{ST} : \mathcal{H}_T \to \mathcal{H}_S$ — *Premature Extrapolation of Prose & Paper Claims*)**:
   Informal prose projects single-subalgebra associativity onto ambient 64-pair sums, projects non-degenerate symplectic forms onto GENERIC dissipation without adding degenerate coordinates, and projects isotropic fluid behavior onto rank-1 $v_\mu v_\nu$ tensors.
3. **Inward Shadow-Intrusion ($\mathbf{\Sigma}_{TS} : \mathcal{H}_S \to \mathcal{H}_T$ — *Counterexample & Residual Refutation*)**:
   Formal proof obligations strike back into $\mathcal{H}_T$: the quaternion counterexample $\mathcal{G}_{\text{amb}}(i, i) > 0$ refutes subalgebra vanishing of $\mathcal{G}_{\text{amb}}$; $\ker L = \{0\} \implies dS = 0$ blocks naive symplectic GENERIC; $-3H\lambda\Gamma \neq 0$ and $\rho(r) \sim \frac{\eta}{\pi r}$ refute the cosmological paper’s prose; and $\psi = \mathbf{1} + \sigma_1$ exhibits $J(\psi)^2 = 0$.
4. **Autonomous Unexamined Ground ($\mathbf{\Gamma}_{SS} : \mathcal{H}_S \to \mathcal{H}_S$ — *Degenerate Thermodynamic Phase Space, Subregister Projectors, & CI Build Locks*)**:
   The autonomous mathematical and infrastructural reality still awaiting construction: corank-1 contact/thermodynamic phase spaces $M \times \mathbb{R}_S$, channel-projected Zorn Gram forms $\mathcal{G}_{\mathcal{S}}$, $4+4$ curved Monge–Ampère PDEs, moving-observer Cauchy conservation, and physical execution of the queued Lean 4 compiler jobs.

---

### III. IGNITION OF THE TRANSCENDENT FUNCTION

Pairing $\Pi = \begin{pmatrix} 0 & 0 \\ \mathbf{\Pi}_{ST} & 0 \end{pmatrix}$ and $\Sigma = \begin{pmatrix} 0 & \mathbf{\Sigma}_{TS} \\ 0 & 0 \end{pmatrix}$ over $\mathbb{R}$ ignites the four moments resolving every open mathematical gap flagged in PR #382 and PR #384:

1. **Shared Substantive Gravity ($\mathfrak{G} = \{\Sigma, \Pi\}$ — *Kernel-Exactness & Counterexample-Driven Specification*)**:
   Both the prose synthesis and the PR #382/#384 formalizations converge on one governing invariant: **quadratic positivity paired with exact kernel characterization**—identifying precisely *which* subspace is annihilated ($\ker\mathcal{G}_{\text{amb}} = \mathbb{R}\cdot\mathbf{1}$, $\ker L$, $\Omega_1^2 + \Omega_2^2 = 0$, $3\bar{p} - \rho = 0$) rather than relying on verbal analogies.

2. **Directional Tension ($\mathfrak{T} = [\Sigma, \Pi] \neq 0$ — *Ambient Nucleus $\mathbb{R}\cdot\mathbf{1}$ vs. Channel Subregister $\mathbb{H}$, and Injective $\omega^{-1}$ vs. Degenerate $\widetilde{L}$*)**:
   Two sharp structural dualities separate trivialization from active dynamics ($\Sigma\Pi \neq \Pi\Sigma$):
   * **Ambient vs. Projected Associator Probe**: Probing $X$ against *all* $e_i, e_j \in \mathbb{O}_s$ ($\mathcal{G}_{\text{amb}}$) isolates the **1D Nucleus** $\mathbb{R}\cdot\mathbf{1}$ ($\mathcal{G}_{\text{amb}}(i, i) > 0$); probing $X$ against **projected subregister pairs** $P_{\mathbb{H}}e_i, P_{\mathbb{H}}e_j \in \mathbb{H}$ ($\mathcal{G}_{\mathbb{H}}$) isolates the **4D Associative Quaternion Register $\mathbb{H}$** ($\ker\mathcal{G}_{\mathbb{H}} = \mathbb{H}$)!
   * **Symplectic Injectivity vs. GENERIC Degeneracy**: Non-degenerate $L = \omega^{-1}$ ($\ker L = \{0\}$) enforces pure conservative mechanics ($dS = 0$); extending $M \to M \times \mathbb{R}_S$ with $\widetilde{L} = \omega^{-1} \oplus 0_S$ ($\ker\widetilde{L} = \mathrm{Span}\{dS\}$) unlocks irreversible GENERIC entropy growth!

3. **Integrative Bridge ($\mathfrak{B}$ — *Lean-Ready Upgrades for PR #384, GENERIC Degeneracy, & Cosmological Repairs*)**:
   Supplies the exact, polynomial, division-free mathematical constructions needed to discharge the open implications documented in PR #382 and PR #384:
   * *Bridge 1 — Exact Quaternion-Kernel Zorn Gram Form (Complementing `ZornAssociatorGram.lean`)*:
     Alongside PR #384’s ambient $\mathcal{G}_{\text{amb}}$ ($\ker\mathcal{G}_{\text{amb}} = \mathbb{R}\cdot\mathbf{1}$), let $P_{\mathbb{H}} : \mathbb{O}_s \to \mathbb{H}$ project onto the embedded quaternion subalgebra $\mathbb{H} = \mathrm{Span}_{\mathbb{R}}\{\mathbf{1}, i, j, k\} \subset \mathbb{O}_s = \mathbb{H} \oplus \mathbb{H}\ell$, and define the **Subregister-Projected Gram Form**:
     $$\mathcal{G}_{\mathbb{H}}(X, Y) := \sum_{a,b \in I_8} B_+\!\big([X, P_{\mathbb{H}}e_a, P_{\mathbb{H}}e_b],\; [Y, P_{\mathbb{H}}e_a, P_{\mathbb{H}}e_b]\big)$$
     For $X = q_0 + q_1\ell$ ($q_0, q_1 \in \mathbb{H}$), associativity of $\mathbb{H}$ gives $[q_0, P_{\mathbb{H}}e_a, P_{\mathbb{H}}e_b] = 0$, while testing $(P_{\mathbb{H}}e_a, P_{\mathbb{H}}e_b) = (i, j)$ gives $[q_1\ell, i, j] = 2(q_1 k)\ell$; invertibility of $k \in \mathbb{H}^\times$ proves **$\mathcal{G}_{\mathbb{H}}(X, X) = 0 \iff q_1 = 0 \iff X \in \mathbb{H}$**! Thus $\mathcal{G}_{\text{amb}}$ characterizes the 1D scalar nucleus while $\mathcal{G}_{\mathbb{H}}$ characterizes the 4D associative quaternion register!
   * *Bridge 2 — Exact Degenerate GENERIC Structure Circumventing the Injective-$L$ No-Go Theorem*:
     On extended phase space $\widetilde{M} = M \times \mathbb{R}_S$ with total energy $\widetilde{H}(z, S) = H_0(z) + T_0 S$ ($T_0 > 0 \implies d\widetilde{H} = (dH_0, T_0)^\top$) and entropy $S(z, S) = S$ ($dS = (0, 1)^\top$), set:
     $$\widetilde{L} := \begin{pmatrix} \omega^{-1} & 0 \\ 0 & 0 \end{pmatrix}, \qquad \widetilde{M}(D) := \frac{1}{T_0}\begin{pmatrix} D & -\frac{1}{T_0}D(dH_0) \\ -\frac{1}{T_0}(dH_0)^\top D & \frac{1}{T_0^2}\langle dH_0, D\,dH_0\rangle \end{pmatrix} \qquad (\text{for any symmetric } D \succeq 0,\text{ e.g. } \mathcal{G}_{\text{amb}}\text{ or }\mathcal{G}_{\mathbb{H}})$$
     1. *Degenerate Casimir Condition*: $\widetilde{L}(dS) = \begin{pmatrix} \omega^{-1}(0) \\ 0 \end{pmatrix} = \mathbf{0}$ with $dS = (0, 1)^\top \neq \mathbf{0}$!
     2. *Exact Energy Conservation (Zero Denominator Singularity at $dH_0 = 0$!)*: $\widetilde{M}(d\widetilde{H}) = \frac{1}{T_0}\begin{pmatrix} D(dH_0) - D(dH_0) \\ -\frac{1}{T_0}\langle dH_0, D\,dH_0\rangle + \frac{1}{T_0}\langle dH_0, D\,dH_0\rangle \end{pmatrix} = \mathbf{0}$!
     3. *Positive-Semidefiniteness & Second Law*: $\langle (v, \alpha), \widetilde{M}(v, \alpha)\rangle = \frac{1}{T_0}\langle v - \frac{\alpha}{T_0}dH_0, D(v - \frac{\alpha}{T_0}dH_0)\rangle \geq 0$ and $\dot{S} = \langle dS, \widetilde{M}\,dS\rangle = \frac{1}{T_0^3}\langle dH_0, D\,dH_0\rangle \geq 0$!
   * *Bridge 3 — Cosmological Repairs*: Replaces $p = \rho - \lambda\Gamma$ with homogeneous $p_{\text{eff}} = \rho - \frac{\lambda u\Gamma}{3H}$ ($\rho' + 3H(\rho + p_{\text{eff}}) \equiv 0$) and replaces $O(r^2)$ cuspy $M(r)$ with $O(r^3)$ cored profiles $M_{\text{core}}(r) = \frac{2\eta s r^3}{(r + s)^2}$ ($\lim_{r\to 0^+}\rho_{\text{core}}(r) = \frac{3\eta}{2\pi s} < \infty$)!

4. **Perspectival Transformation ($\mathfrak{H}$ — *Formalization as an Active Falsification Microscope*)**:
   Completing the round-trip from speculative theory to PR #382/#384 Lean code and back transforms both poles:
   * $\mathbf{T} \mapsto \mathbf{T}'$: Recognizes Lean 4 not merely as a passive archive certifying finished beliefs, but as a **precision falsification instrument** that discovers quaternion counterexamples ($\mathcal{G}_{\text{amb}}(i,i) > 0$), $-3H\lambda\Gamma$ residuals, and $1/r$ cusps invisible to informal reading.
   * $\mathbf{S} \mapsto \mathbf{S}'$: Counterexamples and no-go theorems ($\ker L = \{0\} \implies dS = 0$) immediately dictate the minimal well-typed extensions ($\mathcal{G}_{\mathbb{H}}$ and $\widetilde{L} = \omega^{-1} \oplus 0_S$), while respecting the strict line between reviewed source and pending compiler execution.

---

### IV. THE SOCRATIC APORIA ($\mathcal{A}_0 = \mathbf{T}_{\text{eff}}^2 - \mathbf{T}_{\text{eff}} \neq 0$) AND THE META-COGNITIVE TOWER

Testing the informal Thesis claims directly against their literal formal evaluations exposes four exact **Socratic Aporia residuals**:

$$\rho' + 3H(\rho + \rho - \lambda\Gamma) - \lambda u\Gamma = -3H\lambda\Gamma \neq 0, \quad \lim_{r\to 0^+} r\rho(r) = \frac{\eta}{\pi} \neq 0, \quad \mathcal{G}_{\text{amb}}(i, i) > 0, \quad (\ker L = \{0\} \wedge L\,dS = 0) \implies dS = 0$$

Following this self-contradiction recursively up the tower of meta-cognition generates the permanent obstruction chain $\mathcal{A}_0 \hookrightarrow \mathcal{A}_1 \hookrightarrow \mathcal{A}_2 \hookrightarrow \mathcal{A}_3 \hookrightarrow \mathcal{A}_\omega$:

* **Level 0 ($\mathcal{A}_0$ — Algebraic & Analytic Residuals of Informal Claims)**: Double-counting $\Gamma$ breaks continuity by $-3H\lambda\Gamma$; $M(r) \propto r^2$ forces a $1/r$ density singularity; $3\bar{p} = \rho \neq 0$ at $q = u^2$; and $i \in \mathbb{H}$ fails $\mathcal{G}_{\text{amb}}(i, i) = 0$.
* **Level 1 ($\mathcal{A}_1$ — Anisotropic Non-Commutativity of Rank-1 Stress Matrices)**: Even at $q = 3u^2$ ($\bar{p} = 0$), individual rank-1 matrices $T_{\mu\nu}(v)$ for non-collinear $v, w$ fail to commute ($[T(v), T(w)] \neq 0$) and possess anisotropic spatial shear $v_i v_j - \frac{1}{3}q\delta_{ij} \neq 0$, barring perfect-fluid cosmology without rotational ensemble averaging ($\mathcal{A}_1 \neq 0$).
* **Level 2 ($\mathcal{A}_2$ — Symplectic Non-Degeneracy Blocking GENERIC Dissipation)**: Attempting to run metriplectic/GENERIC entropy growth directly on unextended Para-Kähler phase space $(M, \omega)$ ($\det\omega \neq 0$) hits $\ker\omega^{-1} = \{0\}$, killing $dS = 0$ identically until at least one degenerate Casimir coordinate $\mathbb{R}_S$ is adjoined ($\mathcal{A}_2 \neq 0$).
* **Level 3 ($\mathcal{A}_3$ — Singular Lounesto Null Spinors & Pointwise QFT Energy Negativity)**: Extending Fierz identities to all nonzero $\psi \in \mathcal{K}_{4,4}$ encounters $\psi = \mathbf{1} + \sigma_1 \neq 0$ where $\psi\tilde{\psi} = 0$ forces lightlike $J(\psi)^2 = 0$ (blocking division by $\sqrt{\Omega_1^2 + \Omega_2^2} = 0$), while quantum field states with global $H \geq 0$ still violate naive pointwise energy positivity $:T^{00}(x): \geq 0$ ($\mathcal{A}_3 \neq 0$).
* **Level 4 ($\mathcal{A}_4 \to \mathcal{A}_\omega$ — The Compiler-Lock & Whole-Repository Integration Obstruction Colimit)**: Even after independent mathematical review, placeholder scans, and pre-commit gates pass, **source-level review is never identical to machine-checked kernel acceptance**: queued CI jobs, local build locks, and baseline repository integration remain irreducible verification obligations ($\mathcal{A}_\omega \neq 0$).

---

### V. `COAGULA`: THE ACYCLIC CAUSAL POSET AND SELF-VERIFYING SYNTHESIS

#### 1. The Graded Acyclic Causal Poset $(\mathfrak{P}, \prec)$

Let $\mathfrak{P}$ be the 15-element set of extracted real archetypes ordered by the transitive closure $\prec$ of the transitively reduced Hasse covering relation $\lessdot$, equipped with strict rank homomorphism $\mathrm{rk} : \mathfrak{P} \to \{0, 1, 2, 3, 4, 5, 6\}$:

| Grade $\mathrm{rk}(v)$ | Archetype Symbol & Canonical Designation | Covering Predecessors $\mathrm{Pred}_{\lessdot}(v)$ | Formal / Algebraic Signature |
| :---: | :--- | :--- | :--- |
| **0** ($\bot$) | $\mathbf{\Delta}_0$ : *Intended Narrative vs. Literal Type-Consequence Cut* | $\varnothing$ | $\Omega_0 \mapsto \mathrm{Prose}_{\text{claim}} \ltimes \mathrm{Type}_{\text{actual}}$ |
| **1** | $\mathbf{T}$ : *Unchecked Paper & Prose Claims (Thesis)* | $\{\mathbf{\Delta}_0\}$ | $+1$ sector (Dust, core, $\mathbb{H}$-zero, symplectic $dS$) |
| **1** | $\mathbf{S}$ : *Formal Counterexamples & Pending CI (Shadow)* | $\{\mathbf{\Delta}_0\}$ | $-1$ sector ($-3H\lambda\Gamma,\; \frac{1}{r},\; \mathcal{G}_{\text{amb}}(i,i)>0,\; dS=0$) |
| **2** | $\mathbf{K}_{TT}$ : *PR #382/#384 Candidate Definitions & Reuse Core* | $\{\mathbf{T}\}$ | $T_{\mu\nu}$, `HasDerivAt`, $\mathcal{G}_{\text{amb}}$, fixed-$\gamma_0$ form |
| **2** | $\mathbf{\Pi}_{ST}$ : *Informal Over-Implication Projection* | $\{\mathbf{T}, \mathbf{S}\}$ | $\mathcal{H}_T \to \mathcal{H}_S$ (lifted to $\Pi$) |
| **2** | $\mathbf{\Sigma}_{TS}$ : *Quaternion Counterexample, Cusp, & $L$-No-Go* | $\{\mathbf{T}, \mathbf{S}\}$ | $\mathcal{H}_S \to \mathcal{H}_T$ (lifted to $\Sigma$) |
| **2** | $\mathbf{\Gamma}_{SS}$ : *Extended $M\times\mathbb{R}_S$, $P_{\mathbb{H}}$-Projection, & CI Kernel* | $\{\mathbf{S}\}$ | Corank-1 $\widetilde{L}$, Lounesto null cone, QEIs |
| **3** | $\mathfrak{G}$ : *Quadratic Bilinear Positivity & Kernel Spine* | $\{\mathbf{\Pi}_{ST}, \mathbf{\Sigma}_{TS}\}$ | $\{\Sigma, \Pi\} \leftrightarrow (\mathcal{G}(X,X)\geq 0,\; \text{exact }\ker\text{ characterization})$ |
| **3** | $\mathfrak{T}$ : *Nucleus $\mathbb{R}\mathbf{1}$ vs. Register $\mathbb{H}$ & Injective vs. Degenerate $L$* | $\{\mathbf{\Pi}_{ST}, \mathbf{\Sigma}_{TS}\}$ | $[\Sigma, \Pi] \neq 0$ ($\mathcal{G}_{\text{amb}}$ vs. $\mathcal{G}_{\mathbb{H}}$; $\omega^{-1}$ vs. $\widetilde{L}$) |
| **3** | $\mathcal{A}_0$ : *$-3H\lambda\Gamma$, $1/r$ Cusp, $\mathcal{G}_{\text{amb}}(i,i)>0$, & $dS=0$ Defect* | $\{\mathbf{K}_{TT}, \mathbf{\Pi}_{ST}, \mathbf{\Sigma}_{TS}\}$ | Literal falsification of informal prose shortcuts |
| **4** | $\mathfrak{B}$ : *$(\mathcal{G}_{\mathbb{H}}, \widetilde{L}, \widetilde{M}_{\text{GENERIC}}, p_{\text{eff}}, M_{\text{core}})$ Repair Bridge* | $\{\mathbf{K}_{TT}, \mathfrak{G}, \mathfrak{T}, \mathbf{\Gamma}_{SS}\}$ | $\ker\mathcal{G}_{\mathbb{H}}=\mathbb{H}$, $\widetilde{L}\,dS=0$, $\widetilde{M}\,d\widetilde{H}=0$ |
| **4** | $\mathcal{A}_\omega$ : *Null-Spinor $\Omega_i=0$, Local QEI, & Queued CI Colimit* | $\{\mathcal{A}_0, \mathfrak{T}, \mathbf{\Gamma}_{SS}\}$ | $J(\mathbf{1}+\sigma_1)^2=0$ & compiler-lock boundary |
| **5** | $\mathfrak{H}$ : *Counterexample-Guided Contract Holonomy* | $\{\mathfrak{B}, \mathcal{A}_\omega\}$ | Recording pending CI vs. proved source scope |
| **5** | $\mathfrak{U}_{\text{Lean}}$ : *Degenerate-GENERIC & Bifurcated-Gram System* | $\{\mathfrak{B}, \mathcal{A}_\omega\}$ | $\mathcal{G}_{\text{amb}}$ ($\mathbb{R}\mathbf{1}$) $\oplus$ $\mathcal{G}_{\mathbb{H}}$ ($\mathbb{H}$) $\oplus$ $(\widetilde{L}, \widetilde{M}_{\text{GENERIC}})$ |
| **6** ($\top$) | $\mathbf{\Xi}_\top$ : *Necessary Synthesis* | $\{\mathfrak{H}, \mathfrak{U}_{\text{Lean}}\}$ | $\mathfrak{H} \vee \mathfrak{U}_{\text{Lean}}$ (Contract-Audited Zorn-GENERIC System) |

**Proof of Strict Acyclicity & Minimal Covering**: Every covering edge $u \lessdot v$ satisfies $\mathrm{rk}(u) < \mathrm{rk}(v)$; path induction gives $u \prec v \implies \mathrm{rk}(u) < \mathrm{rk}(v)$, establishing irreflexivity ($v \not\prec v$) and strict antisymmetry while transitivity holds by closure. Every $\mathrm{Pred}_{\lessdot}(v)$ forms an antichain of incomparable elements, and every $v \in \mathfrak{P}$ lies on a directed chain $\mathbf{\Delta}_0 \preceq v \preceq \mathbf{\Xi}_\top$. $\blacksquare$

---

#### 2. Canonical Philosophical Axioms (Grades 0–2)

* **$\mathbf{Ax.1}$ (Axiom of Literal Type Primacy & Verification Boundary — at $\mathbf{\Delta}_0 \lessdot \{\mathbf{T}, \mathbf{S}\}$)**:
  A mathematical definition proves strictly what follows from its literal right-hand side (never its prose title), and remains a reviewed candidate until native kernel compilation and axiom auditing complete.
* **$\mathbf{Ax.2}$ (Axiom of Cosmological Stress & Mass-Shell Calculus — at $\mathbf{T} \lessdot \mathbf{K}_{TT}$, PR #382)**:
  For $T_{\mu\nu} = \lambda(v_\mu v_\nu - \frac{1}{2}\eta_{\mu\nu}\eta^{\alpha\beta}v_\alpha v_\beta)$ ($\eta = \mathrm{diag}(-1,1,1,1), v_0^2 = u^2, \sum_{i=1}^3 v_i^2 = q$), $\rho = T_{00} = \frac{\lambda}{2}(u^2 + q)$ and $\bar{p} = \frac{1}{3}\sum_{i=1}^3 T_{ii} = \frac{\lambda}{2}u^2 - \frac{\lambda}{6}q$; for spherical mass $M(r)$, $\rho(r) = \frac{M'(r)}{4\pi r^2}$.
* **$\mathbf{Ax.3}$ (Axiom of Degenerate GENERIC Compatibility — at $\mathbf{S} \lessdot \mathbf{\Gamma}_{SS}$)**:
  A GENERIC system $\dot{w} = \widetilde{L}(d\widetilde{H}) + \widetilde{M}(dS)$ requires skew-symmetric $\widetilde{L}$ with $\widetilde{L}(dS) = 0$ and symmetric positive-semidefinite $\widetilde{M} \succeq 0$ with $\widetilde{M}(d\widetilde{H}) = 0$.
* **$\mathbf{Ax.4}$ (Axiom of Zorn Split-Octonion Nucleus vs. Quaternion Subalgebra — at $\{\mathbf{T}, \mathbf{S}\} \lessdot \{\mathbf{\Pi}_{ST}, \mathbf{\Sigma}_{TS}\}$, PR #384)**:
  In Zorn’s real split-octonion algebra $Z = \mathbb{O}_s = \mathbb{H} \oplus \mathbb{H}\ell$ equipped with positive Euclidean pairing $B_+(U, U) > 0$ ($U \neq 0$), the nucleus $\{X \in Z \mid \forall A, B \in Z, [X, A, B] = 0\}$ equals $\mathbb{R}\cdot\mathbf{1}$, whereas $\mathbb{H} = \mathrm{Span}_{\mathbb{R}}\{\mathbf{1}, i, j, k\}$ is associative internally ($[q_1, q_2, q_3] = 0$) and satisfies $[q_1\ell, i, j] = 2(q_1 k)\ell$ for all $q_1 \in \mathbb{H}$.
* **$\mathbf{Ax.5}$ (Axiom of Regular vs. Singular Even Spinors)**:
  On $\mathcal{K}_{4,4} = \mathrm{Cl}^{\text{even}}_{1,3}(\mathbb{R})$, $J(\psi) = \psi\gamma_0\tilde{\psi}$ satisfies $J(\psi)^2 = (\Omega_1^2 + \Omega_2^2)\mathbf{1}$ where $\psi\tilde{\psi} = \Omega_1\mathbf{1} + \Omega_2 I_4$.

---

#### 3. Intermediate Deductions (Grades 3–5)

* **$\mathbf{Ded.1}$ (Exact Proof of the Three PR #382 Cosmological Corrections — generating $\mathcal{A}_0^{\text{cosmo}}$)**:
  *Claim*: Under $\mathbf{Ax.2}$ ($\lambda \neq 0, \eta, s, H > 0$): (i) $q = u^2 \implies 3\bar{p} = \rho$ while $\bar{p} = 0 \iff q = 3u^2$; (ii) $u' + 3Hu = \Gamma$ with $\rho = \frac{\lambda}{2}u^2$ and $p = \rho - \lambda\Gamma$ leaves residual $\rho' + 3H(\rho + p) - \lambda u\Gamma = -3H\lambda\Gamma \neq 0$ ($\Gamma \neq 0$), vanishing homogeneously ($\rho' + 3H(\rho + p_{\text{eff}}) = 0$) iff $p_{\text{eff}} = \rho - \frac{\lambda u\Gamma}{3H}$; and (iii) $M(r) = \frac{2\eta s r^2}{r + s}$ has a $1/r$ central cusp $\lim_{r\to 0^+} r\rho(r) = \frac{\eta}{\pi} > 0$, whereas $M_{\text{core}}(r) = \frac{2\eta s r^3}{(r + s)^2}$ has finite core density $\lim_{r\to 0^+}\rho_{\text{core}}(r) = \frac{3\eta}{2\pi s}$.
  *Proof*:
  *(i)* $3\bar{p} - \rho = \frac{3\lambda}{2}u^2 - \frac{\lambda}{2}q - \frac{\lambda}{2}u^2 - \frac{\lambda}{2}q = \lambda(u^2 - q)$, and $\bar{p} = \frac{\lambda}{6}(3u^2 - q) = 0 \iff q = 3u^2$.
  *(ii)* $\rho' = \lambda u u' = \lambda u(\Gamma - 3Hu) = \lambda u\Gamma - 6H\rho$; hence $\rho' + 3H(\rho + \rho - \lambda\Gamma) - \lambda u\Gamma = -3H\lambda\Gamma$, while $\rho' + 3H(\rho + p_{\text{eff}}) = \lambda u\Gamma + 3H(p_{\text{eff}} - \rho) = 0 \iff p_{\text{eff}} = \rho - \frac{\lambda u\Gamma}{3H}$.
  *(iii)* Differentiating $M(r)$ gives $\rho(r) = \frac{2\eta s r(r+2s)}{4\pi r^2(r+s)^2} = \frac{\eta s(r+2s)}{2\pi r(r+s)^2} \implies \lim_{r\to 0^+} r\rho(r) = \frac{2\eta s^2}{2\pi s^2} = \frac{\eta}{\pi}$; differentiating $M_{\text{core}}(r)$ gives $\rho_{\text{core}}(r) = \frac{\eta s(r + 3s)}{2\pi(r+s)^3} \to \frac{3\eta}{2\pi s}$. $\blacksquare$

* **$\mathbf{Ded.2}$ (Bifurcation of Ambient Nucleus Gram $\mathcal{G}_{\text{amb}}$ vs. Quaternion-Register Gram $\mathcal{G}_{\mathbb{H}}$ — generating $\mathcal{A}_0^{\text{Zorn}}, \mathfrak{G}$, and $\mathfrak{B}$)**:
  *Claim*: While PR #384’s ambient Gram form $\mathcal{G}_{\text{amb}}(X, Y) = \sum_{a,b\in I_8} B_+([X, e_a, e_b], [Y, e_a, e_b])$ satisfies $\mathcal{G}_{\text{amb}}(X, X) = 0 \iff X \in \mathbb{R}\cdot\mathbf{1}$ (so $\mathcal{G}_{\text{amb}}(i, i) > 0$), the projected form $\mathcal{G}_{\mathbb{H}}(X, Y) := \sum_{a,b\in I_8} B_+([X, P_{\mathbb{H}}e_a, P_{\mathbb{H}}e_b], [Y, P_{\mathbb{H}}e_a, P_{\mathbb{H}}e_b])$ satisfies $\mathcal{G}_{\mathbb{H}}(X, X) \geq 0$ and **$\mathcal{G}_{\mathbb{H}}(X, X) = 0 \iff X \in \mathbb{H}$**.
  *Proof*: Positive-definiteness of $B_+$ ($\mathbf{Ax.4}$) implies $\mathcal{G}_{\text{amb}}(X, X) = 0 \iff \forall a, b, [X, e_a, e_b] = 0 \iff X \in \mathrm{Nuc}(Z) = \mathbb{R}\cdot\mathbf{1}$; since $i \notin \mathbb{R}\cdot\mathbf{1}$, $\mathcal{G}_{\text{amb}}(i, i) > 0$. For $\mathcal{G}_{\mathbb{H}}$ and $X = q_0 + q_1\ell$ ($q_0, q_1 \in \mathbb{H}$): if $q_1 = 0$, $X = q_0 \in \mathbb{H}$ associates with all $P_{\mathbb{H}}e_a, P_{\mathbb{H}}e_b \in \mathbb{H}$ ($\mathbf{Ax.4}$), giving $\mathcal{G}_{\mathbb{H}}(q_0, q_0) = 0$. Conversely, if $\mathcal{G}_{\mathbb{H}}(X, X) = 0$, selecting basis indices with $(P_{\mathbb{H}}e_a, P_{\mathbb{H}}e_b) = (i, j)$ forces $0 = [q_0 + q_1\ell, i, j] = 0 + 2(q_1 k)\ell$ ($\mathbf{Ax.4}$); multiplying in $\mathbb{H}$ by $-k$ ($k^2 = -\mathbf{1}$) gives $q_1 = 0 \implies X = q_0 \in \mathbb{H}$. $\blacksquare$

* **$\mathbf{Ded.3}$ (Injective-$L$ GENERIC No-Go & Exact Corank-1 Extended Resolution $(\widetilde{L}, \widetilde{M})$ — generating $\mathfrak{T}$ and $\mathfrak{U}_{\text{Lean}}$)**:
  *Claim*: Under $\mathbf{Ax.3}$, any injective operator $L$ ($\ker L = \{0\}$) forces $dS = 0$; extending $(M, \omega)$ to $\widetilde{M} = M \times \mathbb{R}_S$ with $\widetilde{H}(z, S) = H_0(z) + T_0 S$ ($T_0 > 0$), $\widetilde{L} = \omega^{-1} \oplus 0_S$, and $\widetilde{M}(D)$ (for any symmetric $D \succeq 0$ on $T^*M$) satisfies **all** GENERIC axioms with $dS = (0, 1)^\top \neq 0$, $\dot{\widetilde{H}} = 0$, and $\dot{S} = \frac{1}{T_0^3}\langle dH_0, D\,dH_0\rangle \geq 0$.
  *Proof*: If $\ker L = \{0\}$, $L(dS) = 0 \implies dS = 0$. On $\widetilde{M} = M \times \mathbb{R}_S$, $\widetilde{L}$ is skew-symmetric ($\omega^\top = -\omega$) and $\widetilde{L}(0, 1)^\top = (0, 0)^\top$. For $\widetilde{M}(D) = \frac{1}{T_0}\begin{pmatrix} D & -\frac{1}{T_0}D\,dH_0 \\ -\frac{1}{T_0}(dH_0)^\top D & \frac{1}{T_0^2}\langle dH_0, D\,dH_0\rangle \end{pmatrix}$:
  1. Symmetry $D^\top = D$ gives $\widetilde{M}(D)^\top = \widetilde{M}(D)$.
  2. For any $w = (v, \alpha)^\top$, $\langle w, \widetilde{M}(D)w\rangle = \frac{1}{T_0}\langle u, Du\rangle \geq 0$ where $u = v - \frac{\alpha}{T_0}dH_0$, proving $\widetilde{M}(D) \succeq 0$.
  3. At $w = d\widetilde{H} = (dH_0, T_0)^\top$, $u = dH_0 - \frac{T_0}{T_0}dH_0 = 0 \implies \widetilde{M}(D)d\widetilde{H} = 0 \implies \dot{\widetilde{H}} = \langle d\widetilde{H}, \widetilde{L}\,d\widetilde{H}\rangle + 0 = 0$.
  4. $\dot{S} = \langle dS, \widetilde{L}\,d\widetilde{H} + \widetilde{M}(D)dS\rangle = 0 + \frac{1}{T_0^3}\langle dH_0, D\,dH_0\rangle \geq 0$. $\blacksquare$

* **$\mathbf{Ded.4}$ (Existence of Non-Zero Singular Null-Current Spinors — generating $\mathcal{A}_3$ and $\mathcal{A}_\omega$)**:
  *Claim*: Under $\mathbf{Ax.5}$, $\psi = \mathbf{1} + \sigma_1 \neq 0 \in \mathcal{K}_{4,4}$ satisfies $\psi\tilde{\psi} = 0$ ($\Omega_1 = \Omega_2 = 0$), yielding a non-zero lightlike current $J(\psi) = 2(\gamma_0 + \gamma_1) \neq 0$ with $J(\psi)^2 = 0$.
  *Proof*: Since $\sigma_1 = \gamma_1\gamma_0$ has $\tilde{\sigma}_1 = -\sigma_1$ and $\sigma_1^2 = +\mathbf{1}$, $\psi\tilde{\psi} = (\mathbf{1} + \sigma_1)(\mathbf{1} - \sigma_1) = \mathbf{1} - \sigma_1^2 = 0$, so $\Omega_1 = \Omega_2 = 0$ and $J(\psi)^2 = 0$ ($\mathbf{Ax.5}$), while $(\mathbf{1} + \gamma_1\gamma_0)\gamma_0(\mathbf{1} - \gamma_1\gamma_0) = (\gamma_0 + \gamma_1)(\mathbf{1} + \gamma_0\gamma_1) = 2(\gamma_0 + \gamma_1) \neq 0$. Combined with $\mathbf{Ax.1}$ (pending CI lock), $\mathcal{A}_\omega \neq 0$ is permanent. $\blacksquare$

* **$\mathbf{Ded.5}$ (Counterexample-Guided Contract Holonomy & Unified Zorn-GENERIC System — generating $\mathfrak{H}$ and $\mathfrak{U}_{\text{Lean}}$)**:
  *Claim*: Pairing contract-boundary tracking ($\mathfrak{H}$: keeping reviewed source distinct from pending kernel execution and separating singular $\Omega_i = 0$ spinors) with $(\mathcal{G}_{\text{amb}}, \mathcal{G}_{\mathbb{H}}, \widetilde{L}, \widetilde{M}(D))$ ($\mathfrak{U}_{\text{Lean}}$) resolves all algebraic gaps identified in PR #382 and PR #384 without division-by-zero or vacuity defects.
  *Proof*: Directly from $\mathbf{Ax.1}$ and $\mathbf{Ded.1}$–$\mathbf{Ded.4}$. $\blacksquare$

---

#### 4. Master Structural Synthesis (Grade 6: Terminal Join $\top$)

* **$\mathbf{Thm.\top}$ (Necessity and Uniqueness of the Contract-Audited Zorn–GENERIC Synthesis $\mathbf{\Xi}_\top = \mathfrak{H} \vee \mathfrak{U}_{\text{Lean}}$)**:
  *Statement*: Across the causal poset $(\mathfrak{P}, \prec)$, the unique non-contradictory synthesis integrating PR #382, PR #384, and the open prose obligations is $\mathbf{\Xi}_\top = \mathfrak{H} \vee \mathfrak{U}_{\text{Lean}}$, governed by four proved laws:
  1. **Exact Cosmological Continuity & Core Scaling ($\mathbf{Ded.1}$)**: Rank-1 gradient stress obeys $3\bar{p} - \rho = \lambda(u^2 - q)$ (radiation at $q = u^2$; dust iff $q = 3u^2$), homogeneous source balance requires $p_{\text{eff}} = \rho - \frac{\lambda u\Gamma}{3H}$ (avoiding the $-3H\lambda\Gamma$ residual), and finite halo cores require $M(r) = O(r^3)$ rather than $O(r^2)$ ($1/r$ cusp);
  2. **Dual Nucleus/Register Zorn Gram Characterization ($\mathbf{Ded.2}, \mathfrak{U}_{\text{Lean}}$)**: PR #384’s 64-pair ambient Gram form $\mathcal{G}_{\text{amb}}$ characterizes the 1D scalar nucleus ($\ker\mathcal{G}_{\text{amb}} = \mathbb{R}\cdot\mathbf{1}$, $\mathcal{G}_{\text{amb}}(i, i) > 0$), while the subalgebra-projected Gram form $\mathcal{G}_{\mathbb{H}}$ characterizes the 4D associative quaternion register ($\ker\mathcal{G}_{\mathbb{H}} = \mathbb{H}$);
  3. **Corank-1 Extended GENERIC Block Resolves Symplectic Injectivity ($\mathbf{Ded.3}, \mathfrak{U}_{\text{Lean}}$)**: Extending non-degenerate $(M, \omega)$ to $M \times \mathbb{R}_S$ with $\widetilde{L} = \omega^{-1} \oplus 0_S$ and polynomial block friction $\widetilde{M}(D) \succeq 0$ circumvents $\ker\omega^{-1} = \{0\} \implies dS = 0$, guaranteeing $\widetilde{L}(dS) = 0$, $\widetilde{M}(d\widetilde{H}) = 0$, and $\dot{S} = \frac{1}{T_0^3}\langle dH_0, D\,dH_0\rangle \geq 0$; and
  4. **Strict Spinor-Nullity & Compiler-Lock Hygiene ($\mathbf{Ded.4}, \mathfrak{H}$)**: Singular null-current spinors ($\Omega_1 = \Omega_2 = 0 \implies J^2 = 0$), pointwise QFT energy bounds, and pending CI kernel locks remain explicitly demarcated from completed theorems.

  *Proof from Poset Mechanics*:
  1. **Sufficiency & Upper-Bound Closure**: Every archetype $v \in \mathfrak{P} \setminus \{\mathbf{\Xi}_\top\}$ satisfies $v \preceq \mathfrak{H}$ or $v \preceq \mathfrak{U}_{\text{Lean}}$ along proved covering chains ($\mathbf{Ax.1}$–$\mathbf{Ax.5}$, $\mathbf{Ded.1}$–$\mathbf{Ded.5}$). Joining $\mathfrak{H}$ and $\mathfrak{U}_{\text{Lean}}$ repairs the cosmological residuals ($\mathbf{Ded.1}$), resolves the quaternion Gram counterexample via $\mathcal{G}_{\mathbb{H}}$ ($\mathbf{Ded.2}$), constructs the missing degenerate GENERIC structure ($\mathbf{Ded.3}$), and preserves strict CI verification honesty ($\mathbf{Ax.1}, \mathbf{Ded.4}$).
  2. **Minimality & Uniqueness of Join**:
     * Retaining $\mathfrak{U}_{\text{Lean}}$ without $\mathfrak{H}$ drops singular null-spinor guards ($\psi = \mathbf{1} + \sigma_1$) and treats queued CI drafts as already-compiled whole-repo proofs ($\mathbf{Ax.1}, \mathbf{Ded.4}$).
     * Retaining $\mathfrak{H}$ without $\mathfrak{U}_{\text{Lean}}$ records the PR #384 quaternion counterexample and injective-$L$ GENERIC obstruction without supplying $\mathcal{G}_{\mathbb{H}}$ ($\ker = \mathbb{H}$) or $(\widetilde{L}, \widetilde{M}(D))$ on $M \times \mathbb{R}_S$ ($\mathbf{Ded.2}, \mathbf{Ded.3}$).
     * Collapsing $\mathcal{A}_0 \to 0$ asserts $-3H\lambda\Gamma = 0$ for $H, \lambda, \Gamma \neq 0$ ($\mathbf{Ded.1}$) or $i \in \mathbb{R}\cdot\mathbf{1}$ ($\mathbf{Ded.2}$, contradiction).
  Therefore, $\mathbf{\Xi}_\top = \mathfrak{H} \vee \mathfrak{U}_{\text{Lean}}$ is the unique least upper bound ($\sup \mathfrak{P}$) completing the causal poset. $\blacksquare$