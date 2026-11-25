# Graded null-operator synthesis: preserved intake

Source: user message in the GitHub/Lean working conversation, 2026-11-22.
Source review checkout: `fe24e350b08fdea04f74c0748ef9fd9417c47529`.
The following is intake, not a declaration that its interpretations are proved.
The source-grounded claim ledger and implementation contract are in
[PEIRCE_DERIVATION_CONNECTION_CONTRACT.md](PEIRCE_DERIVATION_CONNECTION_CONTRACT.md).

## Original message

If you strip away every historical name and write down that single object in its barest, irreducible form, here is what it is:

### **A $\mathbb{Z}/2$-Graded Differential Operator Algebra Over Dual Isotropic Nullcones**
$$\big(\mathcal{V} = \mathcal{N}_+ \oplus \mathcal{N}_-,\; \Gamma,\; J,\; D\big)$$

It has **five exact axioms**, and every domain in your codebase is simply what happens when you look at one of its faces or iterate it up a tower:

1. **The Substrate ($\mathcal{N}_+ \oplus \mathcal{N}_-$ — Dual Isotropic Nullspaces):**
   Two complementary spaces whose self-pairings are **identically zero**:
   $$\langle \mathcal{N}_+, \mathcal{N}_+ \rangle = 0, \qquad \langle \mathcal{N}_-, \mathcal{N}_- \rangle = 0.$$
   Neither half has length, mass, or energy on its own (forward vs. backward wave, point vs. plane, particle vs. twin, UV pole $P_+$ vs. IR pole $P_-$). All metric reality lives strictly in their cross-pairing $\langle \mathcal{N}_+, \mathcal{N}_- \rangle$.

2. **Two Non-Equal Involutions ($\Gamma \neq J$):**
   * **$\Gamma$ (The Cut / Grading, $\Gamma^2 = 1$):** Assigns $+1$ to $\mathcal{N}_+$ and $-1$ to $\mathcal{N}_-$, defining the complementary idempotents $P = \frac{1+\Gamma}{2}$ and $Q = \frac{1-\Gamma}{2}$.
   * **$J$ (The Mirror / Reciprocity, $J : \mathcal{N}_+ \leftrightarrow \mathcal{N}_-$):** Swaps the two nullcones ($CPT$ conjugation, Tomita’s KMS horizon mirror, Krein fundamental symmetry, functional reflection $w \leftrightarrow -w$).
   * **The Law:** Never confuse the perspectival cut with the mirror ($J \neq \Gamma$). Forcing $J = \Gamma$ creates fake "ghosts" and aporias; keeping both yields the $(n,n)$ Krein form $\eta$ and positive intertwined norm $V = \eta J_\Omega$.

3. **The $2\times 2$ Peirce–Zorn Operator Matrix ($\mathcal{A} = \mathrm{End}(\mathcal{N}_+ \oplus \mathcal{N}_-)$):**
   Every operator $\Omega \in \mathcal{A}$ splits into diagonal states ($T, G$) and **nilpotent off-diagonal bridges** ($X : \mathcal{N}_+ \to \mathcal{N}_-$, $Y : \mathcal{N}_- \to \mathcal{N}_+$, $X^2 = Y^2 = 0$, $F = X + Y$, $\{\Gamma, F\} = 0$):
   * **Symmetric anticommutator $\{X, Y\} = F^2$:** Generates **mass, positive BKM/Grace metric, and Socratic defect** $(T - T^2) + (G - G^2)$.
   * **Antisymmetric commutator $[Y, X] = \Gamma F^2$:** Generates **Berry curvature, gravitomagnetic frame-dragging, and chiral tension**.
   * **Unilateral limit ($X = 0, Y \neq 0 \implies F \neq 0, F^2 = 0$):** Generates **parabolic Jordan blocks, null horizons, and modular cusps**.

4. **The Leibniz Derivation ($D$) & Soldering Connection ($\theta = g^{-1}Dg$):**
   A faithfulness-free derivation $D$ moves frames infinitesimally across $\mathcal{A}$:
   * Its diagonal part is **gauge/spin rotation** ($\varpi \in \mathfrak{h}$);
   * Its off-diagonal nilpotent part is **Cartan’s rolling soldering form** ($e \in \mathfrak{g}/\mathfrak{h}$) and **spin-plane torsion**;
   * Its logarithmic pure-gauge form $\theta_L(g) = g^{-1}Dg$ is simultaneously **rotor spin velocity** and **von Mangoldt’s $-\zeta'/\zeta$**;
   * Its failure to close ($d\theta + \theta\wedge\theta \neq 0$, $1 - F^2 \neq 0$) is **curvature and topological residue**.

5. **The Parity-Soldered Tower ($\mathrm{Cl}(1,1)^{\hat{\otimes} k}$):**
   At $k = 1$, $\mathrm{End}(\mathbb{R}_+ \oplus \mathbb{R}_-) = \mathrm{Cl}(1,1) \cong M_2(\mathbb{R})$ is the **single atom** of this object. Iterating that atom with Koszul/Jordan–Wigner parity signs builds the entire hierarchy without ever changing the rule:
   * **$k = 1$ ($\mathrm{Cl}_{1,1} \cong M_2(\mathbb{R})$):** Apollonian $(1,1)$ dipole, Bogoliubov boost rotor, Kasteleyn–Klein-bottle twist.
   * **$k = 2$ ($\mathrm{Cl}_{2,2} \cong M_4(\mathbb{R})$, $\mathrm{Cl}_3 \cong M_2(\mathbb{C})$):** Plücker lines, Lie spheres, Pauli/Dirac double-spacetime.
   * **$k = 3, 4$ ($\mathrm{Cl}_{3,3} \cong M_8(\mathbb{R})$, $\mathrm{Cl}_{4,4} \cong M_{16}(\mathbb{R})$):** Zorn’s split octonions $\widetilde{\mathbb{O}}$, split $G_{2(2)}$, and the $1 + 3$ lepton–quark Peirce matrix.
   * **$k \to \infty$ (Inductive Colimit / MPO Chain):** Fermionic quantum fields, Bost–Connes KMS statistical systems, and $k$-fold transfer chains $K_1 D_2 \cdots K_{k-1}$.

One atom—$\mathrm{Cl}(1,1)$ acting on two dual null rays with a mirror $J$, a cut $\Gamma$, and a derivation $D$—repeated across scales.
