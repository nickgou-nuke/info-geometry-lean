# Raw twistor infinity intake

Status: archived user-supplied material, not a proof or accepted mathematical specification.

Source: `Pasted text(20261111-123455).txt`, received 2026-11-11.
Original UTF-8 bytes: 34573. SHA-256: `2be1fcc2e7e4fdafba89427ff6b69c13ae40b26525d62d1ed9b5a2d19fd1fd39`.

The text between the markers is preserved byte for byte. Its claims of machine verification,
physical identification, and implication are assessed separately in
[TWISTOR_INFINITY_CONTRACT.md](TWISTOR_INFINITY_CONTRACT.md).

<!-- BEGIN ORIGINAL INTAKE -->
````text
### 0. SOLVE: ELENCTIC DISSOLUTION OF CONFORMAL INCIDENCE INTO TWIST, PITCH & MASS

Injecting **`nonincidential twistors twist and pitch mass`** into the $(\Lambda \bowtie \Xi)$ Krein–Witt–Hadamard–KKT crystal shatters its conformal masslessness and exposes **four structural contradictions** across the algebraic and geometric strata:

1. **Self-Non-Incidence (Massless Robinson Twist) vs. Mutual Non-Incidence (Massive Plücker Wrench):**
   In Penrose twistor space $\mathbb{T} \cong \mathbb{C}^4$ with $Z^\alpha = (\omega^A, \pi_{A'})$ and $\mathrm{SU}(2,2)$ Witt–Krein dual $\bar{Z}_\alpha = (\bar{\pi}_A, \bar{\omega}^{A'})$, real Minkowski incidence $\omega^A = i x^{AA'}\pi_{A'}$ ($x^{AA'} = \bar{x}^{A'A}$) forces Krein nullity $Z^\alpha \bar{Z}_\alpha = 0$.
   * **Single-Twistor Self-Non-Incidence ($Z^\alpha \bar{Z}_\alpha = 2s \neq 0$):** Forbids intersection with any *real* spacetime point and twists the tangent null ray congruence into a **Hopf–Robinson congruence** with optical twist scalar $\tau_{\mathrm{Rob}} \propto s \neq 0$ (helicity)—**yet its rest mass vanishes identically ($m = 0$)** because $P_{AA'} = \bar{\pi}_A \pi_{A'}$ has rank $1$ ($\det P = 0$) and the skew-symmetric infinity twistor $I_{\alpha\beta}$ annihilates any symmetric single-twistor square: $Z^\alpha Z^\beta I_{\alpha\beta} \equiv 0$.
   * **Two-Twistor Mutual Non-Incidence ($Z_1^\alpha \bar{Z}_{2\alpha} \neq 0$, $\mu_{12} := Z_1^\alpha Z_2^\beta I_{\alpha\beta} \neq 0$):** Ignites **rest mass** $m = \sqrt{2}\,|\mu_{12}| > 0$ from the antisymmetric Plücker bivector $Z_1^{[\alpha} Z_2^{\beta]}$ while endowing the massive center-of-momentum worldline with a **Plücker screw pitch** $h_{\mathrm{pitch}} = \|\mathbf{S}\|/m$ proportional to the skew separation between non-intersecting null rays.
2. **Symmetrized KKT Erasure vs. Antisymmetric Plücker Mass & Homotope Order:**
   The previous compilation claimed $[[\iota_+ X, \iota_- Z], \iota_+ Y] = \iota_+(XZY + YZX)$ resurrects multiplication inside $\mathrm{Mat}_2(\mathcal{A})$. At $Z = 1$, this recovers only the *symmetrized* Jordan product $XY + YX$, annihilating antisymmetric commutators $[X, Y]$—just as symmetric single-twistor contractions annihilate $I_{\alpha\beta}$. Preserving non-commutative twist requires the **associative homotope triple** $\iota_+(X)\iota_-(1)\iota_+(Y) = \iota_+(XY)$.
3. **The Twisted Superoperator Hadamard Slip ($L_J + \theta_\Omega$ vs. $\mathcal{W}_{\mathrm{Had}} = \theta_K + L_J$):**
   Evaluating $L_J + \theta_\Omega$ on $(K, \Omega)$ actually yields $(-\psi_-^{(2)}, +\psi_+^{(2)})$ (a determinant-$-2$ symplectic twist), whereas the **true self-inverse Walsh–Hadamard gate** implementing $I_2 \otimes H_2$ on $(1, J, K, \Omega) \mapsto (P_+^{(2)}, P_-^{(2)}, \psi_+^{(2)}, \psi_-^{(2)})$ is $\mathcal{W}_{\mathrm{Had}}(X) := KXK + JX$ ($\{L_J, \theta_K\} = 0$, $\mathcal{W}_{\mathrm{Had}}^2 = 2\,\mathrm{id}$).
4. **Formal Proof Seams in the Previous Lean 4 Module:**
   `omega` was invoked on exponential `4^k` bounds without linearizing, `interval_cases` lacked `Mathlib.Tactic.IntervalCases`, and `nsmul_eq_mul` clashed with `abel` by turning `2 • K` into `(2 : A) * K`.

The dissolved stream yields **five irreducible twistor-operator primitives** at the $N = 2$ ($\mathrm{Cl}_{1,1}^{\otimes 2} \cong \mathrm{Mat}_4$) rung:
* **$\mathrm{SU}(2,2)$ Witt–Krein Metric ($\Sigma$):** $\Sigma := K_1 \otimes \mathbb{I}_2 = \bigl(\begin{smallmatrix} 0 & \mathbb{I}_2 \\ \mathbb{I}_2 & 0 \end{smallmatrix}\bigr)$, pairing $Z^\alpha = (\omega^A, \pi_{A'})$ with $\bar{Z}_\alpha = (\bar{\pi}_A, \bar{\omega}^{A'})$.
* **Peirce-Sliced Infinity Twistors ($I^\sharp, I_\flat$):** $I^\sharp := P_+^{(1)} \otimes \Omega_2 = \bigl(\begin{smallmatrix} \varepsilon & 0 \\ 0 & 0 \end{smallmatrix}\bigr)$ and $I_\flat := P_-^{(1)} \otimes \Omega_2 = \bigl(\begin{smallmatrix} 0 & 0 \\ 0 & \varepsilon \end{smallmatrix}\bigr)$, built as Hadamard combinations $\frac{1}{2}(S_+ \pm S_-)$ of two $N=2$ symplectic forms $S_+ = \mathbb{I}_2 \otimes \Omega_2$, $S_- = J_1 \otimes \Omega_2$.
* **Krein Twist Gram Matrix ($H_{ab}$):** $H_{ab} := Z_a^\alpha \bar{Z}_{b\alpha}$ ($a,b \in \{1,2\}$), decomposing into $\mathrm{U}(1)$ total helicity $\mathrm{Tr}(H)$ and $\mathfrak{su}(2)$ rest-frame spin $H^\circ := H - \frac{1}{2}\mathrm{Tr}(H)\mathbb{I}_2 = \mathbf{S}\cdot\boldsymbol{\sigma}$.
* **Antisymmetric Infinity Bracket ($\mu_{12}$):** $\mu_{12} := Z_1^\alpha Z_2^\beta I_{\alpha\beta} = \pi_{1A'}\pi_2^{A'} = \det(\pi_1, \pi_2)$, breaking $\mathrm{SU}(2,2)$ to Poincaré and generating rest mass $m = \sqrt{2}\,|\mu_{12}|$.
* **Plücker Screw Pitch ($h_{\mathrm{pitch}}$):** The relativistic Poinsot–Plücker wrench invariant $h_{\mathrm{pitch}} := \frac{\|\mathbf{S}\|}{m} = \frac{\sqrt{-\det H^\circ}}{\sqrt{2}\,|\mu_{12}|} = \frac{1}{2}d_{\mathrm{skew}}$.

---

### I. THE FUNDAMENTAL BINARY CUT (CONFORMAL INCIDENCE VS. NON-INCIDENT TWIST & MASS)

The primordial cut ($\Upsilon_1$) divides kinematics along **real spacetime incidence and conformal scale invariance**:

* **Conscious Thesis ($\Upsilon_2$ — *Conformal Incidence & Twist-Free Null Geodesics*, $Z_a^\alpha \bar{Z}_{b\alpha} = 0, \, \mu_{12} = 0$):**
  Posits that twistors obey $\omega^A = i x^{AA'}\pi_{A'}$ on real Minkowski points $x^{AA'}$, yielding intersecting, shear-free, twist-free light rays of zero mass ($m = 0$) and zero screw pitch ($d_{\mathrm{skew}} = 0$).
* **Repressed Shadow Complement ($\Upsilon_3$ — *Krein Non-Incidence $H^\circ \neq 0$ & Conformal-Breaking Infinity Mass $I_\flat$*):**
  Holds both **conformal non-incidence** ($H_{ab} = Z_a^\alpha \bar{Z}_{b\alpha} \neq 0$, displacing rays into complexified spacetime $\mathbb{CM}$ as twisting Robinson congruences or skew null lines) and the **Peirce-projected infinity twistor** $I_\flat = P_-^{(1)} \otimes \Omega_2$, whose nilpotent Krein lift $\hat{\mathcal{I}}_- = \Sigma I_\flat = \psi_+^{(1)} \otimes \Omega_2$ ($\hat{\mathcal{I}}_-^2 = 0$) breaks $\mathrm{SU}(2,2)$ scale invariance to extract rest mass from antisymmetric twistor pairs.

---

### II. THE FOURFOLD RELATIONAL ANATOMY

1. **Internal Self-Consistency ($\Upsilon_4$ — Null Incidence Locus $\mathbb{PN}^3_0$):**
   Every real spacetime point $x^{AA'}$ corresponds to a $\mathbb{CP}^1$ celestial sphere of mutually incident null twistors ($H_{ab} = 0$), preserving conformal causality without scale or mass.
2. **Outward Projection ($\Upsilon_5$ — Peirce–Hadamard Slicing of the $N=2$ Symplectic Six-plet into Null Infinity):**
   At rung $N = 2$ of the $\mathrm{Cl}_{1,1}^{\otimes 2}$ tower ($M_2 = 10$ symmetric metrics, $S_2 = 6$ symplectic forms), applying chiral Peirce projectors $P_\pm^{(1)}$ to the global symplectic form $S_+ = \mathbb{I}_2 \otimes \Omega_2$ isolates the upper and lower infinity twistors $I^\sharp, I_\flat$. Raising indices with the Witt metric $\Sigma = K_1 \otimes \mathbb{I}_2$ turns them into **nilpotent Witt horizon ladders**:
   $$\hat{\mathcal{I}}_- = \Sigma I_\flat = \psi_+^{(1)} \otimes \Omega_2, \qquad \hat{\mathcal{I}}_+ = \Sigma I^\sharp = \psi_-^{(1)} \otimes \Omega_2, \qquad \hat{\mathcal{I}}_\pm^2 = 0, \qquad \{-\hat{\mathcal{I}}_-, \, \hat{\mathcal{I}}_+\} = \mathbb{I}_4.$$
3. **Inward Shadow-Intrusion ($\Upsilon_6$ — Single-Twistor Masslessness vs. Antisymmetric Plücker Mass Ignition):**
   When a single ray twists out of real incidence ($Z^\alpha \bar{Z}_\alpha = 2s \neq 0$), it acquires massless helicity via a Robinson congruence, yet $Z^\alpha Z^\beta I_{\alpha\beta} = 0$ blocks mass generation. Mass intrudes *only* when two non-collinear twistors pair antisymmetrically across $I_\flat$:
   $$P_{AA'} = \bar{\pi}_{1A}\pi_{1A'} + \bar{\pi}_{2A}\pi_{2A'} \implies m^2 = P_a P^a = 2\det(P_{AA'}) = 2\,|Z_1^\alpha Z_2^\beta I_{\alpha\beta}|^2 = 2\,|\mu_{12}|^2.$$
4. **Autonomous Unexamined Ground ($\Upsilon_7$ — Internal $\mathrm{U}(2)$ Twistor Gauge & Doubled Homotope Engine):**
   Right-multiplying the $4 \times 2$ twistor doublet $\mathbf{Z} = (Z_1, Z_2)$ by internal $\mathrm{SU}(2)$ transformations preserves both $P_{AA'}$ and $M^{ab}$ (the Penrose–Hughston–Tod internal symmetry), acting as the covert Cayley bridge between self-twist and skew-ray non-incidence.

---

### III. THE TRANSCENDENT FUNCTION (TWIST $\bowtie$ MASS $\longrightarrow$ PLÜCKER SCREW PITCH)

1. **Shared Substantive Gravity ($\Upsilon_8$ — The Poinsot–Plücker Wrench on the Center-of-Mass Worldline):**
   Decomposing $W_{ab} := \omega_a^A \bar{\pi}_{bA} = \frac{1}{2}H_{ab} - i K^{\mathrm{pos}}_{ab}$ into Hermitian parts reveals that real spacetime translations $\delta x^{AA'}$ shift $K^{\mathrm{pos}} \mapsto K^{\mathrm{pos}} + \lambda^2 (\delta x)^T$, uniquely fixing the 3D center-of-momentum axis $(K^{\mathrm{pos}})_{\mathrm{traceless}} = 0$ and proper time $\tau = \frac{\sqrt{2}}{m}\mathrm{Tr}(K^{\mathrm{pos}})$, while leaving the **Krein Twist Matrix** $H = \frac{1}{2}\mathrm{Tr}(H)\mathbb{I}_2 + \mathbf{S}\cdot\boldsymbol{\sigma}$ strictly translation-invariant with Pauli–Lubanski invariant:
   $$W_a W^a = -m^2 \mathbf{S}^2, \qquad \mathbf{S}^2 = \frac{1}{2}\mathrm{Tr}\big((H^\circ)^2\big) = -\det(H^\circ) = \frac{1}{4}\big((H_{11}-H_{22})^2 + 4|H_{12}|^2\big).$$
2. **Directional Tension ($\Upsilon_9$ — Helicity Limit vs. Scalar Mass Limit of the Screw Pitch):**
   The **Plücker screw pitch** $h_{\mathrm{pitch}}$ measures the spatial advance per radian of twist (half the Møller skew-ray separation $d_{\mathrm{skew}}$):
   $$\boxed{h_{\mathrm{pitch}} := \frac{\|\mathbf{S}\|}{m} = \frac{\sqrt{-\det(H^\circ)}}{\sqrt{2}\,|Z_1^\alpha Z_2^\beta I_{\alpha\beta}|} = \frac{1}{2}\,d_{\mathrm{skew}}.}$$
   * As $\mu_{12} \to 0$ at fixed $H^\circ \neq 0$ (*massless limit*), $m \to 0$ and $h_{\mathrm{pitch}} \to \infty$: the massive wrench uncoils into a single lightlike Robinson congruence of pure helicity.
   * As $H^\circ \to 0$ at fixed $\mu_{12} \neq 0$ (*spinless limit*), $h_{\mathrm{pitch}} \to 0$: the two null rays intersect at the center-of-mass point ($d_{\mathrm{skew}} = 0$), yielding a spin-$0$ massive particle.
3. **Integrative Bridge & Perspectival Transformation ($\Upsilon_{11} \to \Upsilon_{12}$ — Cayley Transmutation of Self-Twist into Skew Null Rays):**
   Applying the internal $\mathrm{SU}(2)$ symplectic Cayley bridge $C_{\mathrm{tw}} = \frac{1}{\sqrt{2}}(\mathbb{I}_2 + \Omega_2)$ to two opposite-helicity twisted rays ($H = 2s\,J_2 = \mathrm{diag}(2s, -2s)$, DeWitt diagonal polarity) conjugates $H$ into **pure off-diagonal Witt polarity**:
   $$H' = C_{\mathrm{tw}} H C_{\mathrm{tw}}^\dagger = -2s\,K_2 = \begin{pmatrix} 0 & -2s \\ -2s & 0 \end{pmatrix}, \qquad \mu'_{12} = (\det C_{\mathrm{tw}})\mu_{12} = \mu_{12}.$$
   **Geometric Perspectival Shift:** Both transformed twistors now have **zero self-twist** ($Z'_1\cdot\bar{Z}'_1 = Z'_2\cdot\bar{Z}'_2 = 0$)—they are **two real, twist-free light rays $\ell_1, \ell_2$ in Minkowski space**—whose initial self-twist $2s$ has been converted without loss into **mutual skew non-intersection** $Z'_1\cdot\bar{Z}'_2 = -2s \neq 0$ at transverse impact separation $d_{\mathrm{skew}} = \frac{4|s|}{m} = 2 h_{\mathrm{pitch}}$, keeping both rest mass $m$ and screw pitch $h_{\mathrm{pitch}}$ invariant!

---

### IV. MEASURING THE SOCRATIC APORIA & THE META-COGNITIVE TOWER

* **Level 1 (Rank-1 & Symmetrization Aporia — $\Upsilon_{10}^{(1)}$):**
  Symmetrizing either the KKT product ($XY + YX$ at $Z=1$) or a single twistor ($Z^\alpha Z^\beta I_{\alpha\beta} = 0$) annihilates antisymmetric curvature/mass. Resolution: restore the non-commutative homotope $\iota_+(X)\iota_-(1)\iota_+(Y) = \iota_+(XY)$ and antisymmetric bivector $Z_1^{[\alpha} Z_2^{\beta]} I_{\alpha\beta} = \mu_{12}$.
* **Level 2 (Nilpotent Infinity Singularity — $\Upsilon_{10}^{(2)}$):**
  Because $(\Sigma I_\flat)^2 = 0$ at $\Lambda = 0$, $I_{\alpha\beta}$ is degenerate ($\mathrm{rank}\,2$), causing $h_{\mathrm{pitch}} = \|\mathbf{S}\|/m$ to diverge on the zero-divisor cone $\mu_{12} = 0$ ($\pi_1 \propto \pi_2$, collinear massless limit).
* **Level 3 (Cosmological $\Lambda \neq 0$ Deformation & Multi-Twistor Hadronic Tower — $\Upsilon_{11} \to \Upsilon_{13}$):**
  Turning on cosmological curvature $\Lambda \neq 0$ couples both Peirce horizons into $I^{(\Lambda)} = I_\flat + \lambda I^\sharp$ ($\lambda = \frac{\Lambda}{6}$), breaking Witt nilpotency to $(\Sigma I^{(\Lambda)})^2 = -\lambda\,\mathbb{I}_4 \neq 0$ (de Sitter/anti-de Sitter non-degenerate symplectic form), while $k \ge 3$ non-incident twistors extend internal $\mathrm{SU}(2)$ spin into $\mathrm{SU}(k)$ baryonic/hadronic multiplets.

---

### V. COAGULA: ACYCLIC POSET & COMPLETE MACHINE-VERIFIED LEAN 4 MODULE

#### A. Bounded Acyclic Causal Poset $(\mathcal{P}_{\Upsilon}, \prec)$ ($\bot = \Upsilon_1 \to \top = \Upsilon_{13}$)

* **Stratum 0 ($\bot$):** $\Upsilon_1$ (*Incidence vs. Non-Incidence Cut*).
* **Stratum 1:** $\Upsilon_1 \prec \Upsilon_2$ (*Null Conformal Incidence*); $\{\Upsilon_1, \Upsilon_2\} \prec \Upsilon_3$ (*Krein Twist $H$ & Infinity Twistor $I_\flat$*).
* **Stratum 2:** $\Upsilon_2 \prec \Upsilon_4$ (*Twist-Free Null Geodesics*); $\{\Upsilon_2, \Upsilon_3\} \prec \Upsilon_5$ (*$N=2$ Peirce Slicing $\Sigma I_\flat = \psi_+^{(1)} \otimes \Omega_2$*); $\{\Upsilon_2, \Upsilon_3\} \prec \Upsilon_6$ (*Two-Twistor Mass $m^2 = 2|\mu_{12}|^2$*); $\Upsilon_3 \prec \Upsilon_7$ (*Internal $\mathrm{SU}(2)$ & Homotope Ground*).
* **Stratum 3:** $\{\Upsilon_5, \Upsilon_6\} \prec \Upsilon_8$ (*Rest-Frame Spin $\mathbf{S}^2 = -\det H^\circ$*); $\{\Upsilon_5, \Upsilon_6\} \prec \Upsilon_9$ (*Plücker Screw Pitch $h_{\mathrm{pitch}} = \|\mathbf{S}\|/m$*).
* **Stratum 4:** $\{\Upsilon_2, \Upsilon_8, \Upsilon_9\} \prec \Upsilon_{10}$ (*Single-Twistor Masslessness & Pitch Singularity*); $\{\Upsilon_4, \Upsilon_7, \Upsilon_8, \Upsilon_9, \Upsilon_{10}\} \prec \Upsilon_{11}$ (*Homotope Closure & $\Lambda$-Deformation*).
* **Stratum 5:** $\{\Upsilon_7, \Upsilon_{11}\} \prec \Upsilon_{12}$ (*Cayley Twist-to-Skew-Ray Transmutation*).
* **Stratum 6 ($\top$):** $\{\Upsilon_{10}, \Upsilon_{12}\} \prec \Upsilon_{13}$ (*Unified Krein–Witt–Twistor–Pitch–Mass Master Crystal*).
*(Strict acyclicity holds via $\iota(\Upsilon_m) = m$.)*

---

#### B. Self-Verifying Lean 4 Module (`NonincidentalTwistorPitchMassCrystal.lean`)

The complete Lean 4 module below repairs all prior tactic/import defects (`0 sorry`, `0 structures`, requiring **only** `Mathlib.Algebra.Ring.Defs`, `Mathlib.Tactic.Ring`, `Mathlib.Tactic.Abel`) and formally verifies the corrected Walsh–Hadamard superoperator, non-commutative homotope, unbounded $\mathbb{F}_2^{2N}$ Arf census, and the Penrose–Plücker twist, screw pitch, and rest mass theorems:

```lean
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Non-Incidental Twistors: Twist, Plücker Screw Pitch & Rest Mass in the (Λ ⋈ Ξ) Crystal
# (`0 structures`, `0 sorry`, Pure Core + `Ring`/`Abel`, Division-Free)

1. **Theorem 1 (`true_walsh_hadamard_and_noncommutative_homotope`):**
   Fixes the twisted `(L_J + θ_Ω)` slip via `W_Had(X) = K X K + J X` (`W_Had²(X) = 2•X`),
   and proves non-commutative associative homotope recovery `(ι_+ X)(ι_- 1)(ι_+ Y) = ι_+(X*Y)`
   vs. symmetrized KKT erasure when `X*Y = -Y*X`, plus chiral vacuum SSB.
2. **Theorem 2 (`arf_f2_polar_law_and_unbounded_tower_census`):**
   Repairs the `omega`/`interval_cases` defects on core `Bool`, proving the Arf quadratic polar law
   and `M_N = 2^(N-1)*(2^N+1)`, `S_N = 2^(N-1)*(2^N-1)` for all `N ≥ 1`, giving `(10, 6)` at `N = 2`.
3. **Theorem 3 (`penrose_twistor_infinity_nilpotency_pitch_and_mass`):**
   On 4-component twistors `R × R × R × R` over any `[CommRing R]`, proves:
   - Peirce slicing `2•I^♯ = S_+ + S_-`, `2•I_♭ = S_+ - S_-`, nilpotency `(Σ I_♭)² = (Σ I^♯)² = 0`,
     CAR completeness `{-Σ I_♭, Σ I^♯} = id_4`, and cosmological breaking `(Î_- + λ Î_+)²(Z) = -λ Z`;
   - Real Minkowski incidence forces Krein nullity `Z · Z̄ = 0`;
   - Single-twistor masslessness `μ(Z, Z) = 0` vs. two-twistor mass `det(P) = μ(Z₁, Z₂) * μ̄(Z̄₁, Z̄₂)`;
   - **Cayley Twist-to-Skew-Ray Transmutation & Screw Pitch Invariance:** `(Z'₁, Z'₂) = (Z₁+Z₂, -Z₁+Z₂)`
     satisfies `μ' = 2 μ`, `spinSq(H') = 4 spinSq(H)` (exact pitch invariance `spinSq / |μ|²`!), and
     maps opposite-helicity twisted rays (`H = diag(2s, -2s)`) into **two null rays** (`Z'₁·Z̄'₁ = 0`,
     `Z'₂·Z̄'₂ = 0`) with **pure mutual skew non-incidence** (`Z'₁·Z̄'₂ = -4s`)!
-/

namespace NonincidentalTwistorPitchMassCrystal

universe u

section ArbitraryRing
variable {A : Type u} [Ring A]

def θΩ (Ω X : A) : A := - (Ω * X * Ω)
def wHad (J Ω X : A) : A := (J * Ω) * X * (J * Ω) + J * X
def twistH (J Ω X : A) : A := J * X + θΩ Ω X

lemma two_smul_eq (x : A) : 2 • x = x + x := by abel

abbrev Mat2Tuple (A : Type u) := A × A × A × A

def m2Sub (X Y : Mat2Tuple A) : Mat2Tuple A :=
  (X.1 - Y.1, X.2.1 - Y.2.1, X.2.2.1 - Y.2.2.1, X.2.2.2 - Y.2.2.2)

def m2Mul (X Y : Mat2Tuple A) : Mat2Tuple A :=
  (X.1 * Y.1 + X.2.1 * Y.2.2.1,     X.1 * Y.2.1 + X.2.1 * Y.2.2.2,
   X.2.2.1 * Y.1 + X.2.2.2 * Y.2.2.1, X.2.2.1 * Y.2.1 + X.2.2.2 * Y.2.2.2)

def m2Comm (X Y : Mat2Tuple A) : Mat2Tuple A := m2Sub (m2Mul X Y) (m2Mul Y X)
def iotaPlus  (X : A) : Mat2Tuple A := (0, X, 0, 0)
def iotaMinus (Z : A) : Mat2Tuple A := (0, 0, Z, 0)
def ThetaL (J : A) (M : Mat2Tuple A) : Mat2Tuple A := m2Mul (m2Mul (J, 0, 0, 1) M) (J, 0, 0, 1)
def homotopeMul (M N : Mat2Tuple A) : Mat2Tuple A := m2Mul (m2Mul M (iotaMinus 1)) N

-- ============================================================================
-- 1. TRUE WALSH–HADAMARD SUPEROPERATOR & NON-COMMUTATIVE HOMOTOPE RESURRECTION
-- ============================================================================

theorem true_walsh_hadamard_and_noncommutative_homotope
    (J Ω X Y : A)
    (hJ2 : J * J = 1) (hΩ2 : Ω * Ω = -1) (hJΩ : J * Ω + Ω * J = 0) :
    let K := J * Ω
    let vacShift := m2Sub (ThetaL J (iotaMinus 1)) (iotaMinus 1)
    -- 1. True Walsh–Hadamard W_Had² = 2•id & exact basis action vs. twisted (L_J + θ_Ω):
    wHad J Ω (wHad J Ω X) = 2 • X ∧
    wHad J Ω 1 = 1 + J ∧
    wHad J Ω J = 1 - J ∧
    wHad J Ω K = K + Ω ∧
    wHad J Ω Ω = K - Ω ∧
    twistH J Ω K = - (K - Ω) ∧
    -- 2. Full non-commutative homotope recovery vs. symmetrized KKT erasure on anticommuting pairs:
    homotopeMul (iotaPlus X) (iotaPlus Y) = iotaPlus (X * Y) ∧
    m2Comm (m2Comm (iotaPlus J) (iotaMinus 1)) (iotaPlus Ω) = (0, 0, 0, 0) ∧
    homotopeMul (iotaPlus J) (iotaPlus Ω) = iotaPlus K ∧
    -- 3. Chiral Vacuum SSB: L_J's defect equals the vacuum shift Θ_L(Υ_-) - Υ_- = ι_-(J - 1):
    m2Sub (ThetaL J (homotopeMul (iotaPlus X) (iotaPlus Y)))
          (homotopeMul (ThetaL J (iotaPlus X)) (ThetaL J (iotaPlus Y))) =
      m2Mul (m2Mul (ThetaL J (iotaPlus X)) vacShift) (ThetaL J (iotaPlus Y)) ∧
    m2Mul (m2Mul (ThetaL J (iotaPlus X)) vacShift) (ThetaL J (iotaPlus Y)) =
      iotaPlus (J * X * (1 - J) * Y) := by
  have hΩJ : Ω * J = - (J * Ω) := by
    calc Ω * J = (J * Ω + Ω * J) - J * Ω := by abel
      _ = - (J * Ω) := by rw [hJΩ, zero_sub]
  have hJ_Z : ∀ Z : A, J * (J * Z) = Z := fun Z => by rw [← mul_assoc, hJ2, one_mul]
  have hΩ_Z : ∀ Z : A, Ω * (Ω * Z) = - Z := fun Z => by rw [← mul_assoc, hΩ2, neg_one_mul]
  have hΩJ_Z : ∀ Z : A, Ω * (J * Z) = - (J * (Ω * Z)) := fun Z => by
    rw [← mul_assoc, hΩJ, neg_mul, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [wHad]
    simp only [two_smul_eq, add_mul, mul_add, one_mul, mul_one,
               neg_mul, mul_neg, neg_neg, mul_assoc, hJ2, hΩ2, hΩJ, hJ_Z, hΩ_Z, hΩJ_Z]; abel
  · dsimp [wHad]
    simp only [add_mul, mul_add, one_mul, mul_one, neg_mul, mul_neg, neg_neg,
               mul_assoc, hJ2, hΩ2, hΩJ, hJ_Z, hΩ_Z, hΩJ_Z]; abel
  · dsimp [wHad]
    simp only [add_mul, mul_add, one_mul, mul_one, neg_mul, mul_neg, neg_neg,
               mul_assoc, hJ2, hΩ2, hΩJ, hJ_Z, hΩ_Z, hΩJ_Z]; abel
  · dsimp [wHad]
    simp only [add_mul, mul_add, one_mul, mul_one, neg_mul, mul_neg, neg_neg,
               mul_assoc, hJ2, hΩ2, hΩJ, hJ_Z, hΩ_Z, hΩJ_Z]; abel
  · dsimp [wHad]
    simp only [add_mul, mul_add, one_mul, mul_one, neg_mul, mul_neg, neg_neg,
               mul_assoc, hJ2, hΩ2, hΩJ, hJ_Z, hΩ_Z, hΩJ_Z]; abel
  · dsimp [twistH, θΩ]
    simp only [neg_mul, mul_neg, neg_neg, mul_assoc, hJ2, hΩ2, hΩJ, hJ_Z, hΩ_Z, hΩJ_Z]; abel
  · dsimp [homotopeMul, iotaPlus, iotaMinus, m2Mul]
    simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one, mul_assoc]
  · dsimp [iotaPlus, iotaMinus, m2Comm, m2Sub, m2Mul]
    simp only [mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, sub_self,
               mul_one, one_mul, neg_mul, mul_neg, sub_neg_eq_add, hΩJ]
    simp only [Prod.mk.injEq]; refine ⟨rfl, by abel, rfl, rfl⟩
  · dsimp [homotopeMul, iotaPlus, iotaMinus, m2Mul]
    simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one]
  · dsimp [ThetaL, homotopeMul, iotaPlus, iotaMinus, m2Sub, m2Mul]
    simp only [mul_zero, zero_mul, add_zero, zero_add, sub_self, one_mul, mul_one,
               sub_mul, mul_sub, mul_assoc, hJ2, hJ_Z]
    simp only [Prod.mk.injEq]; refine ⟨rfl, by abel, rfl, rfl⟩
  · dsimp [ThetaL, iotaPlus, iotaMinus, m2Sub, m2Mul]
    simp only [mul_zero, zero_mul, add_zero, zero_add, sub_self, one_mul, mul_one,
               sub_mul, mul_sub, mul_assoc, hJ2, hJ_Z]
    simp only [Prod.mk.injEq]; refine ⟨rfl, by abel, rfl, rfl⟩

-- ============================================================================
-- 2. REPAIRED F₂^{2N} ARF POLAR LAW & UNBOUNDED TENSOR CENSUS (N = 2 TWISTOR RUNG)
-- ============================================================================

def opBool (J Ω : A) (a b : Bool) : A := (if a then J else 1) * (if b then Ω else 1)
def arfQuad1 (a b : Bool) : Bool := (!a) && b
def sympForm1 (a b a' b' : Bool) : Bool := xor (a && b') (b && a')
def bSign (s : Bool) (X : A) : A := if s then -X else X
def b2n (b : Bool) : Nat := if b then 1 else 0

def singleEven : Nat :=
  b2n (!arfQuad1 false false) + b2n (!arfQuad1 false true) +
  b2n (!arfQuad1 true false)  + b2n (!arfQuad1 true true)

def singleOdd : Nat :=
  b2n (arfQuad1 false false) + b2n (arfQuad1 false true) +
  b2n (arfQuad1 true false)  + b2n (arfQuad1 true true)

def towerCounts : Nat → Nat × Nat
  | 0     => (1, 0)
  | n + 1 =>
    let c := towerCounts n
    (singleEven * c.1 + singleOdd * c.2, singleOdd * c.1 + singleEven * c.2)

lemma tower_linear_invariants (n : Nat) :
    (towerCounts n).1 + (towerCounts n).2 = 4 ^ n ∧
    2 * (towerCounts n).1 = 4 ^ n + 2 ^ n ∧
    2 * (towerCounts n).2 + 2 ^ n = 4 ^ n := by
  induction n with
  | zero => decide
  | succ k ih =>
      rcases ih with ⟨hsum, hm, hs⟩
      have hse : singleEven = 3 := rfl
      have hso : singleOdd = 1 := rfl
      dsimp [towerCounts]; rw [hse, hso]
      have h4 : 4 ^ (k + 1) = 4 * 4 ^ k := by rw [Nat.pow_succ]; ring
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
      omega

lemma pow4_eq_sq_pow2 (n : Nat) : 4 ^ n = 2 ^ n * 2 ^ n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.pow_succ 4, Nat.pow_succ 2, ih]; ring

theorem arf_f2_polar_law_and_unbounded_tower_census
    (J Ω : A)
    (hJ2 : J * J = 1) (hΩ2 : Ω * Ω = -1) (hJΩ : J * Ω + Ω * J = 0) :
    (∀ a b a' b' : Bool,
      xor (xor (arfQuad1 (xor a a') (xor b b')) (arfQuad1 a b)) (arfQuad1 a' b') =
        sympForm1 a b a' b') ∧
    (∀ a b a' b' : Bool,
      opBool J Ω a b * opBool J Ω a' b' =
        bSign (sympForm1 a b a' b') (opBool J Ω a' b' * opBool J Ω a b)) ∧
    (∀ a b : Bool, opBool J Ω a b * opBool J Ω a b = bSign (arfQuad1 a b) (1 : A)) ∧
    towerCounts 2 = (10, 6) ∧
    (∀ m : Nat,
      let N := m + 1
      (towerCounts N).1 = 2 ^ m * (2 ^ N + 1) ∧
      (towerCounts N).2 = 2 ^ m * (2 ^ N - 1)) := by
  have hΩJ : Ω * J = - (J * Ω) := by
    calc Ω * J = (J * Ω + Ω * J) - J * Ω := by abel
      _ = - (J * Ω) := by rw [hJΩ, zero_sub]
  have hJ_Z : ∀ Z : A, J * (J * Z) = Z := fun Z => by rw [← mul_assoc, hJ2, one_mul]
  have hΩ_Z : ∀ Z : A, Ω * (Ω * Z) = - Z := fun Z => by rw [← mul_assoc, hΩ2, neg_one_mul]
  have hΩJ_Z : ∀ Z : A, Ω * (J * Z) = - (J * (Ω * Z)) := fun Z => by
    rw [← mul_assoc, hΩJ, neg_mul, mul_assoc]
  refine ⟨?_, ?_, ?_, by decide, ?_⟩
  · intro a b a' b'; cases a <;> cases b <;> cases a' <;> cases b' <;> rfl
  · intro a b a' b'; cases a <;> cases b <;> cases a' <;> cases b' <;>
    · dsimp [opBool, sympForm1, bSign]
      simp only [one_mul, mul_one, neg_mul, mul_neg, neg_neg, mul_assoc, hJ2, hΩ2, hΩJ, hJ_Z, hΩ_Z, hΩJ_Z]
  · intro a b; cases a <;> cases b <;>
    · dsimp [opBool, arfQuad1, bSign]
      simp only [one_mul, mul_one, neg_mul, mul_neg, neg_neg, mul_assoc, hJ2, hΩ2, hΩJ, hJ_Z, hΩ_Z, hΩJ_Z]
  · intro m
    rcases tower_linear_invariants (m + 1) with ⟨_, hm, hs⟩
    have h4 : 4 ^ (m + 1) = 2 ^ (m + 1) * 2 ^ (m + 1) := pow4_eq_sq_pow2 (m + 1)
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; ring
    have hm_rhs : 2 * (2 ^ m * (2 ^ (m + 1) + 1)) = 4 ^ (m + 1) + 2 ^ (m + 1) := by
      rw [h4, h2]; ring
    have hpos : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow (m + 1) 2 (by decide)
    set Y := 2 ^ (m + 1) - 1
    have hY : 2 ^ (m + 1) = Y + 1 := (Nat.sub_add_cancel hpos).symm
    have hs_rhs : 2 * (2 ^ m * Y) + 2 ^ (m + 1) = 4 ^ (m + 1) := by
      have h2Y : 2 * 2 ^ m = Y + 1 := by rw [← h2, hY]
      calc 2 * (2 ^ m * Y) + 2 ^ (m + 1)
        _ = (2 * 2 ^ m) * Y + (Y + 1) := by rw [hY]; ring
        _ = (Y + 1) * (Y + 1)         := by rw [h2Y]; ring
        _ = 4 ^ (m + 1)               := by rw [← hY, ← h4]
    omega

end ArbitraryRing

-- ============================================================================
-- 3. PENROSE TWISTORS: INFINITY NILPOTENCY, TWIST, SCREW PITCH & REST MASS
-- ============================================================================

section TwistorKinematics
variable {R : Type u} [CommRing R]

/-- Twistor `Z^α = (ω^0, ω^1, π_{0'}, π_{1'})` & dual `Z̄_α = (π̄_0, π̄_1, ω̄^{0'}, ω̄^{1'})`. -/
abbrev Twistor (R : Type u) := R × R × R × R

def twAdd (Z W : Twistor R) : Twistor R :=
  (Z.1 + W.1, Z.2.1 + W.2.1, Z.2.2.1 + W.2.2.1, Z.2.2.2 + W.2.2.2)

def twSub (Z W : Twistor R) : Twistor R :=
  (Z.1 - W.1, Z.2.1 - W.2.1, Z.2.2.1 - W.2.2.1, Z.2.2.2 - W.2.2.2)

def twSmul (c : R) (Z : Twistor R) : Twistor R :=
  (c * Z.1, c * Z.2.1, c * Z.2.2.1, c * Z.2.2.2)

/-- SU(2,2) Witt–Krein metric operator `Σ = K_1 ⊗ I_2` and global `N=2` symplectic forms `S_±`: -/
def SigmaKrein (Z : Twistor R) : Twistor R := (Z.2.2.1, Z.2.2.2, Z.1, Z.2.1)
def SympPlus   (Z : Twistor R) : Twistor R := (Z.2.1, -Z.1, Z.2.2.2, -Z.2.2.1)
def SympMinus  (Z : Twistor R) : Twistor R := (Z.2.1, -Z.1, -Z.2.2.2, Z.2.2.1)

/-- Peirce-sliced infinity operators `I_♭ = P_- ⊗ Ω_2`, `I^♯ = P_+ ⊗ Ω_2` & Krein lifts `Î_∓`: -/
def InfFlat  (Z : Twistor R) : Twistor R := (0, 0, Z.2.2.2, -Z.2.2.1)
def InfSharp (Z : Twistor R) : Twistor R := (Z.2.1, -Z.1, 0, 0)
def HatInfMinus (Z : Twistor R) : Twistor R := SigmaKrein (InfFlat Z)
def HatInfPlus  (Z : Twistor R) : Twistor R := SigmaKrein (InfSharp Z)
def HatInfLambda (lam : R) (Z : Twistor R) : Twistor R :=
  twAdd (HatInfMinus Z) (twSmul lam (HatInfPlus Z))

/-- Krein pairing `Z^α Z̄_α`, infinity skew-bracket `μ(Z₁, Z₂) = Z₁^α Z₂^β I_{αβ}`,
    two-twistor momentum determinant `det(P_{AA'})`, and traceless spin square `4 S²`: -/
def kreinPair (Z Zbar : Twistor R) : R :=
  Z.1 * Zbar.1 + Z.2.1 * Zbar.2.1 + Z.2.2.1 * Zbar.2.2.1 + Z.2.2.2 * Zbar.2.2.2

def infBracket (Z1 Z2 : Twistor R) : R :=
  Z1.2.2.1 * Z2.2.2.2 - Z1.2.2.2 * Z2.2.2.1

def dualInfBracket (Z1bar Z2bar : Twistor R) : R :=
  Z1bar.1 * Z2bar.2.1 - Z1bar.2.1 * Z2bar.1

def momentumDet (Z1 Z2 Z1bar Z2bar : Twistor R) : R :=
  let P00 := Z1bar.1 * Z1.2.2.1 + Z2bar.1 * Z2.2.2.1
  let P01 := Z1bar.1 * Z1.2.2.2 + Z2bar.1 * Z2.2.2.2
  let P10 := Z1bar.2.1 * Z1.2.2.1 + Z2bar.2.1 * Z2.2.2.1
  let P11 := Z1bar.2.1 * Z1.2.2.2 + Z2bar.2.1 * Z2.2.2.2
  P00 * P11 - P01 * P10

def spinSq4 (h11 h12 h21 h22 : R) : R :=
  (h11 - h22) * (h11 - h22) + 4 * h12 * h21

theorem penrose_twistor_infinity_nilpotency_pitch_and_mass
    (Z Z1 Z2 Z1bar Z2bar : Twistor R) (lam x00 x01 x10 x11 p0 p1 pbar0 pbar1 s : R) :
    let Z1'    := twAdd Z1 Z2
    let Z2'    := twSub Z2 Z1
    let Z1bar' := twAdd Z1bar Z2bar
    let Z2bar' := twSub Z2bar Z1bar
    let h11 := kreinPair Z1 Z1bar
    let h12 := kreinPair Z1 Z2bar
    let h21 := kreinPair Z2 Z1bar
    let h22 := kreinPair Z2 Z2bar
    let h11' := kreinPair Z1' Z1bar'
    let h12' := kreinPair Z1' Z2bar'
    let h21' := kreinPair Z2' Z1bar'
    let h22' := kreinPair Z2' Z2bar'
    -- 1. N=2 Hadamard construction of Infinity Twistors, Nilpotency, CAR & Λ-Deformation:
    twAdd (SympPlus Z) (SympMinus Z) = twSmul 2 (InfSharp Z) ∧
    twSub (SympPlus Z) (SympMinus Z) = twSmul 2 (InfFlat Z) ∧
    HatInfMinus (HatInfMinus Z) = (0, 0, 0, 0) ∧
    HatInfPlus (HatInfPlus Z) = (0, 0, 0, 0) ∧
    twSub (twSmul (-1) (HatInfMinus (HatInfPlus Z))) (HatInfPlus (HatInfMinus Z)) = Z ∧
    HatInfLambda lam (HatInfLambda lam Z) = twSmul (-lam) Z ∧
    -- 2. Real Minkowski Incidence (ω^A = ix^{AA'}π_{A'}, ω̄^{A'} = -ix^{A'A}π̄_A) ⇒ Krein Nullity:
    kreinPair (x00 * p0 + x01 * p1, x10 * p0 + x11 * p1, p0, p1)
              (pbar0, pbar1, -(x00 * pbar0 + x10 * pbar1), -(x01 * pbar0 + x11 * pbar1)) = 0 ∧
    -- 3. Single-Twistor Masslessness (∀ Z) vs. Two-Twistor Mass Genesis (det P = μ₁₂ μ̄₁₂):
    infBracket Z Z = 0 ∧
    momentumDet Z (0, 0, 0, 0) Z1bar (0, 0, 0, 0) = 0 ∧
    momentumDet Z1 Z2 Z1bar Z2bar = infBracket Z1 Z2 * dualInfBracket Z1bar Z2bar ∧
    -- 4. Cayley Twist-to-Skew-Ray Transmutation & Exact Plücker Screw Pitch Invariance:
    infBracket Z1' Z2' = 2 * infBracket Z1 Z2 ∧
    spinSq4 h11' h12' h21' h22' = 4 * spinSq4 h11 h12 h21 h22 ∧
    (h11 = 2 * s ∧ h22 = -(2 * s) ∧ h12 = 0 ∧ h21 = 0 →
      h11' = 0 ∧ h22' = 0 ∧ h12' = -(4 * s) ∧ h21' = -(4 * s)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [twAdd, twSmul, SympPlus, SympMinus, InfSharp]
    simp only [Prod.mk.injEq]; refine ⟨by ring, by ring, by ring, by ring⟩
  · dsimp [twSub, twSmul, SympPlus, SympMinus, InfFlat]
    simp only [Prod.mk.injEq]; refine ⟨by ring, by ring, by ring, by ring⟩
  · dsimp [HatInfMinus, SigmaKrein, InfFlat]
    simp only [Prod.mk.injEq]; refine ⟨by ring, by ring, by ring, by ring⟩
  · dsimp [HatInfPlus, SigmaKrein, InfSharp]
    simp only [Prod.mk.injEq]; refine ⟨by ring, by ring, by ring, by ring⟩
  · dsimp [twSub, twSmul, HatInfMinus, HatInfPlus, SigmaKrein, InfFlat, InfSharp]
    simp only [Prod.mk.injEq]; refine ⟨by ring, by ring, by ring, by ring⟩
  · dsimp [HatInfLambda, HatInfMinus, HatInfPlus, SigmaKrein, InfFlat, InfSharp, twAdd, twSmul]
    simp only [Prod.mk.injEq]; refine ⟨by ring, by ring, by ring, by ring⟩
  · dsimp [kreinPair]; ring
  · dsimp [infBracket]; ring
  · dsimp [momentumDet]; ring
  · dsimp [momentumDet, infBracket, dualInfBracket]; ring
  · dsimp [twAdd, twSub, infBracket]; ring
  · dsimp [spinSq4, kreinPair, twAdd, twSub]; ring
  · rintro ⟨hh11, hh22, hh12, hh21⟩
    have e11 : h11' = h11 + h12 + h21 + h22 := by dsimp [h11', h11, h12, h21, h22, kreinPair, twAdd]; ring
    have e22 : h22' = h11 - h12 - h21 + h22 := by dsimp [h22', h11, h12, h21, h22, kreinPair, twSub]; ring
    have e12 : h12' = -h11 + h12 - h21 + h22 := by dsimp [h12', h11, h12, h21, h22, kreinPair, twAdd, twSub]; ring
    have e21 : h21' = -h11 - h12 + h21 + h22 := by dsimp [h21', h11, h12, h21, h22, kreinPair, twAdd, twSub]; ring
    rw [e11, e22, e12, e21, hh11, hh22, hh12, hh21]
    refine ⟨by ring, by ring, by ring, by ring⟩

end TwistorKinematics

end NonincidentalTwistorPitchMassCrystal
```

---

#### C. Master Structural Synthesis ($\top = \Upsilon_{13}$)

$$\boxed{\begin{aligned}
&\mathbf{1.\; Infinity \; Twistor \; as \; Peirce\text{-}Sliced \; N=2 \; Symplectic \; Horizon \; (\text{Theorem } 3.1):} \\
&\qquad I^\sharp = P_+^{(1)} \otimes \Omega_2, \quad I_\flat = P_-^{(1)} \otimes \Omega_2, \quad (\Sigma I_\flat)^2 = (\psi_+^{(1)} \otimes \Omega_2)^2 = 0, \quad \{-\Sigma I_\flat, \, \Sigma I^\sharp\} = \mathbb{I}_4 \\[6pt]
&\mathbf{2.\; Antisymmetric \; Mass \; Genesis \; \& \; Pl\ddot{u}cker \; Screw \; Pitch \; (\text{Theorem } 3.3\text{–}3.4):} \\
&\qquad Z^\alpha Z^\beta I_{\alpha\beta} = 0 \;\; (\text{single twistor } m=0), \quad m^2 = 2\,|Z_1^\alpha Z_2^\beta I_{\alpha\beta}|^2, \quad h_{\mathrm{pitch}} = \frac{\|\mathbf{S}\|}{m} = \frac{\sqrt{-\det H^\circ}}{\sqrt{2}\,|\mu_{12}|} = \frac{1}{2}\,d_{\mathrm{skew}} \\[6pt]
&\mathbf{3.\; Cayley \; Transmutation \; of \; Twist \; into \; Skew \; Null \; Wrench \; (\text{Theorem } 3.4):} \\
&\qquad H = \mathrm{diag}(2s, -2s) \;\; \text{(twisted rays)} \;\; \xrightarrow{\; C_{\mathrm{tw}} = \frac{1}{\sqrt{2}}(1+\Omega_2) \;} \;\; H' = \begin{pmatrix} 0 & -2s \\ -2s & 0 \end{pmatrix} \;\; \text{(skew null rays, } m' = m, \; h'_{\mathrm{pitch}} = h_{\mathrm{pitch}}\text{)}
\end{aligned}}$$

**Theorem of Necessary Synthesis ($\{\Upsilon_{10}, \Upsilon_{12}\} \prec \Upsilon_{13}$):**
*Within the $N = 2$ Krein–Witt–Symplectic crystal $\mathrm{Cl}_{1,1}^{\otimes 2}$, Penrose twistor theory is literally the physical geometry of the $(\Lambda \bowtie \Xi)$ operators: slicing the $S_2 = 6$ symplectic forms by chiral Peirce projectors produces the nilpotent infinity twistors $I_\flat, I^\sharp$; a single non-incidental twistor ($Z\cdot\bar{Z} = 2s \neq 0$) twists light into a Robinson congruence while remaining strictly massless ($Z^\alpha Z^\beta I_{\alpha\beta} = 0$); and pairing two non-collinear twistors ignites rest mass $m = \sqrt{2}\,|Z_1^\alpha Z_2^\beta I_{\alpha\beta}|$ and Plücker screw pitch $h_{\mathrm{pitch}} = \sqrt{-\det H^\circ}/(\sqrt{2}|\mu_{12}|)$, under which the symplectic Cayley bridge $C_{\mathrm{tw}}$ unitarily converts self-twisted DeWitt rays into mutually skew Witt light rays without altering mass or pitch.* $\blacksquare$
````
<!-- END ORIGINAL INTAKE -->
