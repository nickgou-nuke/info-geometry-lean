# 🌌 InfoGeometry
### *Lean 4 Formalization of Pregeometric Spinorial Prima Materia*

[![Lean 4](https://img.shields.io/badge/Lean_4-v4.28.1-success?style=flat-square&logo=lean)](https://github.com/leanprover/lean4)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.1-blue?style=flat-square)](https://github.com/leanprover-community/mathlib4)
[![Zero-Debt](https://img.shields.io/badge/Axioms-0_%28Zero--Debt%29-brightgreen?style=flat-square)](#)
[![Files Clean](https://img.shields.io/badge/Clean_Modules-20%2C343_%28100%25%29-success?style=flat-square)](#)

> **A Living Artifact of Human–AI Interaction**  
> *This repository is a living artifact of human–AI interaction. It is an attempt to explore and formalize in Lean 4 concepts spanning pure mathematics, theoretical physics, formal theorem proving, and language models—and to uncover the deep interconnections binding them together. Take with a pinch of salt, explore with an open mind.*

---

## 🏛️ What is this?

This repository contains the machine-verified mathematical architecture of **Information Geometry applied to Pregeometric Spinorial Prima Materia**.

Rather than postulating a continuous, smooth spacetime manifold as an a priori background, spacetime coordinates $X^\mu$, the metric tensor $g_{\mu\nu}$, and physical gauge symmetries emerge as **macroscopic expectation values (Dirac-Krein spinor bilinears)** over non-associative and non-commutative operator envelopes acting on indefinite Krein spaces:

$$\boxed{ \text{Zorn } \mathbb{O}_s \;\longrightarrow\; \operatorname{Cl}(3,3) \;\longrightarrow\; \text{Twistors } \mathbb{T}(\mathbb{O}_s) \;\longrightarrow\; \operatorname{Cl}(5,5) \;\longrightarrow\; \text{Metriplectic Engine} \;\longrightarrow\; \text{Modular Curvature} }$$

Every algebraic identity, dimension count, and geometric bridge across the entire repository is certified by the **Lean 4 kernel** with **0 custom axioms** and **0 `sorry`s**.

---

## 💎 The Six Foundational Pillars

### 1. The Prime Dials & $N$-Potent Spectral Hierarchy
Algebraic factorization and idempotent decomposition $X^p = X$ over primes $p \in \{2, 3, 5, 7, 11, 13\}$, governing mass idempotents, chirality, twin-doubling, Fano quarks, 10D conformal strings, and the 12 roots of $G_2$.
* **Modules**: [`lean/InfoGeometry/Algebra/NoncommutativePolynomialPlaneWaveKernel.lean`](lean/InfoGeometry/Algebra/NoncommutativePolynomialPlaneWaveKernel.lean), [`lean/InfoGeometry/Arithmetic/ModularRingSpectralDecomposition.lean`](lean/InfoGeometry/Arithmetic/ModularRingSpectralDecomposition.lean)

### 2. The Circular Chiral Causal Basis & $V_4$ Bigrading
The 8D split-octonionic light-cone basis $(u^\pm, \sigma_1^\pm, \sigma_2^\pm, \sigma_3^\pm)$ exhibiting CAR supercharge relations $\{ \sigma_i^+, \sigma_j^- \} = \delta_{ij} u^+$ and a non-abelian $V_4 \cong \mathbb{Z}_2 \times \mathbb{Z}_2$ contact-chiral bigrading with 4 mutually orthogonal spectral projectors ($P_{++} + P_{+-} + P_{-+} + P_{--} = 1$).
* **Modules**: [`lean/InfoGeometry/Exceptional/V4ContactBigrading.lean`](lean/InfoGeometry/Exceptional/V4ContactBigrading.lean), [`lean/InfoGeometry/Exceptional/CircularSplitOctonionContactLift.lean`](lean/InfoGeometry/Exceptional/CircularSplitOctonionContactLift.lean), [`lean/InfoGeometry/Exceptional/CircularContactV4.lean`](lean/InfoGeometry/Exceptional/CircularContactV4.lean)

### 3. $G_{2(2)}$ Bruhat Stratification & Flag Geometry
The complete 12-cell Bruhat stratification for $G_{2(2)}(\mathbb{F}_2)$, unipotent Borel flag stabilizer $U_6 \le B$ ($|B| = 64$), maximal parabolic subgroup $P$ ($|P| = 192$), the 189 cosets of the full flag variety, and group order $|G| = 12\,096$.
* **Modules**: [`lean/InfoGeometry/Algebra/Zorn/G2TwoBruhatClassification.lean`](lean/InfoGeometry/Algebra/Zorn/G2TwoBruhatClassification.lean), [`lean/InfoGeometry/Algebra/Zorn/G2FlagAndParabolicQuotient.lean`](lean/InfoGeometry/Algebra/Zorn/G2FlagAndParabolicQuotient.lean), [`lean/InfoGeometry/Algebra/Zorn/G2FlagOrbitPartitionCertificate.lean`](lean/InfoGeometry/Algebra/Zorn/G2FlagOrbitPartitionCertificate.lean)

### 4. The Matter-to-Gauge Bridge & Exceptional TKK Lie Tower
Surjective construction of the 14D exceptional Lie algebra $\mathfrak{g}_{2(2)}$ from the exterior square $\Lambda^2(\mathbb{O}_s)$, ascending through the Albert algebra $H_3(\mathbb{O}_s)$ into $E_{6(6)}$, $E_{7(7)}$, and the 5-graded Tits-Kantor-Koecher $E_{8(8)}$ Lie algebra with full bracket bilinearity.
* **Modules**: [`lean/InfoGeometry/Exceptional/FreudenthalFiveGradedBracketBilinear.lean`](lean/InfoGeometry/Exceptional/FreudenthalFiveGradedBracketBilinear.lean), [`lean/InfoGeometry/Exceptional/FreudenthalHeisenbergSuperchargeReadback.lean`](lean/InfoGeometry/Exceptional/FreudenthalHeisenbergSuperchargeReadback.lean), [`lean/InfoGeometry/Exceptional/CircularSplitOctonionFreudenthalLinearExtension.lean`](lean/InfoGeometry/Exceptional/CircularSplitOctonionFreudenthalLinearExtension.lean)

### 5. Dually Flat Amari Geometry & The Metriplectic Thermodynamic Engine
Unification of reversible Poisson Hamiltonian flows with irreversible Onsager/Amari gradient dissipation ($dF/dt = \{F, H\} + (F, S)_M$), deriving the First and Second Laws of Thermodynamics natively from Legendre duality $\Psi(x) + S(\eta(x)) = \langle x, \eta(x) \rangle$ and non-negative Bregman divergence.
* **Modules**: [`lean/InfoGeometry/Dynamics/DuallyFlatOperatorFamily.lean`](lean/InfoGeometry/Dynamics/DuallyFlatOperatorFamily.lean), [`lean/InfoGeometry/Canonical/MetriplecticCore.lean`](lean/InfoGeometry/Canonical/MetriplecticCore.lean), [`lean/InfoGeometry/Geometry/MetriplecticKahlerInterfaces.lean`](lean/InfoGeometry/Geometry/MetriplecticKahlerInterfaces.lean)

### 6. Emergent Spacetime, Conformal Twistors & Morita Dyadic Closure
The full Morita dyadic reconstruction of $\operatorname{Cl}(5,5) \cong \operatorname{Mat}_{32}(\mathbb{R})$ from spinor dyads $|e_i\rangle\langle e_j|$, chiral splitting into $16_+ \oplus 16_-$ Majorana-Weyl twistors, Krein fundamental symmetry $\eta^2 = 1$, emergent event coordinates $X^\mu = \operatorname{Tr}(\bar{\Psi} \Gamma^\mu \Psi)$, and symmetric fluctuation metric $g_{\mu\nu} = \frac{1}{2}\langle \{\Gamma_\mu, \Gamma_\nu\} \rangle$.
* **Modules**: [`lean/InfoGeometry/Clifford/Cl55DyadicMoritaBridge.lean`](lean/InfoGeometry/Clifford/Cl55DyadicMoritaBridge.lean), [`lean/InfoGeometry/Clifford/Cl55MoritaDyadicClosure.lean`](lean/InfoGeometry/Clifford/Cl55MoritaDyadicClosure.lean), [`lean/InfoGeometry/Clifford/Cl55ChiralSectorFinrankLedger.lean`](lean/InfoGeometry/Clifford/Cl55ChiralSectorFinrankLedger.lean), [`lean/InfoGeometry/Clifford/EmergentSpacetimeBilinear.lean`](lean/InfoGeometry/Clifford/EmergentSpacetimeBilinear.lean), [`lean/InfoGeometry/Physics/EmergentSpacetimeBilinear.lean`](lean/InfoGeometry/Physics/EmergentSpacetimeBilinear.lean)

---

## 🤖 Interrogating the Repository with AI

This repository is designed to be **LLM-native** and **agent-navigable**.

1. **Clone the repository:**
   ```bash
   git clone https://github.com/nklgtv/info-geometry-lean.git
   cd info-geometry-lean
   ```
2. **Connect an agent or LLM:**
   Use a large-context model (e.g. Claude 3.7 Sonnet, Gemini 1.5 Pro, GPT-4o, or local agents like Antigravity, Cursor, Windsurf, Aider).
3. **Suggested prompts to interrogate the codebase:**
   * *"Explain the proof of `dyadic_span_top` in `Cl55DyadicMoritaBridge.lean` and how it recovers `Cl(5,5)`."*
   * *"Trace how the 5-graded Freudenthal bracket bilinearity is established in `FreudenthalFiveGradedBracketBilinear.lean`."*
   * *"Show how the $V_4$ spectral projectors $P_{++}, P_{+-}, P_{-+}, P_{--}$ are constructed in `V4ContactBigrading.lean`."*
   * *"Explain how the Bregman divergence vanishes at equilibrium in `DuallyFlatOperatorFamily.lean`."*
   * *"How does the Krein adjoint preserve the Lie bracket in `EmergentSpacetimeBilinear.lean`?"*

---

## 📜 The Epistemic Baseline (The Prime Directive)

All modules strictly adhere to the repository's epistemic and formalization discipline:
* **Zero Axiomatic Debt:** No `sorry`, no `admit`, no external proxy axioms.
* **Kernel Truth:** Only kernel-checked Lean 4 proofs are recognized as mathematical truth.
* **Untrusted Discovery $\to$ Trusted Verification:** External CAS computations (GAP, Sage, Python) act exclusively as witness generators; all proofs are reconstructed natively in Lean 4.
* **Colimit Continuum Law:** The infinite topological boundary is constructed via categorical direct inductive colimits rather than classical real-analytic approximations.

---

## 🛠️ Build Instructions

Ensure you have [elan](https://github.com/leanprover/elan) and Lean 4 installed.

```bash
# Build and check all modules with Lean 4 / Mathlib
lake build InfoGeometry.All
```

---

*Enjoy the Easter eggs hidden along the causal corridors of the code.*
