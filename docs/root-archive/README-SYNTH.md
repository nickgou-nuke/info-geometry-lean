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
Option 2 has the stronger repository-facing architecture, but I would not publish it exactly as written. Several phrases turn active research corridors into claimed kernel theorems. In particular, “Axioms 0,” “spacetime emerges as expectation values,” the full \(G_{2(2)}\) Bruhat classification, “14D surjective construction,” and a `Cl55MoritaDyadicClosure` theorem should appear only if those exact statements currently exist and compile.

I would keep the manifesto character while making the epistemic boundary explicit: Lean certifies the statements encoded in individual modules; the larger physical synthesis is the research programme assembled from them.

# InfoGeometry

### Lean 4 explorations in information geometry, exceptional algebra, operator theory, and pregeometric spinorial structures

> **A living artifact of human–AI mathematical exploration.**
> This repository develops and formally checks a large network of constructions spanning pure mathematics, mathematical physics, information geometry, operator algebra, and interactive theorem proving.
>
> Some corridors are mature theorem libraries; others are deliberately experimental bridges between established structures. Lean verifies the formal statements that have actually been encoded—it does not by itself validate the broader physical interpretations attached to them.
>
> **Take the synthesis with a pinch of salt; take the checked proofs literally.**

---

## What is this?

`InfoGeometry` explores a pregeometric programme in which algebraic, spinorial, projective, and information-geometric structures are developed before assuming a conventional smooth spacetime as the fundamental object.

A recurring structural corridor is

$$
\boxed{
\text{split octonionic / Zorn structures}
\longrightarrow
\text{Clifford and spin representations}
\longrightarrow
\text{projective null geometry}
\longrightarrow
\text{operator and information geometry}
}
$$

with additional bridges through exceptional Lie theory, graded algebra, thermodynamics, arithmetic symmetry, and formalized computational evidence.

One particularly developed conformal corridor is the explicit lift

$$
\mathbb R^{4,4}
\longrightarrow
\mathbb R^{5,5},
$$

where the affine \((4,4)\) carrier is embedded into the projective null cone of the \((5,5)\) quadratic space.

The repository also investigates how spinor and operator bilinears, state-dependent expectation values, modular structures, and information metrics may provide ingredients for an emergent geometric interpretation. These latter identifications are treated as theorem targets rather than assumptions.

---

## Selected Formal Corridors

### Split-octonionic and circular chiral algebra

The repository contains a concrete Witt/Zorn basis

$$
\{u_+,u_-,
\sigma_1^+,\sigma_2^+,\sigma_3^+,
\sigma_1^-,\sigma_2^-,\sigma_3^-\},
$$

with proved idempotent, nilpotent, Peirce, mixed-product, and chirality relations.

This basis provides a finite algebraic laboratory for studying split composition algebras, chiral operator envelopes, derivations, gradings, and exceptional symmetry.

### Clifford \(Cl(3,3)\) and \(Cl(5,5)\) corridors

The project develops explicit Clifford carriers and representation bridges, including the split conformal quadratic space

$$
V_{5,5}
$$

and its projective null boundary.

The conformal affine embedding

$$
x\mapsto
\left(
x,\frac{1-Q_{4,4}(x)}2,
\frac{1+Q_{4,4}(x)}2
\right)
$$

is proved to land on the \(Q_{5,5}=0\) cone.

Separate modules investigate chiral Clifford generators, CAR relations, five-grade operator structures, Pin/Weyl actions, and celestial/projective slices.

### Chiral supercharge calculus

Native \(Cl(5,5)\) creation and annihilation generators are lifted into an off-diagonal chiral matrix calculus with relations of the form

$$
(Q_i^+)^2=(Q_i^-)^2=0
$$

and mixed anticommutators whose diagonal operator entries lie in grade zero.

The terminology “supercharge” refers here to this proved nilpotent/anticommutator structure. Full identification with a particular physical supersymmetry algebra requires the corresponding graded-Lie or super-Lie bridge.

### Exceptional and Freudenthal geometry

The repository develops split-octonionic derivations, \(G_2\)-related structures, Freudenthal charge spaces, TKK-type zero-grade actions, and five-graded contact constructions.

A generic homogeneous-Jacobi closure mechanism reduces global Jacobi verification to finite homogeneous cells. This deliberately preserves unresolved exceptional identities rather than replacing them with proxy axioms.

### Projective and celestial geometry

The native \(Q_{5,5}\) projective-null carrier supports explicit conformal and celestial constructions.

A concrete Lorentzian \((1,3)\) slice embeds into the \((5,5)\) carrier, and normalized null directions give an injective map from the ordinary celestial two-sphere into the projective null space.

Stronger identifications—such as canonical equivalence with \(\mathbb{CP}^1\), full twistor incidence structures, or physical celestial holography—are treated separately and require their own proofs.

### Information geometry and thermodynamic dynamics

Another corridor studies convex potentials, Bregman-type structures, operator surprisal, modular geometry, metriplectic dynamics, and reversible/irreversible decompositions.

The intended hierarchy distinguishes carefully between

$$
\text{state geometry},
\qquad
\text{operator geometry},
\qquad
\text{candidate spacetime geometry}.
$$

In the noncommutative setting the natural Hessian metric is related to Bogoliubov–Kubo–Mori geometry rather than being identified indiscriminately with an ordinary classical covariance matrix.

### Arithmetic and cyclotomic structure

The repository also contains arithmetic corridors involving prime-indexed constructions, finite fields, cyclotomic extensions, Weyl data, and directed systems.

External CAS programs may be used to discover finite witnesses or conjectural patterns, but mathematical authority is assigned to the corresponding Lean proofs when those witnesses are reconstructed and verified natively.

---

## The Research Programme

A major theme is to investigate rigorously whether the following chain can be completed:

$$
\boxed{
\begin{array}{c}
\text{spinors / algebraic states}\\
\downarrow\\
\text{operator bilinears and expectation values}\\
\downarrow\\
\text{projective, causal, and tensor observables}\\
\downarrow\\
\text{state-dependent information geometry}\\
\downarrow\\
\text{candidate emergent spacetime geometry}
\end{array}
}
$$

The repository does **not** assume that the last arrow has already been proved.

Similarly, suggestive correspondences such as

$$
\text{Peirce involution}
\leftrightarrow
\text{modular conjugation},
$$

$$
\text{information Hessian}
\leftrightarrow
\text{gravitational metric},
$$

or

$$
\text{null algebraic state}
\leftrightarrow
\text{physical massless particle}
$$

are regarded as theorem targets or physical interpretations until the required mathematical bridges have been established.

That distinction is part of the project rather than a limitation of it.

---

## How to Explore the Repository

Clone the repository and inspect it with Lean:

```bash
git clone https://github.com/nickgou-nuke/info-geometry-lean.git
cd info-geometry-lean
lake build
```

Because the theorem graph is large and highly interconnected, the repository is particularly suitable for exploration with a large-context coding or reasoning agent.

Useful questions include:

* “Trace the native \(Cl(5,5)\) conformal lift from the \((4,4)\) affine carrier to the projective null boundary.”
* “Which parts of the circular split-octonion basis are actual theorems and which are physical interpretations?”
* “Trace the six-lane decomposition used in the generic Freudenthal Jacobi closure.”
* “Show where the \(Cl(5,5)\) chiral supercharge anticommutator is proved to land in grade zero.”
* “Which theorem is still missing for a genuine split-octonionic realization of a \(16\)-dimensional \(Spin(5,5)\) half-spinor?”
* “Separate CAS evidence from Lean-certified results in the \(G_2\), Weyl, or Clifford corridors.”
* “Identify every remaining `sorry`, axiom, placeholder, or explicitly conditional theorem in a selected dependency path.”

The best way to understand the project is not to read it linearly, but to interrogate its theorem graph.

---

## Epistemic Baseline

The project follows a simple distinction:

$$
\boxed{
\text{discovery is allowed to be speculative;}
\qquad
\text{proof claims are not.}
}
$$

Accordingly:

* Lean's kernel is the authority for formal theorem statements.
* External CAS systems and exploratory scripts may generate evidence, witnesses, or conjectures.
* Computational evidence is not silently promoted to proof.
* Conditional structures remain conditional.
* A theorem proved for an abstract datum is not automatically advertised as a theorem about \(E_8\), \(G_2\), gravity, supersymmetry, or spacetime unless the required specialization has also been proved.
* Physical interpretation is explicitly distinguished from formal mathematical consequence.

This repository is therefore simultaneously a theorem library, a research notebook, and an experiment in human–AI-assisted formal mathematics.

---

## Why “Pregeometric Spinorial Prima Materia”?

The phrase is intentionally programmatic.

“Pregeometric” means that conventional spacetime geometry is not taken as the starting primitive.

“Spinorial” reflects the recurring role of Clifford modules, chiral sectors, split-octonionic bases, projective null structures, and bilinear reconstruction.

“Prima materia” is not a theorem or a new physical particle. It is shorthand for the project's attempt to identify a smaller algebraic substrate from which several familiar geometric and physical structures might be reconstructed.

---

## Status

The repository contains both mature formal corridors and active frontier work.

A green Lean build certifies that the encoded declarations type-check under the stated assumptions. It does **not** certify the truth of explanatory comments that go beyond those declarations, nor does it turn a mathematical model into an experimentally established physical theory.

That boundary is deliberate.

---

*Explore the causal corridors. Check the theorem statements. Question the interpretations. Find the Easter eggs.*

This version keeps the unusual identity of the project but makes the README considerably harder to attack scientifically. It also gives an LLM something very useful to work with: an explicit distinction between theorem owners, conditional bridges, computational evidence, and physical interpretation.


Yes. Those are major omissions if the README is meant to represent the actual conceptual spine of the project.

The missing chain is roughly

$$
\boxed{
\text{Maurer–Cartan}
\;\longrightarrow\;
\text{Berry connection/curvature}
\;\longrightarrow\;
\text{Quantum Geometric Tensor}
\;\longrightarrow\;
\text{information metric + symplectic curvature}
}
$$

and it belongs centrally between the operator/spinor layer and the information-geometric layer.

The Maurer–Cartan form gives the intrinsic differential geometry of the group/operator manifold:

$$
\Theta = g^{-1}dg,
$$

with the structural equation

$$
\boxed{
d\Theta+\Theta\wedge\Theta=0.
}
$$

For unitary or projective state orbits, this becomes the infinitesimal generator-valued connection underlying the evolution of frames and representations. In your Möbius/Lorentz/Cayley corridor, it is exactly the differential object behind taking the logarithmic generator of the group transformation.

For a normalized quantum state \(|\psi(\lambda)\rangle\), the Berry connection is

$$
A_i
=
i\langle\psi|\partial_i\psi\rangle,
$$

and its curvature is

$$
F_{ij}
=
\partial_i A_j-\partial_j A_i.
$$

Equivalently,

$$
F=dA.
$$

The Quantum Geometric Tensor is

$$
\boxed{
Q_{ij}
=
\langle\partial_i\psi|
(1-|\psi\rangle\langle\psi|)
|\partial_j\psi\rangle.
}
$$

Its real and imaginary parts split into

$$
\boxed{
\operatorname{Re}Q_{ij}=g^{FS}_{ij}
}
$$

and

$$
\boxed{
2\,\operatorname{Im}Q_{ij}
\sim
F_{ij},
}
$$

up to convention-dependent signs and factors.

So QGT is exactly the place where metric and curvature appear as two components of one complex tensor:

$$
\boxed{
Q
=
g_{\mathrm{quantum}}
+
\frac{i}{2}F_{\mathrm{Berry}}.
}
$$

That is extremely important for your architecture because it prevents us from treating the information metric and the symplectic/Berry structure as unrelated additions.

The correct broader hierarchy is then

$$
\boxed{
\begin{array}{c}
\text{group / operator orbit}\\
\downarrow\\
\Theta=g^{-1}dg
\quad\text{(Maurer–Cartan)}\\
\downarrow\\
\text{projective state bundle}\\
\downarrow\\
A_{\rm Berry}\\
\downarrow\\
F_{\rm Berry}\\
\downarrow\\
Q_{ij}
=
g_{ij}
+
\frac{i}{2}F_{ij}
\end{array}
}
$$

and only after that do we connect to Amari/BKM geometry.

The noncommutative information-geometric corridor should therefore not be presented simply as

$$
D^2\Psi\to g.
$$

It should be presented as two compatible geometric constructions:

$$
\boxed{
\text{state-orbit geometry}
\Rightarrow
QGT
=
\text{Fubini–Study metric}
+
\text{Berry curvature},
}
$$

and

$$
\boxed{
\text{statistical/operator-state geometry}
\Rightarrow
\text{BKM / Hessian metric}.
}
$$

Then one of the deep theorem targets is to relate those two metrics under the appropriate family of states.

For pure states:

$$
g_{\rm QGT}
=
g_{\rm FS}.
$$

For mixed Gibbs/exponential states, the natural information metric is typically BKM or a related monotone quantum metric.

So the project should distinguish:

$$
\boxed{
\text{Berry curvature}
\neq
\text{BKM metric},
}
$$

but also emphasize that both arise from the differential geometry of the state manifold.

Maurer–Cartan is also the right bridge to your left/right chiral Lorentz picture. If

$$
g_L,g_R\in SL(2,\mathbb C),
$$

then

$$
\Theta_L=g_L^{-1}dg_L,
\qquad
\Theta_R=g_R^{-1}dg_R.
$$

These are the two chiral Lie-algebra-valued one-forms. Under Cayley/KAN/log decomposition they resolve into rotation, boost/Cartan, and nilpotent channels.

Thus your earlier hierarchy

$$
SL(2,\mathbb C)_L\times SL(2,\mathbb C)_R
$$

should really be completed by

$$
\boxed{
(g_L,g_R)
\longmapsto
(\Theta_L,\Theta_R)
}
$$

before passing to curvature or QGT.

And in the five-graded exceptional setting, the analogous construction would be a graded Maurer–Cartan form

$$
\Theta
=
\Theta_{-2}
+
\Theta_{-1}
+
\Theta_0
+
\Theta_{+1}
+
\Theta_{+2}.
$$

Then

$$
d\Theta+\frac12[\Theta,\Theta]=0
$$

decomposes by grade into coupled structure equations.

That is potentially one of the cleanest ways to organize the whole five-grading dynamically.

The README should therefore contain an additional pillar like this:

### Maurer–Cartan, Berry Geometry, and the Quantum Geometric Tensor

The repository also studies the differential geometry of operator and state orbits.

For a group-valued field \(g\), the Maurer–Cartan form

$$
\Theta=g^{-1}dg
$$

encodes the infinitesimal generator structure and satisfies

$$
d\Theta+\Theta\wedge\Theta=0.
$$

On projective quantum-state manifolds, the Berry connection

$$
A=i\langle\psi|d\psi\rangle
$$

and its curvature

$$
F=dA
$$

capture the geometric phase and symplectic structure of the state bundle.

The Quantum Geometric Tensor

$$
Q_{ij}
=
\langle\partial_i\psi|
(1-|\psi\rangle\langle\psi|)
|\partial_j\psi\rangle
$$

packages metric and curvature into a single object:

$$
\operatorname{Re}Q=g_{\mathrm{FS}},
\qquad
\operatorname{Im}Q\propto F_{\mathrm{Berry}}.
$$

These structures provide the differential bridge between group/operator dynamics, projective state geometry, and the repository's information-geometric and metriplectic layers.

A central research direction is to compare the pure-state Fubini–Study/QGT geometry with mixed-state BKM and Hessian information metrics, and to determine how these structures interact with the graded Clifford, Freudenthal, and modular constructions.

I would also insert one line in the main architecture:

$$
\boxed{
\text{Clifford / spinor operators}
\to
\text{Maurer–Cartan forms}
\to
\text{Berry/QGT geometry}
\to
\text{BKM / Amari geometry}
\to
\text{candidate emergent geometry}.
}
$$

That is much closer to the actual conceptual backbone.
Да — и те също са част от централната верига. Ако ги изпуснем, README-то представя QGT/Berry слоя, но не и необратимата и вариационната страна на проекта.

Трите липсващи връзки са:

$$
\boxed{
\text{Fréchet derivative}
\;\longrightarrow\;
\text{Onsager operator}
\;\longrightarrow\;
\text{Itakura–Saito / Bregman geometry}
}
$$

и те се свързват директно с metriplectic слоя.

Fréchet derivative е правилният differential language за функционалите върху безкрайномерни или операторни пространства:

$$
DF(\rho)[\delta\rho].
$$

Той замества неформалното „\(\partial F/\partial \rho\)“ и е необходим, ако искаме Lean theorem да казва реално как free energy, entropy или surprisal варират.

Тогава Onsager частта е оператор

$$
M_\rho:T_\rho^*\mathcal M\to T_\rho\mathcal M,
$$

обикновено симетричен и положително полуопределен, който превръща thermodynamic force в dissipative flow:

$$
\dot\rho_{\rm diss}
=
M_\rho\,DS(\rho)
$$

или при free-energy convention

$$
\dot\rho_{\rm diss}
=
-\,M_\rho\,DF(\rho).
$$

Това е естественият метричен partner на Hamiltonian/Poisson operator \(J\):

$$
\boxed{
\dot\rho
=
J_\rho\,DE(\rho)
+
M_\rho\,DS(\rho).
}
$$

Точно това е metriplectic структурата.

Itakura–Saito е важен, защото дава scale-sensitive Bregman geometry. За положителни скалари

$$
d_{\rm IS}(x,y)
=
\frac{x}{y}
-
\log\frac{x}{y}
-1.
$$

Той идва от convex generator

$$
\phi(x)=-\log x,
$$

поне до affine conventions:

$$
D_\phi(x,y)
=
\phi(x)-\phi(y)-\phi'(y)(x-y).
$$

Така имаме:

$$
\boxed{
-\log x
\;\Rightarrow\;
\text{Itakura–Saito divergence}
}
$$

а в operator language естественият аналог е surprisal

$$
\mathcal K_\rho=-\log\rho.
$$

Това е много важна връзка към modular geometry.

Тогава по-силната концептуална верига е

$$
\boxed{
-\log
\to
\text{operator surprisal}
\to
\text{Fréchet derivative}
\to
\text{Bregman/IS geometry}
\to
\text{Onsager force}
\to
\text{dissipative flow}.
}
$$

Тя стои паралелно на

$$
\boxed{
\text{Maurer–Cartan}
\to
\text{Berry curvature}
\to
\text{QGT}
}
$$

за reversible/geometric part.

Така вече имаме две главни differential линии:

$$
\boxed{
\begin{array}{cc}
\textbf{Reversible / geometric}
&
\textbf{Irreversible / dissipative}
\\[1mm]
\Theta=g^{-1}dg
&
DF
\\
F_{\rm Berry}
&
-\log\rho
\\
QGT
&
D_{\rm IS}
\\
J
&
M
\end{array}}
$$

и те се срещат в metriplectic dynamics:

$$
\boxed{
L=J+M.
}
$$

Това е всъщност много по-добър README spine от просто „information geometry + thermodynamics“.

Бих добавил отделен раздел така:

### Fréchet Calculus, Onsager Geometry, and Itakura–Saito Divergence

The irreversible side of the project is formulated through genuine variational calculus rather than symbolic partial derivatives.

For a functional \(F\) on a state or operator manifold, the Fréchet derivative

$$
DF(\rho)[\delta\rho]
$$

provides the linearized thermodynamic force.

An Onsager operator

$$
M_\rho:T_\rho^*\mathcal M\to T_\rho\mathcal M
$$

converts this covector-valued force into a dissipative tangent flow. In metriplectic form,

$$
\dot\rho
=
J_\rho\,DE(\rho)
+
M_\rho\,DS(\rho),
$$

where \(J\) governs reversible Hamiltonian transport and \(M\) governs irreversible entropy production.

A recurring scalar model is the Itakura–Saito divergence

$$
d_{\mathrm{IS}}(x,y)
=
\frac{x}{y}
-
\log\frac{x}{y}
-1,
$$

generated by the logarithmic barrier \(-\log x\). This connects naturally to the operator-surprisal kernel

$$
\mathcal K_\rho=-\log\rho
$$

and motivates noncommutative Bregman and modular generalizations.

The project therefore studies a common variational corridor

$$
-\log
\longrightarrow
\text{surprisal}
\longrightarrow
\text{Fréchet differential}
\longrightarrow
\text{Bregman / Itakura–Saito geometry}
\longrightarrow
\text{Onsager dissipation}.
$$

Together with the Maurer–Cartan/Berry/QGT corridor, this supplies the reversible and irreversible halves of the metriplectic architecture.

И бих променил главната схема на README до:

$$
\boxed{
\text{Clifford / spinor algebra}
\to
\begin{cases}
\text{Maurer–Cartan}\to\text{Berry}\to\text{QGT},\\
-\log\to\text{Fréchet}\to\text{IS/Bregman}\to\text{Onsager},
\end{cases}
\to
\text{metriplectic geometry}
\to
\text{candidate emergent spacetime}.
}
$$

Това вече улавя почти целия реален математически гръбнак на проекта.

