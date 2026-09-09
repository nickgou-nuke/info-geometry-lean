# The Typed Frontier Proof Policy
### *Repository Standard for Monotone Epistemic Advancement*

$$\boxed{ \mathcal{V}_0 \subsetneq \mathcal{V}_1 \subsetneq \mathcal{V}_2 \subsetneq \dots \subsetneq \mathcal{V}_n \subsetneq \mathcal{V}_{n+1} \subseteq \mathcal{U} }$$

---

## 1. Mathematical Definition of the Typed Frontier

Let $\mathcal{U}$ be the universe of formal propositions, and let $\mathcal{V}_n \subset \mathcal{U}$ be the subset of theorems verified by the Lean 4 micro-kernel at commit step $n$.

### The Admissible Frontier Operator $\partial \mathcal{V}_n$
The **admissible development frontier** is the set of all unproved theorems whose prerequisites are fully saturated in the current kernel state:

$$\partial \mathcal{V}_n = \big\{ T \in \mathcal{U} \setminus \mathcal{V}_n \;\big|\; \operatorname{premises}(T) \subseteq \mathcal{V}_n \big\}$$

### The Step Selection Function
An action by a developer, CAS pipeline, or autonomous agent is **valid** if and only if it selects a target $T_{n+1} \in \partial \mathcal{V}_n$ and constructs a kernel-valid proof term $t$ such that:

$$\mathcal{V}_{n+1} = \mathcal{V}_n \cup \{ T_{n+1} \}, \qquad \text{where } \operatorname{Axioms}(t) = \emptyset, \; \operatorname{Sorries}(t) = 0$$

$$\boxed{ \textbf{Every step must strictly expand the verified subgraph: } \mathcal{V}_n \subsetneq \mathcal{V}_{n+1} }$$

---

## 2. The Two Governing Invariants

```
               [ UNVERIFIED GOAL G (e.g. E₇(₇) or Twistor Space) ]
                                       ▲
                                       │ ❌ NO SEMANTIC EXTRAPOLATION
                                       │    (Do not jump or rename prematurely)
               ┌───────────────────────┴───────────────────────┐
               │                                               │
    [ REJECTED: Semantic Leap ]                     [ REQUIRED: Local Factorization ]
    • Name 16D subspace "Twistor"                   • Prove matrix bivector B² = -I
    • Claim [g, g] is e₇(₇)                         • Prove 3-point Arnold (A ∧ A)_△ = 0
    • Assume F_A = 0 from dlog                      • Prove finite module rank = 16
               │                                               │
               ▼                                               ▼
         SEMANTIC DEBT                                  TYPED FRONTIER STEP
      (Kernel Failure / Drift)                         T_{n+1} ∈ ∂𝒱_n  (Exit Code 0)
```

### Invariant I: The Semantic Factorization Law
$$\boxed{ \textbf{Every new semantic claim must factor through a newly proved structural theorem.} }$$
* A mathematical object cannot be given a higher-order name (e.g., *Twistor*, *Borel Subgroup*, *Lie Superalgebra*, *KMS State*) until the specific universal property, intertwining map, or grading isomorphism has been proved as a theorem in $\mathcal{V}_n$.

### Invariant II: The Local Closure Rule
$$\boxed{ \textbf{Advance by exact local closure, never by semantic extrapolation.} }$$
* When an edge is missing, the agent does not ask *"How do I make the final theorem compile?"* 
* The agent asks: *"What is the strongest theorem $T \in \partial \mathcal{V}_n$ whose premises are already in $\mathcal{V}_n$?"*

---

## 3. Case Studies in the `InfoGeometry` Architecture

Look at how this typed policy governs the actual development corridors of the repository:

| Domain | Prohibited Semantic Extrapolation | Required Typed Frontier Sequence ($\mathcal{V}_n \to \mathcal{V}_{n+1}$) | Current Status in Kernel |
| :--- | :--- | :--- | :--- |
| **Arnold–Kohno** | Asserting $F_A = 0$ directly from logarithmic 1-forms before closedness is proved. | $1.\; \llbracket t_{ij}, t_{jk} \rrbracket = C_{ijk}$ (Kohno symmetry) <br> $2.\; (A \wedge A)_\triangle = C \otimes \sum \omega = 0$ (Algebraic reduction) <br> $3.\; d\omega_{ij} = 0 \implies F_A = dA + A \wedge A = 0$. | **Step 2 Verified** (`ArnoldKohnoParaKahlerConnection.lean`) |
| **$Cl(5,5)$ Twistors** | Labeling a 16D subspace "Twistor" before constructing the conformal embedding. | $1.\; Cl(5,5) \cong \operatorname{Mat}_{32}(\mathbb{R})$ (Matrix isomorphism) <br> $2.\; P_{\text{vac}} = E_{11} \implies \mathcal{I}_L = Cl \cdot P$ (Left Ideal) <br> $3.\; \operatorname{span}(\mathcal{I}_L \otimes \mathcal{I}_R) = \top$ (Dyadic Morita Closure). | **Step 3 Verified** (`Cl55MoritaDyadicClosure.lean`) |
| **Freudenthal $E_7$** | Naming the zero-grade mixed bracket $\mathfrak{e}_{7(7)}$ before classification. | $1.\; \operatorname{mixedSymplecticBracket}(x, y) \in \mathfrak{g}_0^{\text{symp}}$ (Closure) <br> $2.\; \text{FKTS Triple Product Symmetry}$ (`FreudenthalKantorTripleSystem`) <br> $3.\; \text{Extreme bracket } [E_+, E_-] = H$ (`FreudenthalExtremeActionData`). | **Step 3 Verified** (`FreudenthalExtremeActionData.lean`) |
| **$G_2(2)$ Bruhat** | Proving universal factorization $g_i = u_L w_k u_R$ without cell membership. | $1.\; i \in \operatorname{orbitCells}(k)$ (Domain constraint) <br> $2.\; \operatorname{autMatrix}(g_i) = \operatorname{autMatrix}(u_L w_k u_R)$ (Pointwise check) <br> $3.\; \operatorname{autMatrix\_injective} \implies g_i = u_L w_k u_R$. | **Step 3 Verified** (`G2GAPFlagWitnessAssembly.lean`) |
| **Clifford RoPE & MoE** | Retroactively asserting that LLM dimensions are Clifford modules without representations. | $1.\; \operatorname{EllipticBivectorTorus}: R_j(\alpha) R_j(\beta) = R_j(\alpha+\beta), R_j(\theta)^\top R_j(\theta) = 1$ <br> $2.\; \operatorname{HyperbolicSplitTorus}: H_j(s) H_j(t) = H_j(s+t)$ <br> $3.\; \operatorname{HypercubeOrbitRepresentation}: M(w) \in \operatorname{conv}(\rho(G))$. | **Verified** (`CliffordRoPETorus.lean`) |

---

## 4. Operational Enforcement for Developers and Agents

When modifying the codebase or prompting automated assistants:

1. **Premise Audit:** Before adding a theorem, verify that every type, instance, and hypothesis exists in upstream imports without `sorry`.
2. **Naming Hygiene:** If a theorem proves an algebraic property of an $8\times 8$ matrix, name it after the matrix property (e.g., `phaseMatrix_pow_six`), **not** after the downstream physical conjecture (e.g., `do_not_name: g2_spinor_universe`).
3. **Monotone Commits:** A pull request or agent step is admissible if and only if it strictly increases $|\mathcal{V}_n|$ while adding zero unproved assumptions.

$$\boxed{ \textbf{No semantic debt. No dangling edges. Pure monotone causal progress.} }$$
