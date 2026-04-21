### 1. The Purified Nucleus: The Entropy-Production Kernel
In any informational dynamical system $(M, \Phi)$, the "Total State" is a composite of information that persists without cost and information whose transformation requires irreversible expenditure. 

**Memory** is the kernel of the entropy-production functional $\sigma$.  
**Dissipation** is the residual positive cone where $\sigma > 0$.

---

### 2. The Definition Stack
1.  **State Space:** A manifold $M$ representing the system's configuration.
2.  **Dynamics:** A vector field $X \in \Gamma(TM)$ generating the flow $\phi_t$.
3.  **Cost Functional:** A non-negative continuous map $\sigma: TM \to [0, \infty)$ (the Entropy Production Rate), which is typically a sub-quadratic or quadratic form on the fibers.
4.  **Memory Kernel ($\mathcal{K}$):** The set of tangent directions $v \in TM$ such that $\sigma(v) = 0$.
5.  **Dissipative Cone ($\mathcal{C}^+$):** The subset of tangent directions $v \in TM$ such that $\sigma(v) > 0$.

---

### 3. Graded Hypotheses (Weak to Strong)

*   **H1 (Weak Decomposition):** For any informational flow $X$, the tangent bundle admits a pointwise partition $TM = \mathcal{K} \cup \mathcal{C}^+$, where $\mathcal{K}$ is a closed sub-cone (often a subspace).
*   **H2 (Dynamic Invariance):** The flow $\phi_t$ preserves the memory kernel: if $v \in \mathcal{K}$, then $d\phi_t(v) \in \mathcal{K}$. This identifies "Memory" as the invariant logic of the system.
*   **H3 (Metric Splitting):** Given a Riemannian metric $g$ on $M$, there exists an orthogonal decomposition $TM = \mathcal{K} \oplus \mathcal{K}^\perp$ such that the dissipative cone $\mathcal{C}^+$ is contained within (or is exactly) the complement $\mathcal{K}^\perp \setminus \{0\}$.

---

### 4. Symbolic Archetype: The Kernel and the Furnace
The **Kernel** is the *Logos*: the structural invariants that survive the flow without being "burned."  
The **Furnace** is the *Materia*: the energetic cost of transition, the necessary friction that allows the system to move from one distinguishable state to another.

---

### 5. Demanded Mathematics: Non-Symmetric Geometry of Cones
This demands a **Thermodynamic Finsler Geometry**, where the "metric" is not a symmetric tensor but a non-negative functional $\sigma$ whose kernel defines the system's internal constraints (Memory) and whose positivity defines the arrow of time (Dissipation).

---

### 6. DISTILLED CONCEPT: The Logos-Pyre Decomposition
**An irreversible flow induces a canonical partition of the tangent bundle into a zero-production kernel (Logos/Memory) and a positive-production residual (Pyre/Dissipation). Persistence is the stationarity of the Logos; evolution is the consumption of the Pyre.**

---

### 7. Lean 4 Hypothesis Surface (Formalized)

```lean
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# The Logos-Pyre Decomposition (Kernel-Cone Hypothesis)
Standard: PAULI-AUDITOR-LOGIC-L1
-/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝⁿ M]

/-- 
An entropy production functional is a non-negative map from the tangent bundle 
to the reals, vanishing on the "Memory" directions.
-/
structure EntropyProduction (M : Type*) [TopologicalSpace M] [ChartedSpace ℝⁿ M] where
  sigma : TotalSpace (TangentBundle ℝⁿ M) → ℝ
  non_neg : ∀ v, 0 ≤ sigma v

/-- 
The Memory Kernel: The subspace of tangent directions with zero entropy production.
-/
def memory_kernel (σ : EntropyProduction M) (p : M) : Set (TangentSpace ℝⁿ p) :=
  {v | σ.sigma ⟨p, v⟩ = 0}

/-- 
The Dissipative Cone: The set of tangent directions with positive entropy production.
-/
def dissipative_cone (σ : EntropyProduction M) (p : M) : Set (TangentSpace ℝⁿ p) :=
  {v | σ.sigma ⟨p, v⟩ > 0}

/-- 
Hypothesis: Logos-Pyre Decomposition.
In a valid informational system, the Memory Kernel is a linear subspace 
that is invariant under the flow.
-/
axiom logos_pyre_decomposition
  (σ : EntropyProduction M)
  (X : VectorField ℝⁿ M) :
  /- 1. Kernel is a subspace (Logos) -/
  (∀ p, IsSubmodule (memory_kernel σ p)) ∧ 
  /- 2. Flow Invariance (Persistence of Memory) -/
  (∀ p (v : TangentSpace ℝⁿ p), v ∈ memory_kernel σ p → 
    ∀ t, (Flow X t v) ∈ memory_kernel σ (Flow X t p))
```
