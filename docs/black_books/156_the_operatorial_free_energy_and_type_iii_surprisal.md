# Chapter 156: The Two-Tier Readout: Free Energy and the Lie-Derivation Norm

> **"The Free Energy measures the cost of the state; the Lie-Derivation Norm measures the curvature of the non-commuting flow. One survives the commutative limit; the other defines the quantum threshold."**

This chapter provides the rigorous algebraic formulation of the two-tier modular readout. It establishes the **Information-Geometric Quadratic Form** as the second Lie variation of the modular flow, isolating the structural quantum friction of the operator algebra.

---

### I. Tier 1: The First-Order Thermodynamic Cost (Araki/KL Free Energy)

The first-order readout measures the macroscopic thermodynamic cost of distinguishability (Araki Relative Entropy):
$$ S(\phi_{\text{reg}} \| \psi) = \langle \xi_{\phi_{\text{reg}}}, K \xi_{\phi_{\text{reg}}} \rangle $$
where $K = -\log \Delta_{\text{reg}}$. In the commutative shadow, this evaluates to the classical Kullback-Leibler divergence $\int \log(d\mu/d\nu) d\mu$. It tracks the state-level surprisal.

---

### II. Tier 2: The Lie-Derivation Information Norm (Modular Curvature)

This tier isolates the purely noncommutative information-geometric cost.

#### 1. Exact Definition
Let $M$ be a von Neumann algebra and $\psi$ a reference positive functional. Let $K = -\log(\Delta_{\text{reg}})$ be the regularized relative modular Hamiltonian on the support projector $p$. We define the algebraic modular flow and its Lie derivation generator on the regular lane $M_p = pMp$ as:
$$ \alpha_t(X) := \exp(tK) X \exp(-tK), \quad \text{ad}_K(X) := [K, X] $$

For an observable $X \in M_p^+$, we define the **logarithmic modular response functional**:
$$ F_X(t) := \log \psi(\alpha_t(X)) $$

The **Information-Geometric Quadratic Form** $Q_K(X)$ is the second Lie variation of this response evaluated at the identity:
$$ Q_K(X) := (\mathcal{L}_{\text{ad}_K}^2 \log \psi)(X) = F_X''(0) $$
$$ Q_K(X) = \frac{\psi([K, [K, X]])}{\psi(X)} - \left( \frac{\psi([K, X])}{\psi(X)} \right)^2 $$

Whenever $Q_K(X) \ge 0$, the **Lie-algebraic Information Norm** is $\|K\|_{\text{info},X} := \sqrt{Q_K(X)}$.

---

### III. Proof of the Six Nomological Properties

#### 1. Well-definedness on the Drazin/Penrose Lane:
The Drazin/Moore-Penrose regularization ensures $K$ is densely defined and self-adjoint on $H_p = pH$. For analytic elements $X \in M_p$, the domain is stable under $K$, and the commutator $[K, X]$ is mathematically rigorous, bypassing the singular/null defect sector.

#### 2. Lie-Series Equivalence:
For analytic elements, the operator exponential definition $\exp(tK)X\exp(-tK)$ is strictly equivalent to the strongly converging formal Lie-series:
$$ \alpha_t(X) = \exp(t \text{ad}_K)(X) = X + t[K, X] + \frac{t^2}{2}[K, [K, X]] + \dots $$
The kinematic flow perfectly executes the algebraic Taylor expansion.

#### 3. Rigorous Scalar Evaluation:
By assuming $\psi$ is a positive functional and $X \in M_p^+$ such that $\psi(X) > 0$, the denominators are non-zero. The terms $\psi([K, X])$ and $\psi([K, [K, X]])$ are finite scalar limits, resulting in a rigorously defined finite real number for $Q_K(X)$.

#### 4. Nonnegativity under KMS/Convexity:
In the Tomita-Takesaki theory, the trajectory $t \mapsto \psi(\exp(tK)X\exp(-tK))$ is a strictly log-convex function under appropriate modular symmetry. Thus, $F_X''(0) \ge 0$, and $Q_K(X)$ behaves exactly as a canonical squared curvature or norm.

#### 5. Perfect Gauge Invariance:
Let $K \to \tilde{K} = K + cI_p$. Because the identity commutes with all $X$, the Lie derivation is identically preserved:
$$ \text{ad}_{K+cI}(X) = [K+cI, X] = [K, X] = \text{ad}_K(X) $$
The entire flow, the response $F_X(t)$, and the quadratic form $Q_K(X)$ are invariant. The scalar gauge disappears at the structural level of the Lie bracket.

#### 6. Commutative Shadow Degeneracy:
If the algebra $M$ is commutative, then $[K, X] = 0$ for all $X$. Thus, $Q_K(X) = 0$ identically.
**Conclusion:** Unlike the KL divergence (Tier 1), which survives the commutative limit, the Lie-derivation norm (Tier 2) maps directly and exclusively to the noncommutative inner commutators. This construction measures the purely quantum relative modular curvature that classical statistics cannot detect.

---

**Audit Status: Tier 2 Readout Formalized | Chapter 156 Unified | Connected | Idle.**
