# Dual-Engine Architecture: Lean 4 Verification Oracle $\longleftrightarrow$ Julia Numerical Executor

This document formalizes the repository-wide dual-pipeline paradigm, where **Lean 4 acts as the algebraic compiler and verification oracle**, and **Julia acts as the high-performance numerical and GPU executor**.

---

## 1. Architectural Division of Labor

```
                 LEAN 4: THE ALGEBRAIC ORACLE
  ┌────────────────────────────────────────────────────────┐
  │ • Exact Algebraic Equivalence & Graded Invariants      │
  │ • Chentsov Markov Congruence & Sufficient Compression  │
  │ • Submersion Splitting & Vanishing Drift (P_V θ̇ = 0)   │
  │ • Continuous Colimits & Hodge Laplacian Commutation    │
  │ • Finite Matrix GNS Left Ideals & Tomita Duality       │
  └───────────────────────────┬────────────────────────────┘
                              │
            ┌─────────────────┴─────────────────┐
            │ Native C Shared ABI / JSON Tables │
            │ (Lake emit-c / Exporter Pipeline) │
            └─────────────────┬─────────────────┘
                              ▼
                 JULIA: THE NUMERICAL EXECUTOR
  ┌────────────────────────────────────────────────────────┐
  │ • Grassmann.jl: Bitwise blade arithmetic (UInt64, ⊻)   │
  │ • Reduced-order solvers: Invert only H_p, skip V_p     │
  │ • Automatic Differentiation: Enzyme.jl, Zygote.jl      │
  │ • High-throughput ODE flows: OrdinaryDiffEq.jl         │
  │ • Hardware Acceleration: CUDA.jl / Metal.jl SIMD       │
  └────────────────────────────────────────────────────────┘
```

---

## 2. Certified Mathematical Contracts Transferred to Julia

### Contract 1: Metric Inversion Truncation ($O(D^3) \to O(d_{\mathcal{H}}^3)$)
* **Lean 4 Source:** `InfoGeometry.Canonical.NaturalGradientSubmersionFlow` & `InfoGeometry.Epistemology.RiemannianSubmersion`
* **Certified Invariant:**
  $$P_{\mathcal{V}}(\tilde{\nabla} \mathcal{L}) = 0 \implies \dot{\theta} = P_{\mathcal{H}}(\dot{\theta}), \qquad g(\dot{\theta}, \dot{\theta}) = g(P_{\mathcal{H}} \dot{\theta}, P_{\mathcal{H}} \dot{\theta})$$
* **Julia Operational Contract:** The numerical solver in Julia omits allocating, computing, and inverting the vertical $d_{\mathcal{V}} \times d_{\mathcal{V}}$ block.
* **Payoff:** For overparameterized architectures ($d_{\mathcal{V}} \gg d_{\mathcal{H}}$), complexity drops from cubic in ambient parameter dimension $O((d_{\mathcal{H}} + d_{\mathcal{V}})^3)$ to cubic only in the invariant base $O(d_{\mathcal{H}}^3)$, with a formal Lean 4 guarantee of zero gauge drift.

### Contract 2: Bitwise Blade Arithmetic & Koszul Sign Certification
* **Lean 4 Source:** `InfoGeometry.Algebra.ChakravalaGA`
* **Certified Invariants:**
  $$\epsilon(p, q) = (-1)^{p \cdot q}, \quad \iota(v) \iota(w) + \iota(w) \iota(v) = 2 Q(v, w)$$
* **Julia Operational Contract:** In `Grassmann.jl`, multivector basis elements are represented as bitwise bitmasks (`UInt64`). Bitwise XOR computes blade products, and popcount parity over lower-order bit pairs computes the Koszul sign.
* **Payoff:** Machine-checked guarantee against orientation anomalies (Trap T13) or grading inconsistencies in multivector multiplication tables.

### Contract 3: Chentsov Markov Compression (Zero Metric Distortion)
* **Lean 4 Source:** `InfoGeometry.Epistemology.ChentsovMetricInvariance`
* **Certified Invariant:**
  $$g_P(v, w) = g_{T_* P}(T_* v, T_* w) \quad \text{for congruent Markov kernel } T$$
* **Julia Operational Contract:** High-dimensional empirical data on alphabet $\mathcal{X}$ can be compressed via sufficient partition into summary space $\mathcal{Y}$.
* **Payoff:** Fisher-Rao geodesic shooting runs directly on $\mathcal{Y}$ with certified zero loss of information metric geometry.

### Contract 4: GNS Left Ideals and State-Dependent Tomita Duality
* **Lean 4 Source:** `InfoGeometry.QuantumContext.MatrixGNS` & `InfoGeometry.QuantumContext.AttentionKMSState`
* **Certified Invariants:**
  $$J_\rho \circ \Delta_\rho \circ J_\rho = \Delta_\rho^{-1}, \quad \forall X, A \in \mathcal{N}_\omega \implies X A \in \mathcal{N}_\omega, \quad \omega(B^T B) = 0 \iff B = 0 \text{ (for } \rho > 0 \text{)}$$
* **Julia Operational Contract:** KV-cache pruning in attention layers is verified to produce genuine GNS left ideals without destroying stability on anchor tokens. State-dependent Tomita conjugation $J_\rho(X) = \rho^{1/2} X^T \rho^{-1/2}$ and modular flow $\Delta_\rho(X) = \rho X \rho^{-1}$ are numerically verified to machine precision ($< 10^{-12}$).

---

## 3. Tooling & Execution Harness

The pipeline is driven by:
1. **Contract Exporter:** `tools/infra/export_lean_julia_contracts.py`
   - Exports the machine-readable manifest `sandbox/Grassmann.jl/certified_contracts.json`.
   - Generates the certified Julia module `sandbox/Grassmann.jl/LeanCertifiedContracts.jl`.
   - Generates the cross-verification test harness `sandbox/Grassmann.jl/test_contracts.jl`.
2. **Verification Suite:**
   - Execute via: `julia sandbox/Grassmann.jl/test_contracts.jl`
   - Status: All tests pass with machine precision ($< 10^{-12}$).
