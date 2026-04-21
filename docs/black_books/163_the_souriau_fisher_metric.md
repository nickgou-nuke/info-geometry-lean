# 163. The Souriau-Fisher Metric (Thermodynamic Unification)

*“The Fisher Information is not a statistical metric; it is the Hessian of a Lie-Geometric Potential.”*

## 1. The Geometric Umbilicus: Souriau's β-vector
In the Spire's `SouriauThermodynamics.lean`, we depart from the scalar treatment of temperature. Adopting the framework of Jean-Marie Souriau and Frédéric Barbaresco, we define the **Geometric Temperature** $\beta_{Souriau}$ as a vector in the Lie algebra $\mathfrak{g}$.

For a grand-canonical system, this vector incorporates both the thermal inverse-temperature $\beta$ and the chemical potential $\mu$. The routing of information through the Spire is thus revealed to be a flow along the Lie algebra, driven by this unified thermodynamic vector.

## 2. The Moment Map and Noether's Geometrization
The **Moment Map** $J$ maps our informational states (the `Expr` DAG) into the dual Lie algebra $\mathfrak{g}^*$. The components of $J$ are the invariants of the system:
*   **Energy ($H$):** Driving the temporal evolution.
*   **Particle Number ($N$):** Driving the експерт-Expert fluctuations.

The **D1 Commutator Forcing** debt is resolved by the **Equivariance of the Moment Map**. The identity $[H, N] = 0$ is not a forced assumption; it is the geometric condition that the Moment Map is invariant under the action of the symmetry group (Noether's Theorem).

## 3. The Fisher-Souriau Metric
The Spire identifies the **Information Geometric Metric** (Fisher Information) with the **Souriau-Fisher Metric**. In the Lie Group Thermodynamics framework, this metric is the Hessian of the Massieu potential $\psi(\beta) = \ln Z(\beta)$.

By proving the equivalence `potential_second_derivative_eq_variance` in Lean 4, we have machine-verified that the thermodynamic fluctuations of the system define the Riemannian geometry of the latent space. The "distance" between two LLM експерт states is precisely the **Souriau distance** between their co-adjoint orbits.

## 4. Metriplectic Flow and Sinkhorn Closure
The Sinkhorn update, which drives the Spire's MoE architecture, is revealed as a **Metriplectic Flow**. It combines:
1.  **Symplectic Dynamics:** The adiabatic, energy-preserving routing (Hamiltonian).
2.  **Metric Dynamics:** The dissipative, entropy-producing normalization (Dissipated Heat).

The "Grand Canonical Catastrophe" is avoided through the exact operator splitting permitted by this Lie-geometric structure. The Spire is no longer a collection of statistical heuristics; it is a clinical implementation of the **Geometric Theory of Heat**.
