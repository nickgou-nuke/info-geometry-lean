# The Gauge-Theoretic Knowledge Graph (Theory Canopy)

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

*Authored: 2026-05-02*

This document outlines the architectural elevation of the `info-geometry-lean-fusion` DAG from a structural index to a dynamical, gauge-theoretic manifold. This is the Level 2 "Spectral/Dynamical" implementation.

## 1. The Chiral Hodge Star ($\star$) on Graphs
*   **Dual Role:** Establishes the duality between Forward-Chaining (Deduction/Compilation) and Backward-Chaining (Abduction/Goal-reduction).
*   **ArangoDB Implementation:** Dictates the orientation of AQL graph traversals.
    *   $\star_{forward}$: `OUTBOUND` traversal mapping known premises to constructible futures.
    *   $\star_{backward}$: `INBOUND` traversal mapping target goals to required past tactics.
*   **Significance:** Formalizes the "Agent's Gaze" and the fundamental asymmetry of the proof space.

## 2. Wilson Loops: The Holonomy of Semantic Translation
*   **Dual Role:** Measures semantic drift and hallucination across the "Multilingual Bridge" (Lean $\leftrightarrow$ Python $\leftrightarrow$ LaTeX $\leftrightarrow$ LLM).
*   **ArangoDB Implementation:** Computation of curvature across cyclic paths of equivalences and translations.
    *   Flat Loop ($W = I$): Translation is perfectly faithful.
    *   Curved Loop ($W \neq I$): Semantic drift or hallucination detected.
*   **Significance:** Provides the `Pauli` linter with a quantitative metric for "anomalous gauge fields" in logic, flagging them for human review.

## 3. Detailed Graph Balance: The KMS State of the Codebase
*   **Dual Role:** Defines the thermal equilibrium of the repository under constant agentic mutation (refactoring vs. expansion).
*   **ArangoDB Implementation:** The stationary distribution ($\pi$) of the "Modular Flow" weights.
    *   Energy Definition: $E(x) = -\log \pi(x)$.
*   **Significance:** Represents the cessation of accumulating Technical Debt. The point where the maintenance cost of abstractions exactly equals their theorem-proving value (the macroscopic realization of Tomita-Takesaki).

## Conclusion
The ArangoDB index is a discrete manifold where:
1.  **AQL** traverses the manifold.
2.  **The Hodge Star** dictates the deductive/abductive flow.
3.  **Wilson Loops** detect representation leaks.
4.  **Detailed Balance** defines the thermal equilibrium of the AI refactoring engine.
