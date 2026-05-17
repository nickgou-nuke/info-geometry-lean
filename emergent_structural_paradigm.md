# Emergent Structural Paradigm: Typed Objective & Structural Programming (TOSP)

> Status: `current architectural authority`
> Audited: 2026-05-17
> Note: Memorialized from the Black Books (Ch. 99, 104, 151) and the Rule of Descent.

## I. The L0-L5 Ladder of Information Physics

The repository is structured as a hierarchical dictionary between multiple presentations of a single information-geometric reality. Each level represents a distinct physical and mathematical "layer":

| Layer | Slug | Domain | Authority |
|---|---|---|---|
| **L0** | `count` | Combinatorial | Discrete counting, cardinality |
| **L1** | `projective` | Geometric | Support, restriction, probability |
| **L2** | `operator` | Algebraic | Endomorphisms, Hilbert spaces, C*-algebras |
| **L3** | `krein` | Metric | Indefinite metrics, doubled geometry, Krein spaces |
| **L4** | `transport` | Dynamical | Modular flows, transport generators, Drazin/MP |
| **L5** | `thermo` | Equilibrium | RN-entropy, free energy, stability, closure |

## II. Practical 2-Categorical Vocabulary

In this paradigm, we do not "choose" one representation; we "bridge" them:

*   **Objects (Layers):** The formal definitions of the L0-L5 representations.
*   **1-Morphisms (Bridges):** The intertwiners, interfacers, and gates that map between layers (e.g., `Bridge`, `Socket`, `Interface`).
*   **2-Morphisms (Proofs):** Native Lean derivation chains proving that bridges preserve invariants (e.g., `Witness`, `Certificate`).

## III. The Rule of Descent

Physical claims at high layers (L4, L5) must descend through lower-layer evidence to reach the Lean kernel.

> **No L5 without descent. No descent without raw witnesses. No truth without Lean.**

## IV. Strategy for Debt Closure

Closure debt is defined as **missing 2-morphisms**—gaps where a 1-morphism (bridge) is stated but not yet discharged by a native Lean derivation.

**Strategic Mandate:**
1.  **Identify the Bridge:** Locate the 1-morphism (e.g., `DrazinNullSupport`).
2.  **Define the Morphism:** Identify the source (L3 Krein) and target (L2 Operator/Mathlib).
3.  **Discharge the Witness:** Replace the "witness-gated" scaffolding with a native Lean proof linking the two structures.
4.  **Promote to Native:** Remove the debt label once the 2-morphism is kernel-verified.
