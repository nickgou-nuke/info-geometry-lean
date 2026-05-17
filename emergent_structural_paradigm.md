# Emergent Structural Paradigm: Typed Objective & Structural Programming (TOSP)

> Status: `current architectural authority`
> Audited: 2026-05-17
> Note: Memorialized from the Black Books (Ch. 99, 104, 113, 151), the Rule of Descent, and Goutev's Principle.

## I. Goutev's Principle: The Absolute Relativity of Measurement

At the foundation of this paradigm is **Goutev's Principle**:
> *There is no measurement in isolation. Every measurement is a comparison.*

This dictates that absolute scalar magnitudes are a representational convenience. True physical content lies in **relational invariants**.

*   **Projective Habitat:** The correct mathematical habitat for measurement is a projective space of rays (L1), not an affine space of absolute values.
*   **Normalization is Gauge Fixing:** Scaling by a common positive factor $\lambda > 0$ preserves physics. Choosing a specific normalization (e.g., probability summing to 1) is merely a choice of gauge section.
*   **Reference States:** Every theorem and measurement (e.g., relative entropy, relative modular operator) is an excitation relative to a prepared vacuum or thermal background ($\omega$).

## II. The L0-L5 Ladder of Information Physics

The repository is structured as a hierarchical dictionary between multiple presentations of this relational reality. Each level represents a distinct physical and mathematical "layer":

| Layer | Slug | Domain | Authority |
|---|---|---|---|
| **L0** | `count` | Combinatorial | Discrete counting, cardinality, subsets |
| **L1** | `projective` | Geometric | Rays, gauge scales, Radon-Nikodym relative volume |
| **L2** | `operator` | Algebraic | Endomorphisms, Hilbert spaces, C*-algebras |
| **L3** | `krein` | Metric | Indefinite metrics, doubled geometry, Krein spaces |
| **L4** | `transport` | Dynamical | Modular flows, transport generators, Drazin/MP |
| **L5** | `thermo` | Equilibrium | RN-entropy, free energy, stability, closure |

## III. Practical 2-Categorical Vocabulary

In this paradigm, we do not "choose" one canonical representation; we build functorial dictionaries that "bridge" them:

*   **Objects (Layers):** The formal definitions of the L0-L5 representations (e.g., a Boolean subset at L0, a Fock state at L4).
*   **1-Morphisms (Bridges):** The intertwiners, interfacers, and gauges that map between layers (e.g., `Bridge`, `Socket`, `Equiv`, `WeylGauge`).
*   **2-Morphisms (Proofs):** Native Lean derivation chains proving that bridges preserve relational invariants (e.g., `Witness`, `Certificate`).

## IV. The Rule of Descent

Physical claims at high layers (L4, L5) must descend through lower-layer evidence to reach the Lean kernel.

> **No L5 without descent. No descent without raw witnesses. No truth without Lean.**

## V. Strategy for Debt Closure

Closure debt is defined as **missing 2-morphisms**—gaps where a 1-morphism (bridge) is stated but not yet discharged by a native Lean derivation.

**Strategic Mandate:**
1.  **Identify the Bridge:** Locate the 1-morphism (e.g., `DrazinNullSupport`, `WeylGaugeCantorFockBridge`).
2.  **Acknowledge the Gauge:** Identify the reference state and any gauge normalization (e.g., scaling by structure constant $\varepsilon$).
3.  **Discharge the Witness:** Replace the "witness-gated" scaffolding with a native Lean proof linking the two structures.
4.  **Promote to Native:** Remove the debt label once the 2-morphism is kernel-verified.
