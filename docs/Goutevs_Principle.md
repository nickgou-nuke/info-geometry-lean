# Goutev’s Principle: The Absolute Relativity of Measurement

This document formalizes the foundational theoretical axiom of the `info-geometry-lean` repository.

## The Principle

**Absolute Relativity of Measurement**
There is no measurement in isolation. Every measurement is a comparison. What is physically meaningful is not an absolute magnitude, but a relation between magnitudes.

## Formal Statement

A measurement does not determine a primitive scalar value ($x$) with standalone physical meaning. It determines only a relational quantity between the measured object and a reference configuration, background, ensemble, apparatus, or comparison class. Therefore, the physical content of measurement is invariant under common rescalings of the compared magnitudes, and the genuine observables are ratios, relative densities, contrasts, or gauge-invariant comparison functionals.

**Corollary: Normalization is not ontology; it is gauge fixing.**

## Axiomatic Structure

### Axiom 1. Relationality
No measurement outcome has physical meaning without a reference class.

### Axiom 2. Gauge of Common Scale
If all compared magnitudes are rescaled by the same positive factor, the physical content is unchanged ($x \sim \lambda x$ for $\lambda > 0$).

### Axiom 3. Comparison Invariance
Only quantities invariant under common rescaling (projective invariants) are admissible as physical observables.

### Axiom 4. Relative Composition
If a quantity is measured relative to a second, and the second relative to a third, the physically meaningful law is the composition law of these relations. In multiplicative form, this yields ratios and cocycles; in additive form, it yields log-differences and potentials.

## Mathematical Implementation in the Repository

The repository's architecture is a direct realization of Goutev’s Principle:

1.  **Projective State Space:** The primary objects at `rep_depth projective` (L1) are `PositiveRay` types, which are equivalence classes of measures under positive rescaling.
2.  **Relative Potentials:** The `RelativePotential` is treated as a core object, not a derived one, representing the logarithmic contrast between states.
3.  **Cocycle Logic:** Morphisms between layers (e.g., from raw counts to operators) are enforced as cocycles, satisfying the Relative Composition axiom.
4.  **Operator Lifts:** Physical observables are lifted to operators only after their relational structure is established, ensuring that "absolute" operators remain representationally convenient rather than ontologically primitive.

## Distinction from Jaynesian Inference

*   **Jaynes-type claim (Epistemic):** Probability assignments are relative to prior information.
*   **Goutev-type claim (Ontological/Structural):** Measurement outcomes themselves are relative structures; absolute magnitudes are not physically primitive.

Measurement is projective; observables are relational invariants.
