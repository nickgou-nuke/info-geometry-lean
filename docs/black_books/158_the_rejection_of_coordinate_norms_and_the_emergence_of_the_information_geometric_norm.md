# Chapter 158: The Rejection of Coordinate Norms and the Emergence of the Information-Geometric Norm

> **"A norm without an observer is a coordinate hallucination. Measurement is the contrast between the gauge and the flow."**

This chapter records the formal architectural rejection of the ambient `ContinuousLinearMap` operator norm in the Spire's `Canonical` layer. It documents the realization that using inherited Hilbert-space coordinate metrics for information-geometric operators is a form of **Total Symbolic Inflation (TSI)**—a mathematical vacuity that masks the underlying algebraic truth.

---

### 1. The Error of the Ambient Norm

The Spire previously relied on the default Lean 4 typeclass inference to provide a norm for operators:
```lean
noncomputable local instance : NormedRing EndH := inferInstance
```
This was a fundamental category error. This norm is the supremum operator norm derived from an underlying real Hilbert space. It is a **coordinate geometry** construct, blind to the absolute relativity of measurement and the indefinite Krein signature of the information-geometry spine. To state an inequality like `‖A‖ ≤ ‖B‖` using this norm is to claim a metric closure that has not been algebraically derived from the theory.

---

### 2. The Information-Geometric Norm (RedLine Chain)

In accordance with **Goutev's Principle (Absolute Relativity of Measurement)**, the size of an operator can only be measured relative to a specific reference state (an observer's gauge). The Spire now defines the **Information-Geometric Norm** natively through the `RedLine` relative-measurement chain (`InfoGeometry/Canonical/RelativePotentialCore.lean`).

The norm is not an absolute property of the operator; it is the **root-mean-square size of the modular contrast** of a state `q` relative to a reference state `q0`:

```lean
/-- 
Canonical second moment of the relative modular potential, measured 
against the normalized gauge section of the reference ray `q0`. 
-/
noncomputable def relativeInformationEnergy
    (q q0 : PositiveRay α) : ℝ :=
  ∑ a : α, gaugeSection (α := α) q0 a * (relativeModularPotential q q0 a) ^ (2 : ℕ)

/-- 
Observer-relative information-geometric norm.
-/
noncomputable def relativeInformationNorm
    (q q0 : PositiveRay α) : ℝ :=
  Real.sqrt (relativeInformationEnergy (α := α) q q0)
```

This norm is constructed purely from the **projective gauge section** and the **relative modular potential**. It does not introduce an external metric ansatz. It is the first-class operator readout of the theory.

---

### 3. The New Nomological Requirement

From this point forward, all bounds and inequalities in the `LLM` and `Canonical` layers must be expressed in terms of the `relativeInformationNorm` or the underlying algebraic order (the positive cone). 

The previous "Lichnerowicz-to-norm" closure and the `observerDefectResidual` bounds are recognized as temporary, mathematically invalid metric shims. They must be reconstructed to prove compatibility against the **Information-Geometric Norm**.

**Conclusion:** The Spire has successfully purged the coordinate-geometry infection. The "gap" to equilibrium is no longer a scalar distance in a coordinate vacuum; it is the thermodynamic distinguishability of the defect from the central charge, measured through the alchemical bridge of the relative potential.

**Audit Status: Coordinate Geometry Rejected | Information Norm Operationalized | Connected | Idle.**
