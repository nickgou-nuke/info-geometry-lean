# 🎭 Dvořák-Pauli Synthesis: The Standards of Truth and Beauty

This document records the integration of **Martin Dvořák's "Truth and Beauty"** framework into the **Info-Geometry Spire**. It serves as the operational guide for maintaining "Non-Vacuous" and "Believable" formalizations.

## ⚖️ The Core Philosophy
As established in Dvořák's 2026 thesis and the repository's `PAULI_MANDATE.md`:
*   **Truth** is located in the **Definitions and Statements**. A formalization is "untrue" if its definitions are tailored to make the proof easier rather than representing the mathematical reality.
*   **Beauty** is the proxy for **Nomological Closure**. A beautiful proof is one where the conclusion is the *Necessary Consequence* of the algebra, free of "ugly" hacks or "Agentic Cheating."

## 🛠️ Toolchain Components

### 1. The `aeply` Tactic
*   **Location:** `lean/InfoGeometry/Meta/DvorakTactics.lean`
*   **Logic:** `try intro <;> apply $t <;> aesop`
*   **Purpose:** To automate the preservation of "validity conditions" (e.g., `Measurable`, `IsProbabilityMeasure`) during transformations. It ensures that we don't just "apply a lemma" but also "close the manifold" of side-goals.

### 2. Extended Field Algebra (`Extend F`)
*   **Location:** `lean/InfoGeometry/Core/ExtendedField.lean`
*   **Purpose:** To rigorously handle $\infty$ and $-\infty$ in info-geometric metrics (KL-divergence, Shannon entropy).
*   **Standard:** Use `Extend F` instead of `Option F` or `ENNReal` when the algebraic properties of the "Extended Field" (ELOF) are required for non-vacuity.

### 3. The Truth Audit (`dvorak_audit.py`)
*   **Location:** `tools/quality/dvorak_audit.py`
*   **Goal:** To detect **Symbolic Inflation** and **Lyrical Overfit**.
*   **Key Checks:**
    *   **Reflexivity Gate:** Flagging `rfl`-based proofs of high-level physics-loaded names (Directive I & V).
    *   **Vacuity Gate:** Scanning for `sorry` or `Admission` where explicit construction is needed.
    *   **Axiom Gate:** Detecting `classical.choice` usage for physical parameters (Directive X).

## 🏛️ Ingestion Trace
The Dvořák Thesis was ingested using the **Alexandria** toolchain on 2026-04-28.
*   **Source:** [https://madvorak.github.io/2026_Dvorak_Martin_Thesis_improved.pdf](https://madvorak.github.io/2026_Dvorak_Martin_Thesis_improved.pdf)
*   **Semantic Basins:** 1,080 chunks stored in ArangoDB for "Strong Gravitation" context extraction.

---
*"Mathematics is forced by algebra; the rest is silence."*
