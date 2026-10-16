# Open Debt Problems — Exhaustive Deep-Search Audit

> **Historical audit date**: 2026-07-24
> **Current status**: This inventory is stale and must not be used as a current repository-wide sorry count. The specific source claims below were checked against the present owner files during the 2026-10-16 review.

This document is a historical debt note, not an exhaustive current audit. Names and status below are corrected only for the inspected owner files; no repository-wide gap count is asserted.

---

## 1. Closed Sectors (100% Proved / Verifiable)

The following sectors have been fully solved, with all stubs and `sorry` keywords eliminated in favor of genuine proofs checked by the Lean 4 kernel:

| Sector | Description / Notes |
| :--- | :--- |
| **Gell-Mann Basis** | Fully proved Gell-Mann basis matrix product tables, trace identities, and commutator properties in `SU3GellMannLieAlgebra.lean`. |
| **Cuntz-Fibonacci** | Fully proved the Cuntz-Fibonacci Five Hypotheses in `CuntzFibonacciFiveHypotheses.lean`, verifying representation, shift commutativity, and braid non-commutativity. |
| **Grover Bound** | Proved Grover optimal success probability lower bound using real analysis mono bounds. |
| **Golden Mean Shift** | All stubs (`X_root`, `braid_flow_noncomm`, `subalgebra_isomorphic_to_golden_quotient`) have been fully proved or resolved in the live codebase and synchronized in the sandbox. |
| **Chevalley Spinors** | Fully proved the coordinate-free Chevalley spinor representation machinery natively in `ChevalleySpinorBlueprint.lean` with exactly zero axioms and zero sorries, using Mathlib's `contractLeft` and `ι` maps. |

---

## 2. Corrected Status of the Formerly Listed Targets

The former claim that these were two active `sorry` declarations is inaccurate for the current source. The following is limited to these two files and is not a complete audit of `lean/InfoGeometry/`.

### A. [GenuineBounds.lean](../lean/InfoGeometry/Arithmetic/GenuineBounds.lean)
The file contains no `sorry` declaration in the inspected source. `primeCounting_le_add_one` proves only the elementary finite-cardinality inequality `Nat.primeCounting x ≤ x + 1`; it is not a Rosser–Schoenfeld estimate against `li(x)`. The scale lemmas `prime_count_error_scale_pos` and `chebyshev_error_scale_nonneg` prove positivity/nonnegativity of displayed expressions, not prime-counting estimates.

### B. [Pin55KreinConformalBridge.lean](../lean/InfoGeometry/Lie/Pin55KreinConformalBridge.lean)
The inspected file has no `sorry` declaration. `exists_pin55_krein_conformal_package` takes `Pin55FiniteCarrierCompatibility` as an explicit hypothesis, so it does not prove that compatibility. Its concrete bilinear form is zero (`B_concrete_zero`), which does not establish a nondegenerate Krein form. Treat the finite-carrier intertwining and any nondegenerate Krein bridge as open mathematical work unless separately supplied by a proved owner theorem.

---

## 3. Audit Scope

This correction is based on current source inspection of the two named owners and their direct references. It does not certify the entire repository's placeholder status or build state. A current global debt inventory requires a fresh exhaustive scan, dependency/taint analysis, and the repository's locked verification pipeline.
