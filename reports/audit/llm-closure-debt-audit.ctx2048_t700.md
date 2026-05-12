# LLM Closure Debt Audit

Generated: `2026-05-11T19:08:06.080665+00:00`
Root: `lean/InfoGeometry`
Endpoint: `http://127.0.0.1:18889/v1`
Model: `leanstral-gguf`
Model context limit: `2048`

## Summary
- Files scanned: **8**
- Findings: **9**
- Hard: **0**
- Soft: **0**
- Advisory: **9**
- Status counts: clean=2, advisory=6, open_gap=0

## Per-file overview

| file | status | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Algebra/PrimeA1RootSystem.lean` | `clean` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/CartanCocycle.lean` | `advisory` | 0 | 0 | 2 | 2 |
| `lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean` | `advisory` | 0 | 0 | 1 | 1 |
| `lean/InfoGeometry/Algebraic/ChiralOperatorCarrier.lean` | `advisory` | 0 | 0 | 1 | 1 |
| `lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean` | `clean` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/ExactPhaseCocycle.lean` | `advisory` | 0 | 0 | 1 | 1 |
| `lean/InfoGeometry/Algebraic/Fitting.lean` | `advisory` | 0 | 0 | 2 | 2 |
| `lean/InfoGeometry/Algebraic/JordanCliffordLieSplit.lean` | `advisory` | 0 | 0 | 2 | 2 |

## Detailed findings

### `lean/InfoGeometry/Algebra/PrimeA1RootSystem.lean`
- module: `InfoGeometry.Algebra.PrimeA1RootSystem`
- status: `clean`
- llm summary: The file appears to be clean with no obvious proof holes, axioms, postulates, or other issues.
- findings: none

### `lean/InfoGeometry/Algebraic/CartanCocycle.lean`
- module: `InfoGeometry.Algebraic.CartanCocycle`
- status: `advisory`
- llm summary: The file contains a definition of `pullback` for Cartan automorphy factors, but the implementation is incomplete. The proof obligations for `map_one` and `map_mul` are not fully resolved.
- L99-101 [advisory] (llm) `llm-evidence-mismatch`: LLM claim could not be verified against source excerpt/category lexical checks: proof-hole
  - fix: review file manually or rerun with larger excerpt
  - snippet: `map_one x := by
     rw [J.map_one x]
     exact weightReadout.map_one`
  - confidence: 0.00
- L102-104 [advisory] (llm) `llm-evidence-mismatch`: LLM claim could not be verified against source excerpt/category lexical checks: proof-hole
  - fix: review file manually or rerun with larger excerpt
  - snippet: `map_mul g h x := by
     rw [J.map_mul g h x]
     exact weightReadout.map_mul _ _`
  - confidence: 0.00

### `lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean`
- module: `InfoGeometry.Algebraic.ChiralOperatorAlgebra`
- status: `advisory`
- llm summary: The file contains a definition and some theorems related to Clifford grade involution and chiral operator algebra, but there are gaps in the proof structure.
- L104-104 [advisory] (llm) `llm-evidence-mismatch`: LLM claim could not be verified against source excerpt/category lexical checks: proof-hole
  - fix: review file manually or rerun with larger excerpt
  - snippet: `@[simp]
theorem canonical_modularHamiltonian
    (n : ℕ) :`
  - confidence: 0.00

### `lean/InfoGeometry/Algebraic/ChiralOperatorCarrier.lean`
- module: `InfoGeometry.Algebraic.ChiralOperatorCarrier`
- status: `advisory`
- llm summary: The file contains a placeholder assumption that needs to be addressed.
- L102-103 [advisory] (llm) `llm-evidence-mismatch`: LLM claim could not be verified against source excerpt/category lexical checks: placeholder-assumption
  - fix: review file manually or rerun with larger excerpt
  - snippet: `refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
   exact X.K_sq`
  - confidence: 0.00

### `lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean`
- module: `InfoGeometry.Algebraic.CliffordSymmetryLift`
- status: `clean`
- llm summary: The file appears to be clean with no obvious proof holes, axioms, postulates, or other issues that would require closure debt.
- findings: none

### `lean/InfoGeometry/Algebraic/ExactPhaseCocycle.lean`
- module: `InfoGeometry.Algebraic.ExactPhaseCocycle`
- status: `advisory`
- llm summary: The file contains a placeholder for the `exactBerryPhase` definition and an incomplete comment block.
- L54-60 [advisory] (llm) `llm-evidence-mismatch`: LLM claim could not be verified against source excerpt/category lexical checks: placeholder-name
  - fix: review file manually or rerun with larger excerpt
  - snippet: `/--
This is the algebraic bridge from the concrete `Circle` phase to an abstract
rotor or spin target.`
  - confidence: 0.00

### `lean/InfoGeometry/Algebraic/Fitting.lean`
- module: `InfoGeometry.Algebraic.Fitting`
- status: `advisory`
- llm summary: The file contains an existential packaging construct without a readback, indicating potential issues with proof completion or clarity.
- L124-130 [advisory] (llm) `llm-evidence-mismatch`: LLM claim could not be verified against source excerpt/category lexical checks: existential-packaging
  - fix: review file manually or rerun with larger excerpt
  - snippet: `theorem surjective_on_range {T : Module.End K V} {k : ℕ}
    (hd : DescentStabilized T k) :
    ∀ y ∈ (T ^ k).range, ∃ x ∈ (T ^ k).range, T x = y := by
  intro y hy
  have h_ran : (T ^ k).range = (T ^ (k + 1)).range := hd
  rw [h_ran] at hy
  rcases hy with ⟨x, hx⟩`
  - confidence: 0.00
- L126-126 [advisory] (deterministic) `existential-packaging`: existential packaging may hide constructive witness obligations
  - fix: add explicit witness/readback lemmas
  - snippet: `    ∀ y ∈ (T ^ k).range, ∃ x ∈ (T ^ k).range, T x = y := by`
  - confidence: 1.00

### `lean/InfoGeometry/Algebraic/JordanCliffordLieSplit.lean`
- module: `InfoGeometry.Algebraic.JordanCliffordLieSplit`
- status: `advisory`
- llm summary: The file contains an unfinished proof at the end of the excerpt, and there are potential issues with temporary trust constructs or closure debt that need to be addressed.
- L3-4 [advisory] (llm) `opaque`: The import of 'InfoGeometry.Meta.Architecture' is present, but the module documentation or content following it is not visible in the excerpt. This could potentially hide important definitions or assumptions.
  - fix: Ensure that the module provides clear and complete documentation or expose necessary declarations for downstream use.
  - snippet: `import InfoGeometry.Meta.Architecture

/-!`
  - confidence: 0.70
- L44-46 [advisory] (llm) `llm-evidence-mismatch`: LLM claim could not be verified against source excerpt/category lexical checks: proof-hole
  - fix: review file manually or rerun with larger excerpt
  - snippet: `norm_num
  
 end InfoGeometry.Algebraic`
  - confidence: 0.00

