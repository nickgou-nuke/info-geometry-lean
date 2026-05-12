# LLM Closure Debt Audit

Generated: `2026-05-11T18:46:00.297014+00:00`
Root: `lean/InfoGeometry`
Endpoint: `http://127.0.0.1:18889/v1`
Model: `leanstral-gguf`
Model context limit: `2048`

## Summary
- Files scanned: **3**
- Findings: **3**
- Hard: **0**
- Soft: **0**
- Advisory: **3**
- Status counts: clean=1, advisory=2, open_gap=0

## Per-file overview

| file | status | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Algebra/PrimeA1RootSystem.lean` | `clean` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/CartanCocycle.lean` | `advisory` | 0 | 0 | 2 | 2 |
| `lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean` | `advisory` | 0 | 0 | 1 | 1 |

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

