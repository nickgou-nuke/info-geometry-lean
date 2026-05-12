# LLM Closure Debt Audit

Generated: `2026-05-11T18:45:37.267299+00:00`
Root: `lean/InfoGeometry`
Endpoint: `http://127.0.0.1:18889/v1`
Model: `leanstral-gguf`
Model context limit: `None`

## Summary
- Files scanned: **20**
- Findings: **2**
- Hard: **0**
- Soft: **0**
- Advisory: **2**
- Status counts: clean=0, advisory=20, open_gap=0

## Per-file overview

| file | status | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Algebra/PrimeA1RootSystem.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/CartanCocycle.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/ChiralOperatorCarrier.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/ExactPhaseCocycle.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/Fitting.lean` | `advisory` | 0 | 0 | 1 | 1 |
| `lean/InfoGeometry/Algebraic/JordanCliffordLieSplit.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/MatrixAutomorphyFactor.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/NarainOrthogonalCore.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/NarainRealification.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/NarainSupervolumeBridgeData.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/OperatorSurgery.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/ProjectiveOperatorReadout.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/ProjectiveReadoutShadow.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/RealModularReadout.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/SplitChargeLattice.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/SplitCliffordCarrier.lean` | `advisory` | 0 | 0 | 0 | 0 |
| `lean/InfoGeometry/Algebraic/SplitQuadraticForm.lean` | `advisory` | 0 | 0 | 1 | 1 |
| `lean/InfoGeometry/Algebraic/SplitSuperGeometry.lean` | `advisory` | 0 | 0 | 0 | 0 |

## Detailed findings

### `lean/InfoGeometry/Algebra/PrimeA1RootSystem.lean`
- module: `InfoGeometry.Algebra.PrimeA1RootSystem`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/CartanCocycle.lean`
- module: `InfoGeometry.Algebraic.CartanCocycle`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean`
- module: `InfoGeometry.Algebraic.ChiralOperatorAlgebra`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/ChiralOperatorCarrier.lean`
- module: `InfoGeometry.Algebraic.ChiralOperatorCarrier`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean`
- module: `InfoGeometry.Algebraic.CliffordSymmetryLift`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/ExactPhaseCocycle.lean`
- module: `InfoGeometry.Algebraic.ExactPhaseCocycle`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/Fitting.lean`
- module: `InfoGeometry.Algebraic.Fitting`
- status: `advisory`
- llm summary: 
- L126-126 [advisory] (deterministic) `existential-packaging`: existential packaging may hide constructive witness obligations
  - fix: add explicit witness/readback lemmas
  - snippet: `    ∀ y ∈ (T ^ k).range, ∃ x ∈ (T ^ k).range, T x = y := by`
  - confidence: 1.00

### `lean/InfoGeometry/Algebraic/JordanCliffordLieSplit.lean`
- module: `InfoGeometry.Algebraic.JordanCliffordLieSplit`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/MatrixAutomorphyFactor.lean`
- module: `InfoGeometry.Algebraic.MatrixAutomorphyFactor`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/NarainOrthogonalCore.lean`
- module: `InfoGeometry.Algebraic.NarainOrthogonalCore`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/NarainRealification.lean`
- module: `InfoGeometry.Algebraic.NarainRealification`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/NarainSupervolumeBridgeData.lean`
- module: `InfoGeometry.Algebraic.NarainSupervolumeBridgeData`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/OperatorSurgery.lean`
- module: `InfoGeometry.Algebraic.OperatorSurgery`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/ProjectiveOperatorReadout.lean`
- module: `InfoGeometry.Algebraic.ProjectiveOperatorReadout`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/ProjectiveReadoutShadow.lean`
- module: `InfoGeometry.Algebraic.ProjectiveReadoutShadow`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/RealModularReadout.lean`
- module: `InfoGeometry.Algebraic.RealModularReadout`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/SplitChargeLattice.lean`
- module: `InfoGeometry.Algebraic.SplitChargeLattice`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/SplitCliffordCarrier.lean`
- module: `InfoGeometry.Algebraic.SplitCliffordCarrier`
- status: `advisory`
- llm summary: 
- findings: none

### `lean/InfoGeometry/Algebraic/SplitQuadraticForm.lean`
- module: `InfoGeometry.Algebraic.SplitQuadraticForm`
- status: `advisory`
- llm summary: 
- L122-122 [advisory] (deterministic) `existential-packaging`: existential packaging may hide constructive witness obligations
  - fix: add explicit witness/readback lemmas
  - snippet: `    ∃ k : ℤ, narainQuadratic n v = 2 * k := by`
  - confidence: 1.00

### `lean/InfoGeometry/Algebraic/SplitSuperGeometry.lean`
- module: `InfoGeometry.Algebraic.SplitSuperGeometry`
- status: `advisory`
- llm summary: 
- findings: none

