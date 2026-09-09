# Continuous Burn-Down Plan

## Live baseline
- total_open_gaps: 48
- debt_files: 30
- semantic vacuity findings: 13810
- semantic vacuity errors: 1164
- Top debt files see `artifacts/axiom_audit_report.json`.

## False-positive debt to exclude from math burn-down
- `lean/Agent/CompilerBridgeCore.lean:705`: string text, not a real sorry
- `lean/InfoGeometry/Lint/Pauli.lean`: debt-report strings and linter call sites
- `lean/InfoGeometry/Meta/*.lean`: policy/telemetry/audit metadata
- `lean/InfoGeometry/Canonical/CognitiveShadow.lean`: taxonomic data, not math
- `lean/DAG/*Export.lean`: tool code in IO/runtime paths
- `lean/InfoGeometry/Automath/Generated/*.lean`: generated stubs; keep debt labels

## Targeted genuine repair order

### Step 1: `lean/sandbox/GoldenMeanShift.lean`  (3 sorry)
- Lower risk than colimit algebra.
- Context: `matrixToCuntz`, `X_sq`, `Invertible X` are already proved.
- Gaps:
  - `X_root` at line 114: commutation-plus-root classification
  - `braid_flow_noncomm` at line 124: conjugation preserves noncommutativity
  - `subalgebra_isomorphic_to_golden_quotient` at line 133: adjoin quotient algebra iso

### Step 2: `lean/test_zorn.lean`  (8 sorry)
- Blocked by colimit/transport algebra debt.
- Gaps:
  - lines 38, 49, 50, 52: `continuumMul` linear map and cocone naturality
  - lines 59, 60, 61, 62: `left_distrib`, `right_distrib`, `zero_mul`, `mul_zero`

### Step 3: Meta/DAG/tooling debt
- Only if it affects build or closure-debt gates.
- Treat as deferred noise unless import-role evidence shows it blocks owner modules.

## Next step options
- Option A: repair `GoldenMeanShift.lean` sorrys with native mathlib algebra lemmas only
- Option B: produce exact blocker names for `test_zorn.lean` via local mathlib limit/colimit API search before editing