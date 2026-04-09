# Surrogate Index

Generated: `2026-04-09 22:54:41`

This report tracks explicit proof gaps, assumption-bearing theorem surfaces, and named contract interfaces so surrogate debt can be replaced aggressively with real proofs.

## Hard Gate
- `scripts/audit_surrogates.sh`: **FAIL**
- last gate output:
  - `[surrogate-audit] checking for imports from InfoGeometry.Unstable in stable modules`
  - `[surrogate-audit] checking for direct open/namespace references to InfoGeometry.Unstable`
  - `[surrogate-audit] checking for placeholder/surrogate keywords outside allowed paths`
  - `lean/InfoGeometry/Canonical/VariationalLadder.lean:48:    -- This is a placeholder for the deep reciprocity proof already present in the repo.`
  - `[surrogate-audit] placeholder/surrogate markers are only allowed under InfoGeometry/Unstable or Archive`

## Counts
- total tracked findings: **7**
- proof holes: **4**
- explicit axiom declarations: **0**
- quarantine manifest drift findings: **0**
- vacuous `trivial` theorems: **2**
- constant `Prop := True/False` surfaces: **0**
- universal `∀ _, True` fields: **0**
- zero quadratic-form surrogates: **0**
- scaled-zero quadratic-form surrogates: **0**
- conditional theorem wrappers (`_of_axioms/_of_hypotheses/_of_assumptions`): **0**
- named contract declarations (`Axioms/Hypotheses/Assumptions`): **1**
- contract constructors (`to...Assumptions`, `..._of_concrete`, `..._of_finiteSupport`): **0**
- stable surrogate/placeholder markers: **0**
- canonical findings: **2**
- other stable findings: **5**
- unstable/archive findings: **0**

## Aggressive Replacement Queue
- `critical` `trivial_theorem` witten_index_invariant_under_onsager_flow at `lean/InfoGeometry/Canonical/TopologicalResidue.lean:71`
- `critical` `trivial_theorem` onsager_reciprocity_at_comparison at `lean/InfoGeometry/Canonical/VariationalLadder.lean:45`
- `critical` `proof_hole` evaluateAdmission at `lean/InfoGeometry/Meta/Admission.lean:141`
- `critical` `proof_hole` StrictDeclData at `lean/InfoGeometry/Meta/StrictDef.lean:18`
- `critical` `proof_hole` validateStrictDeclSyntax at `lean/InfoGeometry/Meta/StrictDef.lean:31`
- `critical` `proof_hole` validateStrictDeclSyntax at `lean/InfoGeometry/Meta/StrictDef.lean:34`
- `medium` `contract_decl` defaultForbiddenAxioms at `lean/InfoGeometry/Meta/Trust.lean:14`

## Explicit Proof Holes

- `lean/InfoGeometry/Meta/Admission.lean:141` `def evaluateAdmission` [critical]
- `lean/InfoGeometry/Meta/StrictDef.lean:18` `structure StrictDeclData` [critical]
- `lean/InfoGeometry/Meta/StrictDef.lean:31` `def validateStrictDeclSyntax` [critical]
- `lean/InfoGeometry/Meta/StrictDef.lean:34` `def validateStrictDeclSyntax` [critical]

## Explicit Axiom Declarations

- none

## Quarantine Manifest Drift

- none

## Vacuous `trivial` Theorems

- `lean/InfoGeometry/Canonical/TopologicalResidue.lean:71` `theorem witten_index_invariant_under_onsager_flow` [critical]
- `lean/InfoGeometry/Canonical/VariationalLadder.lean:45` `theorem onsager_reciprocity_at_comparison` [critical]

## Constant `Prop := True/False` Surfaces

- none

## Universal `∀ _, True` Fields

- none

## Zero Quadratic-Form Surrogates

- none

## Scaled-Zero Quadratic-Form Surrogates

- none

## Conditional Theorem Surface

- none

## Named Contract Declarations

- `lean/InfoGeometry/Meta/Trust.lean:14` `def defaultForbiddenAxioms` [medium]

## Contract Constructors

- none

## Stable Surrogate/Placeholder Markers

- none

## Policy
- explicit proof holes, explicit axioms, and quarantine-manifest drift are not acceptable end-state theory surface
- vacuous closed proofs (`trivial`, `Prop := True/False`, universal-True fields) count as surrogate debt even when Lean accepts them
- zero-valued surrogate constructions count as debt when they stand in for real mathematical content
- conditional wrappers are tolerated only when the missing obligation is explicit and scheduled for replacement
- contract declarations must not be confused with completed proofs
- contract constructors are lower-risk adapters from concrete data into contract surfaces; they should not dominate the replacement queue
- replacement priority is: canonical proof holes/vacuous proofs -> manifest drift and stable axioms -> canonical conditional wrappers -> open contract interfaces
