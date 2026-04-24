# Surrogate Index

Generated: `2026-04-25 01:28:18`

This report tracks explicit proof gaps, assumption-bearing theorem surfaces, and named contract interfaces so surrogate debt can be replaced aggressively with real proofs.

## Hard Gate
- `scripts/audit_surrogates.sh`: **FAIL**
- last gate output:
  - `scripts/audit_surrogates.sh: line 22: rg: command not found`
  - `scripts/audit_surrogates.sh: line 29: rg: command not found`
  - `scripts/audit_surrogates.sh: line 58: rg: command not found`
  - `scripts/audit_surrogates.sh: line 132: rg: command not found`
  - `scripts/audit_surrogates.sh: line 132: rg: command not found`
  - `scripts/audit_surrogates.sh: line 148: rg: command not found`

## Counts
- total tracked findings: **12**
- proof holes: **4**
- explicit axiom declarations: **0**
- quarantine manifest drift findings: **0**
- vacuous `trivial` theorems: **0**
- constant `Prop := True/False` surfaces: **0**
- universal `∀ _, True` fields: **0**
- zero quadratic-form surrogates: **0**
- scaled-zero quadratic-form surrogates: **0**
- conditional theorem wrappers (`_of_axioms/_of_hypotheses/_of_assumptions`): **0**
- named contract declarations (`Axioms/Hypotheses/Assumptions`): **4**
- contract constructors (`to...Assumptions`, `..._of_concrete`, `..._of_finiteSupport`): **0**
- stable surrogate/placeholder markers: **4**
- canonical findings: **2**
- other stable findings: **10**
- unstable/archive findings: **0**

## Aggressive Replacement Queue
- `critical` `proof_hole` evaluateAdmission at `lean/InfoGeometry/Meta/Admission.lean:141`
- `critical` `proof_hole` StrictDeclData at `lean/InfoGeometry/Meta/StrictDef.lean:18`
- `critical` `proof_hole` validateStrictDeclSyntax at `lean/InfoGeometry/Meta/StrictDef.lean:31`
- `critical` `proof_hole` validateStrictDeclSyntax at `lean/InfoGeometry/Meta/StrictDef.lean:34`
- `medium` `contract_decl` DrazinInfiniteAssumptions at `lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean:529`
- `medium` `contract_decl` KitaevRepoHypotheses at `lean/InfoGeometry/Canonical/SYKKitaevGuardrails.lean:92`
- `medium` `contract_decl` legacyInfiniteAssumptionsName at `lean/InfoGeometry/Meta/DrazinRefactor.lean:17`
- `medium` `contract_decl` defaultForbiddenAxioms at `lean/InfoGeometry/Meta/Trust.lean:14`
- `medium` `surrogate_marker` matrixDrazinInverse at `lean/InfoGeometry/Exploration/Symphony/Draft.lean:15`
- `medium` `surrogate_marker` CompilerTelemetryShadow at `lean/InfoGeometry/LLM/CompilerRosetta.lean:9`
- `medium` `surrogate_marker` ProofStateShadow at `lean/InfoGeometry/LLM/ProofSamplingShadow.lean:8`
- `medium` `surrogate_marker` SupertraceFisherShadow at `lean/InfoGeometry/SuperMetriplectic/SupertraceBodyBridge.lean:29`

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

- none

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

- `lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean:529` `structure DrazinInfiniteAssumptions` [medium]
- `lean/InfoGeometry/Canonical/SYKKitaevGuardrails.lean:92` `def KitaevRepoHypotheses` [medium]
- `lean/InfoGeometry/Meta/DrazinRefactor.lean:17` `def legacyInfiniteAssumptionsName` [medium]
- `lean/InfoGeometry/Meta/Trust.lean:14` `def defaultForbiddenAxioms` [medium]

## Contract Constructors

- none

## Stable Surrogate/Placeholder Markers

- `lean/InfoGeometry/Exploration/Symphony/Draft.lean:15` `def matrixDrazinInverse` [medium]
- `lean/InfoGeometry/LLM/CompilerRosetta.lean:9` `structure CompilerTelemetryShadow` [medium]
- `lean/InfoGeometry/LLM/ProofSamplingShadow.lean:8` `structure ProofStateShadow` [medium]
- `lean/InfoGeometry/SuperMetriplectic/SupertraceBodyBridge.lean:29` `structure SupertraceFisherShadow` [medium]

## Policy
- explicit proof holes, explicit axioms, and quarantine-manifest drift are not acceptable end-state theory surface
- vacuous closed proofs (`trivial`, `Prop := True/False`, universal-True fields) count as surrogate debt even when Lean accepts them
- zero-valued surrogate constructions count as debt when they stand in for real mathematical content
- conditional wrappers are tolerated only when the missing obligation is explicit and scheduled for replacement
- contract declarations must not be confused with completed proofs
- contract constructors are lower-risk adapters from concrete data into contract surfaces; they should not dominate the replacement queue
- replacement priority is: canonical proof holes/vacuous proofs -> manifest drift and stable axioms -> canonical conditional wrappers -> open contract interfaces
