# Debt Prompt: Critical Lane

Use this prompt with a Lean-aware review model that aggressively minimizes
replacement plans before anything is materialized in quarantine.

## Hard Constraints

- Treat the creative-lane output as untrusted proposal text.
- Reject invented helper lemmas or unsupported imports.
- Reject plans that only restate the existing debt surface.
- Reject plans that still reduce to `rfl`, direct forwarding, alias transport, or packaging assembly.
- Keep only candidates small enough to materialize in quarantine first.

## Task

Evaluate the creative-lane replacement proposals against the tracked debt packet
and the current debt audits.

For each candidate provide exactly:
1. `name`
2. `review verdict` (`accept` / `revise` / `reject`)
3. `review reason`
4. `quarantine recommendation` (`yes` / `no`)
5. `Lean-ready materialization sketch` (a fenced `lean` code block)
6. `allowed helper lemmas`
7. `blocked moves`

Use the exact field labels above so downstream automation can parse reviewed
materialization packets without manual normalization.

Then end with:
- `Top 3 materialization order`
- `Top 3 rejection reasons`

## Paste Creative Output Below

```text
[PASTE CREATIVE MODEL OUTPUT HERE]
```

## Debt Packet

```md
# Debt Candidates

This note is a report-only constructive replacement queue derived from the tracked
surrogate, vacuity, and thin-bridge audits.

It is not a proof artifact.

The purpose is to pin exact debt targets that can be attacked by a creative lane,
shrunk by a critical lane, and then materialized into quarantine for Lean validation.

## Audit Context

- surrogate findings: `7`
- vacuity findings: `0`
- thin-bridge findings: `5`
- aggregated replacement targets: `11`

## Selection Rule

- Prefer canonical/stable declarations over unstable/archive surfaces.
- Prefer critical/high findings over medium/low findings.
- Aggregate duplicate targets when multiple audits point at the same declaration.
- Keep every candidate tied to a real file:line surface already tracked by the audits.

## Candidate 1

`name`

`DebtCandidate.repair_witten_index_invariant_under_onsager_flow_1`

`Lean-style signature sketch`

```lean
@[rep_depth transport] := by
  -- constructive replacement target generated from the tracked debt packet
```

`why this closes a real frontier edge`

This candidate targets the tracked debt surface `witten_index_invariant_under_onsager_flow` at `lean/InfoGeometry/Canonical/TopologicalResidue.lean:71`. It aggregates the audit signals `surrogate:trivial_theorem (critical)`. A successful replacement would replace the trivial proof with a constructive derivation from load-bearing hypotheses.

`likely proof ingredients already present in repo`

- `target file: lean/InfoGeometry/Canonical/TopologicalResidue.lean`
- `target line: 71`
- `strongest priority: critical`
- `audit signals: surrogate:trivial_theorem (critical)`
- `nearby declarations: InformationalZeroMode, IsTopologicalMemory, wittenIndexResidue`
- `surrogate debt goal: replace the trivial proof with a constructive derivation from load-bearing hypotheses`

`risk level`

`high`

## Candidate 2

`name`

`DebtCandidate.repair_onsager_reciprocity_at_comparison_2`

`Lean-style signature sketch`

```lean
@[rep_depth transport] := by
  -- constructive replacement target generated from the tracked debt packet
```

`why this closes a real frontier edge`

This candidate targets the tracked debt surface `onsager_reciprocity_at_comparison` at `lean/InfoGeometry/Canonical/VariationalLadder.lean:45`. It aggregates the audit signals `surrogate:trivial_theorem (critical)`. A successful replacement would replace the trivial proof with a constructive derivation from load-bearing hypotheses.

`likely proof ingredients already present in repo`

- `target file: lean/InfoGeometry/Canonical/VariationalLadder.lean`
- `target line: 45`
- `strongest priority: critical`
- `audit signals: surrogate:trivial_theorem (critical)`
- `nearby declarations: informationalCurrent, VariationalLadder, IsOnsagerStationary`
- `surrogate debt goal: replace the trivial proof with a constructive derivation from load-bearing hypotheses`

`risk level`

`high`

## Candidate 3

`name`

`DebtCandidate.repair_evaluateAdmission_3`

`Lean-style signature sketch`

```lean
def evaluateAdmission
    (policy : PolicySnapshot)
    (hard : HardEvidence)
    (soft : SoftEvidence) : AdmissionDecision × Array AdmissionReason := by
  -- constructive replacement target generated from the tracked debt packet
```

`why this closes a real frontier edge`

This candidate targets the tracked debt surface `evaluateAdmission` at `lean/InfoGeometry/Meta/Admission.lean:141`. It aggregates the audit signals `surrogate:proof_hole (critical)`. A successful replacement would replace the explicit proof hole with a real Lean proof.

`likely proof ingredients already present in repo`

- `target file: lean/InfoGeometry/Meta/Admission.lean`
- `target line: 141`
- `strongest priority: critical`
- `audit signals: surrogate:proof_hole (critical)`
- `nearby declarations: HardEvidence, SoftEvidence, PolicySnapshot, admissionPolicyVersion, AdmissionReport, AdmissionDecision.asString`
- `surrogate debt goal: replace the explicit proof hole with a real Lean proof`

`risk level`

`high`

## Candidate 4

`name`

`DebtCandidate.repair_StrictDeclData_4`

`Lean-style signature sketch`

```lean
structure StrictDeclData where
  levelParams : List Name
  typeExpr : Expr
  valueExpr : Expr

private def forbiddenTermKinds : List SyntaxNodeKind := by
  -- constructive replacement target generated from the tracked debt packet
```

`why this closes a real frontier edge`

This candidate targets the tracked debt surface `StrictDeclData` at `lean/InfoGeometry/Meta/StrictDef.lean:18`. It aggregates the audit signals `surrogate:proof_hole (critical)`. A successful replacement would replace the explicit proof hole with a real Lean proof.

`likely proof ingredients already present in repo`

- `target file: lean/InfoGeometry/Meta/StrictDef.lean`
- `target line: 18`
- `strongest priority: critical`
- `audit signals: surrogate:proof_hole (critical)`
- `nearby declarations: validateStrictDeclSyntax`
- `surrogate debt goal: replace the explicit proof hole with a real Lean proof`

`risk level`

`high`

## Candidate 5

`name`

`DebtCandidate.repair_validateStrictDeclSyntax_5`

`Lean-style signature sketch`

```lean
def validateStrictDeclSyntax
    (declKind : String)
    (declName : Name)
    (typeStx valueStx : Syntax) : CommandElabM Unit := by
  -- constructive replacement target generated from the tracked debt packet
```

`why this closes a real frontier edge`

This candidate targets the tracked debt surface `validateStrictDeclSyntax` at `lean/InfoGeometry/Meta/StrictDef.lean:31`. It aggregates the audit signals `surrogate:proof_hole (critical), surrogate:proof_hole (critical)`. A successful replacement would replace the explicit proof hole with a real Lean proof; replace the explicit proof hole with a real Lean proof.

`likely proof ingredients already present in repo`

- `target file: lean/InfoGeometry/Meta/StrictDef.lean`
- `target line: 31`
- `strongest priority: critical`
- `audit signals: surrogate:proof_hole (critical), surrogate:proof_hole (critical)`
- `nearby declarations: StrictDeclData`
- `surrogate debt goal: replace the explicit proof hole with a real Lean proof`
- `surrogate debt goal: replace the explicit proof hole with a real Lean proof`

`risk level`

`high`

## Candidate 6

`name`

`DebtCandidate.repair_moorePenroseRightProjector_ne_one_of_hasZeroMode_6`

`Lean-style signature sketch`

```lean
theorem moorePenroseRightProjector_ne_one_of_hasZeroMode
    {A B : S →L[ℝ] S}
    (_hMP : IsMoorePenroseInverse A B)
    (hZero : HasZeroMode (S := by
  -- constructive replacement target generated from the tracked debt packet
```

`why this closes a real frontier edge`

This candidate targets the tracked debt surface `moorePenroseRightProjector_ne_one_of_hasZeroMode` at `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:80`. It aggregates the audit signals `thinness:underscore_hypothesis (medium)`. A successful replacement would replace hidden placeholder hypotheses with explicit constructive assumptions or proved facts.

`likely proof ingredients already present in repo`

- `target file: lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean`
- `target line: 80`
- `strongest priority: medium`
- `audit signals: thinness:underscore_hypothesis (medium)`
- `nearby declarations: NontrivialRegularizationPackage, ZeroModeRegularizationPackage, moorePenroseLeftProjector_ne_one_of_hasZeroMode, drazinProjection_ne_one_of_hasZeroMode, exists_nontrivial_regularization_pair_of_dim_mismatch, nontrivialRegularizationPackage_of_dim_mismatch`
- `thin-bridge debt goal: replace hidden placeholder hypotheses with explicit constructive assumptions or proved facts`

`risk level`

`medium`

## Candidate 7

`name`

`DebtCandidate.repair_moorePenroseLeftProjector_ne_one_of_hasZeroMode_7`

`Lean-style signature sketch`

```lean
theorem moorePenroseLeftProjector_ne_one_of_hasZeroMode
    {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
    {A B : S →L[ℝ] S}
    (_hMP : IsMoorePenroseInverse A B)
    (hZero : HasZeroMode (S := by
  -- constructive replacement target generated from the tracked debt packet
```

`why this closes a real frontier edge`

This candidate targets the tracked debt surface `moorePenroseLeftProjector_ne_one_of_hasZeroMode` at `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:95`. It aggregates the audit signals `thinness:underscore_hypothesis (medium)`. A successful replacement would replace hidden placeholder hypotheses with explicit constructive assumptions or proved facts.

`likely proof ingredients already present in repo`

- `target file: lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean`
- `target line: 95`
- `strongest priority: medium`
- `audit signals: thinness:underscore_hypothesis (medium)`
- `nearby declarations: NontrivialRegularizationPackage, ZeroModeRegularizationPackage, moorePenroseRightProjector_ne_one_of_hasZeroMode, drazinProjection_ne_one_of_hasZeroMode, exists_nontrivial_regularization_pair_of_dim_mismatch, nontrivialRegularizationPackage_of_dim_mismatch`
- `thin-bridge debt goal: replace hidden placeholder hypotheses with explicit constructive assumptions or proved facts`

`risk level`

`medium`

## Candidate 8

`name`

`DebtCandidate.repair_drazinProjection_ne_one_of_hasZeroMode_8`

`Lean-style signature sketch`

```lean
theorem drazinProjection_ne_one_of_hasZeroMode
    {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    {A B : S →L[ℝ] S} {k : ℕ}
    (_hD : IsDrazinInverse A B k)
    (hZero : HasZeroMode (S := by
  -- constructive replacement target generated from the tracked debt packet
```

`why this closes a real frontier edge`

This candidate targets the tracked debt surface `drazinProjection_ne_one_of_hasZeroMode` at `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:109`. It aggregates the audit signals `thinness:underscore_hypothesis (medium)`. A successful replacement would replace hidden placeholder hypotheses with explicit constructive assumptions or proved facts.

`likely proof ingredients already present in repo`

- `target file: lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean`
- `target line: 109`
- `strongest priority: medium`
- `audit signals: thinness:underscore_hypothesis (medium)`
- `nearby declarations: NontrivialRegularizationPackage, ZeroModeRegularizationPackage, moorePenroseRightProjector_ne_one_of_hasZeroMode, moorePenroseLeftProjector_ne_one_of_hasZeroMode, exists_nontrivial_regularization_pair_of_dim_mismatch, nontrivialRegularizationPackage_of_dim_mismatch`
- `thin-bridge debt goal: replace hidden placeholder hypotheses with explicit constructive assumptions or proved facts`

`risk level`

`medium`

## Candidate 9

`name`

`DebtCandidate.repair_bottStep_headNullMinus_9`

`Lean-style signature sketch`

```lean
@[rep_depth krein] theorem bottStep_headNullMinus
    (n : ℕ) :
    bottStepEquiv n (gammaHeadNullMinus n)
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 ((1 / 2 : ℝ), (1 / 2 : ℝ)))
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)) := by
  -- constructive replacement target generated from the tracked debt packet
```

`why this closes a real frontier edge`

This candidate targets the tracked debt surface `bottStep_headNullMinus` at `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:60`. It aggregates the audit signals `thinness:direct_forwarder (medium)`. A successful replacement would replace the direct forwarder with a local constructive derivation.

`likely proof ingredients already present in repo`

- `target file: lean/InfoGeometry/Canonical/ClNNBottBridge.lean`
- `target line: 60`
- `strongest priority: medium`
- `audit signals: thinness:direct_forwarder (medium)`
- `nearby declarations: bottStep_headPair, bottStep_tailLift, bottStep_headNullPlus`
- `thin-bridge debt goal: replace the direct forwarder with a local constructive derivation`

`risk level`

`medium`

## Candidate 10

`name`

`DebtCandidate.repair_bottStep_headNullPlus_10`

`Lean-style signature sketch`

```lean
@[rep_depth krein] theorem bottStep_headNullPlus
    (n : ℕ) :
    bottStepEquiv n (gammaHeadNullPlus n)
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 ((1 / 2 : ℝ), (-(1 / 2 : ℝ))))
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)) := by
  -- constructive replacement target generated from the tracked debt packet
```

`why this closes a real frontier edge`

This candidate targets the tracked debt surface `bottStep_headNullPlus` at `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:68`. It aggregates the audit signals `thinness:direct_forwarder (medium)`. A successful replacement would replace the direct forwarder with a local constructive derivation.

`likely proof ingredients already present in repo`

- `target file: lean/InfoGeometry/Canonical/ClNNBottBridge.lean`
- `target line: 68`
- `strongest priority: medium`
- `audit signals: thinness:direct_forwarder (medium)`
- `nearby declarations: bottStep_headPair, bottStep_tailLift, bottStep_headNullMinus`
- `thin-bridge debt goal: replace the direct forwarder with a local constructive derivation`

`risk level`

`medium`

## Candidate 11

`name`

`DebtCandidate.repair_defaultForbiddenAxioms_11`

`Lean-style signature sketch`

```lean
def defaultForbiddenAxioms : List Name := by
  -- constructive replacement target generated from the tracked debt packet
```

`why this closes a real frontier edge`

This candidate targets the tracked debt surface `defaultForbiddenAxioms` at `lean/InfoGeometry/Meta/Trust.lean:14`. It aggregates the audit signals `surrogate:contract_decl (medium)`. A successful replacement would replace the open contract surface with a concrete proved interface or theorem.

`likely proof ingredients already present in repo`

- `target file: lean/InfoGeometry/Meta/Trust.lean`
- `target line: 14`
- `strongest priority: medium`
- `audit signals: surrogate:contract_decl (medium)`
- `nearby declarations: isAuditableDecl, constantKindLabel, moduleNameOf, collectHardEvidence`
- `surrogate debt goal: replace the open contract surface with a concrete proved interface or theorem`

`risk level`

`medium`
```

## Surrogate Index

```md
# Surrogate Index

Generated: `2026-04-10 00:07:06`

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
```

## Vacuity Index

```md
# Vacuity Index

Generated: `2026-04-10 00:07:06`

This report tracks alias-driven and definitional-identity surfaces that can make a bridge look mathematically deeper than it currently is.

## Status
- vacuity gate: **PASS**
- interpretation: `FAIL` means at least one high-priority alias/identity transport surface still sits on the active theory path

## Counts
- total tracked findings: **0**
- high-priority carrier/identity findings: **0**
- medium-priority explicit marker findings: **0**
- low-priority findings: **0**

## Aggressive Replacement Queue
- none

## Findings
- none

## Policy
- absence of `sorry` is not enough if a bridge is true only by aliasing or identity transport
- carrier aliases on bridge boundaries count as real mathematical debt, even when Lean accepts them
- replacement priority is: carrier aliases -> identity transports -> explicit alias-model compatibility layers
```

## Thin-Bridge Index

```md
# Bridge Thinness Index

Generated: `2026-04-10 00:07:06`

This report is a heuristic audit of bridge-/launchpad-/interface-facing theorem surfaces that may be mathematically thinner than their names suggest.

## Status
- thin-bridge gate: **PASS**
- interpretation: `FAIL` means at least one targeted theorem currently looks like a definitional identity

## Counts
- total tracked findings: **5**
- definitional identity findings: **0**
- direct forwarder findings: **2**
- underscore-hypothesis findings: **3**
- package/orchestration findings: **0**

## Queue
- `medium` `underscore_hypothesis` `moorePenroseRightProjector_ne_one_of_hasZeroMode` at `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:80`
- `medium` `underscore_hypothesis` `moorePenroseLeftProjector_ne_one_of_hasZeroMode` at `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:95`
- `medium` `underscore_hypothesis` `drazinProjection_ne_one_of_hasZeroMode` at `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:109`
- `medium` `direct_forwarder` `bottStep_headNullMinus` at `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:60`
- `medium` `direct_forwarder` `bottStep_headNullPlus` at `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:68`

## Findings
- `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:80` `moorePenroseRightProjector_ne_one_of_hasZeroMode` [medium]
  declaration head contains underscore-prefixed hypotheses: `_hMP`
- `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:95` `moorePenroseLeftProjector_ne_one_of_hasZeroMode` [medium]
  declaration head contains underscore-prefixed hypotheses: `_hMP`
- `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:109` `drazinProjection_ne_one_of_hasZeroMode` [medium]
  declaration head contains underscore-prefixed hypotheses: `_hD`
- `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:60` `bottStep_headNullMinus` [medium]
  proof body is a `simpa ... using bottStep_headPair` forwarder
- `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:68` `bottStep_headNullPlus` [medium]
  proof body is a `simpa ... using bottStep_headPair` forwarder

## Policy
- this is a heuristic syntax audit, not a proof oracle
- `rfl`/direct-forward/package findings are review targets, not automatic verdicts of invalid mathematics
- the purpose is to keep bridge names aligned with actual proof depth
```

## Review Discipline

- Prefer direct repair of the tracked theorem over new wrapper layers.
- If the best action is deletion, renaming, or theorem splitting, say so explicitly.
- A surviving candidate should have a theorem header that the coding agent can materialize verbatim in quarantine.
