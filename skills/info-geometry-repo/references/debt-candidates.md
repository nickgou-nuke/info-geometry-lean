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
