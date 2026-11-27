/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Lean
import InfoGeometry.Lint.Vacuity
import InfoGeometry.Lint.WitnessLint
import InfoGeometry.Meta.Admission
import InfoGeometry.Meta.ArchitectureAudit
import InfoGeometry.Meta.RegionPolicy
import InfoGeometry.Meta.Trust

open Lean Elab Command

namespace InfoGeometry

/-- Collect soft admission evidence from the Lean-side vacuity and witness-pack linters. -/
def collectSoftEvidence
    (env : Environment)
    (declName : Name) : CoreM InfoGeometry.Meta.SoftEvidence := do
  let queryEnv := env.setExporting false
  let runVacuity :=
    match queryEnv.find? declName with
    | some (.inductInfo _) => Lean.isStructure queryEnv declName
    | some _ => true
    | none => false
  let mut vacuityHints ←
    if runVacuity then
      (InfoGeometry.Lint.lintDecl queryEnv declName).toList.mapM fun msg => msg.toString
    else
      pure []
  if Lean.isStructure queryEnv declName then
    let pairs := InfoGeometry.Lint.detectWitnessPackPairs queryEnv declName
    let witnessHints ←
      (InfoGeometry.Lint.renderAllWitnessPackDiags declName pairs).toList.mapM fun msg => msg.toString
    for h in witnessHints do
      if !vacuityHints.contains h then
        vacuityHints := vacuityHints ++ [h]
  return {
    vacuityHints := vacuityHints
    graphRoleHints := []
    plannerHints := []
  }

private def auditReportFromHard
    (policy : InfoGeometry.Meta.PolicySnapshot)
    (env : Environment)
    (declName : Name)
    (hard : InfoGeometry.Meta.HardEvidence) : CoreM InfoGeometry.Meta.AdmissionReport := do
  let region := InfoGeometry.Meta.regionOfDecl policy declName
  let soft ← collectSoftEvidence env declName
  let (baseDecision, rawReasons) := InfoGeometry.Meta.evaluateAdmission policy hard soft
  let decision := InfoGeometry.Meta.adjustDecisionForRegion region baseDecision
  let reasons :=
    let reasons := rawReasons.map fun reason => { reason with declName := declName }
    match decision, baseDecision with
    | .notPromotable, .admitted =>
        reasons.push <|
          InfoGeometry.Meta.mkAdmissionReason declName "region.not_promotable" "warning"
            s!"declaration is admitted in the `{region.asString}` region but not promotable to the protected canonical ring."
    | _, _ => reasons
  return {
    declName := declName
    region := region.asString
    decision := decision
    hard := hard
    soft := soft
    reasons := reasons
    policyVersion := InfoGeometry.Meta.admissionPolicyVersion
  }

private def auditReportForDecl
    (policy : InfoGeometry.Meta.PolicySnapshot)
    (declName : Name) : CoreM InfoGeometry.Meta.AdmissionReport := do
  let env ← getEnv
  let hard ← InfoGeometry.Meta.collectHardEvidence policy declName
  auditReportFromHard policy env declName hard

private def auditReportsForDecls
    (policy : InfoGeometry.Meta.PolicySnapshot)
    (decls : Array Name) : CoreM (Array InfoGeometry.Meta.AdmissionReport) := do
  if decls.isEmpty then
    return #[]
  let env ← getEnv
  let hardMap ← InfoGeometry.Meta.collectHardEvidenceBatch policy decls
  let mut reports : Array InfoGeometry.Meta.AdmissionReport := #[]
  for declName in decls do
    let some hard := hardMap[declName]?
      | throwError "trust audit missing batch hard evidence for `{declName}`"
    reports := reports.push (← auditReportFromHard policy env declName hard)
  return reports

private def logAdmissionReport (report : InfoGeometry.Meta.AdmissionReport) : CommandElabM Unit := do
  let summary :=
    s!"[admission] {report.declName}: {report.decision.asString} ({report.region})"
  match report.decision with
  | .blocked => logError summary
  | .needsReview | .notPromotable => logWarning summary
  | .admitted => logInfo summary
  for reason in report.reasons do
    let detail := s!"  [{reason.code}] {reason.message}"
    match reason.severity with
    | "error" => logError detail
    | "warning" => logWarning detail
    | _ => logInfo detail
  logInfo s!"[admission-json] {(toJson report).compress}"

private def auditAndLogReports
    (reports : Array InfoGeometry.Meta.AdmissionReport) : CommandElabM Unit := do
  for report in reports do
    logAdmissionReport report
  let blockedCount : Nat := reports.foldl (init := 0) fun acc report =>
    if report.decision == .blocked then acc + 1 else acc
  if blockedCount > 0 then
    throwError "Admission audit failed with {blockedCount} blocked declaration(s)."
  if reports.isEmpty then
    logInfo "[admission] no auditable declarations matched the current selector."

private def isFilteredDeclName (env : Environment) (declName : Name) : Bool :=
  declName.isInternal ||
    declName.isInternalDetail ||
    Lean.isPrivateName declName ||
    declName.hasMacroScopes ||
    Lean.isAuxRecursor env declName ||
    Lean.isNoConfusion env declName ||
    Lean.isSparseCasesOn env declName

private def currentModuleDecls : CoreM (Array Name) := do
  let env ← getEnv
  let queryEnv := env.setExporting false
  let decls :=
    InfoGeometry.Meta.ArchitectureAudit.foldCurrentModuleConsts queryEnv #[] fun acc declName info =>
      if isFilteredDeclName queryEnv declName then
        acc
      else if InfoGeometry.Meta.isAuditableDecl info then
        acc.push declName
      else
        acc
  pure <| decls.qsort (fun a b => toString a < toString b)

private def namespaceDecls (ns : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let queryEnv := env.setExporting false
  let nsRoot := ns.getRoot
  let decls :=
    InfoGeometry.Meta.ArchitectureAudit.foldScopedModuleConsts queryEnv
      (fun _ modName =>
        !InfoGeometry.Meta.ArchitectureAudit.isExternalUpstreamModule modName || modName.getRoot == nsRoot)
      #[] fun acc declName info =>
        if isFilteredDeclName queryEnv declName then
          acc
        else if !Name.isPrefixOf ns declName then
          acc
        else if InfoGeometry.Meta.isAuditableDecl info then
          acc.push declName
        else
          acc
  pure <| decls.qsort (fun a b => toString a < toString b)

syntax (name := auditAdmissionDecl) "#audit_admission " ident : command
syntax (name := auditAdmissionFile) "#audit_admission_file" : command
syntax (name := auditAdmissionNamespace) "#audit_admission_namespace " ident : command

elab_rules : command
  | `(#audit_admission $declIdent:ident) => do
      let policy := InfoGeometry.Meta.defaultPolicySnapshot
      let declName ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo declIdent
      let report ← liftCoreM <| auditReportForDecl policy declName
      auditAndLogReports #[report]

elab_rules : command
  | `(#audit_admission_file) => do
      let policy := InfoGeometry.Meta.defaultPolicySnapshot
      let decls ← liftCoreM currentModuleDecls
      let reports ← liftCoreM <| auditReportsForDecls policy decls
      auditAndLogReports reports

elab_rules : command
  | `(#audit_admission_namespace $nsIdent:ident) => do
      let policy := InfoGeometry.Meta.defaultPolicySnapshot
      let ns := nsIdent.getId
      let decls ← liftCoreM <| namespaceDecls ns
      let reports ← liftCoreM <| auditReportsForDecls policy decls
      auditAndLogReports reports

end InfoGeometry

/-!
# InfoGeometry.AuditStrict

Strict repository-admission command surface.

This lightweight module exposes post-hoc admission commands for declarations
already present in the importing environment:

- `#audit_admission <decl>`
- `#audit_admission_file`
- `#audit_admission_namespace <ns>`
-/
