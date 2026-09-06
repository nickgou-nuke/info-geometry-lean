import Lean
import InfoGeometry.Canonical.All
import InfoGeometry.Lint.Vacuity
import InfoGeometry.Lint.Pauli
import InfoGeometry.Meta.Admission
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.RegionPolicy
import InfoGeometry.Meta.Trust

open Lean Elab Command

namespace InfoGeometry

/-- Collect soft admission evidence from the Lean-side vacuity linter. -/
def collectSoftEvidence
    (env : Environment)
    (declName : Name) : CoreM InfoGeometry.Meta.SoftEvidence := do
  let vacuityHints ← (InfoGeometry.Lint.lintDecl env declName).toList.mapM fun msg => msg.toString
  return {
    vacuityHints := vacuityHints
    graphRoleHints := []
    plannerHints := []
  }

private def auditReportForDecl
    (policy : InfoGeometry.Meta.PolicySnapshot)
    (declName : Name) : CoreM InfoGeometry.Meta.AdmissionReport := do
  let env ← getEnv
  let region := InfoGeometry.Meta.regionOfDecl policy declName
  let hard ← InfoGeometry.Meta.collectHardEvidence policy declName
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
  }

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

private def currentModuleDecls : CoreM (Array Name) := do
  let env ← getEnv
  let currentModule := env.mainModule
  let decls :=
    env.constants.fold (init := #[]) fun acc declName _ =>
      if declName.isInternal || declName.hasMacroScopes then
        acc
      else
        match env.find? declName with
        | some info =>
            if !InfoGeometry.Meta.isAuditableDecl info then
              acc
            else if InfoGeometry.Meta.moduleNameOf env declName == currentModule then
              acc.push declName
            else
              acc
        | none => acc
  pure <| decls.qsort (fun a b => toString a < toString b)

private def namespaceDecls (ns : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let decls :=
    env.constants.fold (init := #[]) fun acc declName _ =>
      if declName.isInternal || declName.hasMacroScopes then
        acc
      else if !Name.isPrefixOf ns declName then
        acc
      else
        match env.find? declName with
        | some info =>
            if InfoGeometry.Meta.isAuditableDecl info then
              acc.push declName
            else
              acc
        | none => acc
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
      let mut reports := #[]
      for declName in decls do
        reports := reports.push (← liftCoreM <| auditReportForDecl policy declName)
      auditAndLogReports reports

elab_rules : command
  | `(#audit_admission_namespace $nsIdent:ident) => do
      let policy := InfoGeometry.Meta.defaultPolicySnapshot
      let ns := nsIdent.getId
      let decls ← liftCoreM <| namespaceDecls ns
      let mut reports := #[]
      for declName in decls do
        reports := reports.push (← liftCoreM <| auditReportForDecl policy declName)
      auditAndLogReports reports

end InfoGeometry

/-!
# InfoGeometry.AuditStrict

Strict repository-admission umbrella.

This file keeps the existing representation-depth audit active and exposes the
post-hoc admission commands:

- `#audit_admission <decl>`
- `#audit_admission_file`
- `#audit_admission_namespace <ns>`
-/

#audit_architecture
