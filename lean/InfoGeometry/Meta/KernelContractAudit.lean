import Lean.Util.CollectAxioms
import InfoGeometry.Meta.StrictSurface

namespace InfoGeometry.MetaCompiler.KernelContractAudit

open Lean Meta
open InfoGeometry.Meta
open InfoGeometry.Meta.StrictSurface

structure Request where
  declaration : Name
  expectedType : Expr
  role : DeclRole := .owner

/-- Process-local evidence; not a serialized certificate or a source-file fingerprint. -/
structure Snapshot where
  environment : Lean.Kernel.Environment
  requests : Array Request
  covered : NameSet

private def sameQuotKind : QuotKind → QuotKind → Bool
  | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
  | _, _ => false

/-- Compare declaration payloads, including inductive and recursor metadata, without hashes. -/
def sameDeclaration : ConstantInfo → ConstantInfo → Bool
  | .axiomInfo first, .axiomInfo second => first == second
  | .defnInfo first, .defnInfo second => first == second
  | .thmInfo first, .thmInfo second => first == second
  | .opaqueInfo first, .opaqueInfo second => first == second
  | .ctorInfo first, .ctorInfo second => first == second
  | .recInfo first, .recInfo second => first == second
  | .quotInfo first, .quotInfo second =>
      first.toConstantVal == second.toConstantVal && sameQuotKind first.kind second.kind
  | .inductInfo first, .inductInfo second =>
      first.toConstantVal == second.toConstantVal &&
      first.numParams == second.numParams && first.numIndices == second.numIndices &&
      first.all == second.all && first.ctors == second.ctors &&
      first.numNested == second.numNested && first.isRec == second.isRec &&
      first.isUnsafe == second.isUnsafe && first.isReflexive == second.isReflexive
  | _, _ => false

private def requestRoots (requests : Array Request) : NameSet := Id.run do
  let mut roots : NameSet := {}
  for request in requests do
    roots := roots.insert request.declaration
    roots := roots.union (DAG.collectExprConsts request.expectedType)
  return roots

def capture (requests : Array Request) : CoreM Snapshot := do
  let kernel := (← getEnv).toKernelEnv
  let dependencyEnvironment := Environment.ofKernelEnv kernel
  let roots := requestRoots requests
  let mut covered := roots
  for root in roots.toList do
    covered := covered.union (transitivelyUsedConstants dependencyEnvironment root)
  return { environment := kernel, requests, covered }

private def standardAxiom (name : Name) : Bool :=
  name == ``propext || name == ``Classical.choice || name == ``Quot.sound

/-- Recheck names, closure, types, axioms, ordering and the existing QMS policy.
The request array is a proposed order, not a newly implemented scheduler. -/
def audit (snapshot : Snapshot) : MetaM (Array TelemetryRow) := do
  if snapshot.requests.isEmpty then
    throwError "epistemic.empty_request"
  let environment ← getEnv
  let kernel := environment.toKernelEnv
  let dependencyEnvironment := Environment.ofKernelEnv kernel
  for (name, oldInfo) in snapshot.environment.constants do
    let some currentInfo := kernel.find? name
      | throwError "epistemic.stale_evidence: {name} disappeared"
    unless sameDeclaration oldInfo currentInfo do
      throwError "epistemic.stale_evidence: {name} changed"
  for root in (requestRoots snapshot.requests).toList do
    unless snapshot.covered.contains root do
      throwError "epistemic.incomplete_closure: missing root {root}"
    unless (snapshot.environment.find? root).isSome do
      throwError "epistemic.stale_evidence: root {root} was not captured"
    for axiomName in (← Lean.collectAxioms root) do
      unless standardAxiom axiomName do
        throwError "epistemic.forbidden_axiom: {root} uses {axiomName}"
  for name in snapshot.covered.toList do
    let some info := kernel.find? name
      | throwError "epistemic.incomplete_closure: unknown declaration {name}"
    unless (snapshot.environment.find? name).isSome do
      throwError "epistemic.stale_evidence: dependency {name} was not captured"
    if info.isUnsafe || info.isPartial then
      throwError "epistemic.unsafe_dependency: {name}"
    for (prerequisite, _) in DAG.edgesFromConstantInfo info do
      unless snapshot.covered.contains prerequisite do
        throwError "epistemic.incomplete_closure: {name} requires {prerequisite}"
    if let .axiomInfo _ := info then
      unless standardAxiom name do
        throwError "epistemic.forbidden_axiom: {name}"
  let mut selected : NameSet := {}
  for request in snapshot.requests do
    if selected.contains request.declaration then
      throwError "epistemic.duplicate_target: {request.declaration}"
    selected := selected.insert request.declaration
  let mut earlier : NameSet := {}
  let mut reports : Array TelemetryRow := #[]
  for request in snapshot.requests do
    let some (.thmInfo info) := kernel.find? request.declaration
      | throwError "epistemic.not_checked_theorem: {request.declaration}"
    if request.expectedType.hasExprMVar || request.expectedType.hasLevelMVar ||
        request.expectedType.hasFVar || request.expectedType.hasLooseBVars then
      throwError "epistemic.open_specification: {request.declaration}"
    unless ← isProp request.expectedType do
      throwError "epistemic.not_proposition: {request.declaration}"
    unless ← withNewMCtxDepth <| isDefEq info.type request.expectedType do
      throwError "epistemic.statement_mismatch: {request.declaration}"
    let dependencies := transitivelyUsedConstants dependencyEnvironment request.declaration
    for prerequisite in dependencies.toList do
      if selected.contains prerequisite && !earlier.contains prerequisite then
        throwError "epistemic.invalid_schedule: {request.declaration} requires {prerequisite}"
    reports := reports.push (← auditExistingDeclaration request.declaration request.role)
    earlier := earlier.insert request.declaration
  return reports

/-- Re-run the audit immediately; cached reports and caller overrides are not accepted. -/
def requireAdmission (snapshot : Snapshot) : MetaM (Array TelemetryRow) := do
  let reports ← audit snapshot
  for report in reports do
    unless report.decision == .admitted do
      throwError "epistemic.admission_blocked: {report.name}: {report.decision.asString}"
  return reports

open Elab Command Term in
def checkCommand (declarations : Array Ident) (types : Array (TSyntax `term))
    (requireAccepted : Bool) : CommandElabM Unit := do
  unless declarations.size == types.size do
    throwError "epistemic.contract_arity_mismatch"
  let reports ← liftTermElabM do
    let mut requests : Array Request := #[]
    for (declaration, typeSyntax) in declarations.zip types do
      let name ← realizeGlobalConstNoOverloadWithInfo declaration
      let expectedType ← Term.withoutErrToSorry <| Term.elabType typeSyntax
      Term.synthesizeSyntheticMVarsNoPostponing
      let expectedType ← instantiateMVars expectedType
      requests := requests.push { declaration := name, expectedType }
    let snapshot ← capture requests
    if requireAccepted then
      return ← requireAdmission snapshot
    else
      return ← audit snapshot
  for report in reports do
    logInfo m!"[epistemic-current-environment] {(toJson report).compress}"

open Elab Command in
elab "#audit_epistemic_schedule " "[" declarations:ident,* "]"
    " against " "[" types:term,* "]" : command =>
  checkCommand declarations.getElems types.getElems false

open Elab Command in
elab "#require_epistemic_admission " "[" declarations:ident,* "]"
    " against " "[" types:term,* "]" : command =>
  checkCommand declarations.getElems types.getElems true

end InfoGeometry.MetaCompiler.KernelContractAudit
