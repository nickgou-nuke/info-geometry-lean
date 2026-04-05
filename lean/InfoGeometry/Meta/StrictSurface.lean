import Lean
import InfoGeometry.Meta.StrictDef
import InfoGeometry.Meta.Trust

open Lean Meta Elab Command Term

namespace InfoGeometry.Meta.StrictSurface

inductive DeclRole where
  | owner
  | constructor
  | bridge
  deriving Repr, Inhabited, DecidableEq, BEq

def DeclRole.asString : DeclRole → String
  | .owner => "owner"
  | .constructor => "constructor"
  | .bridge => "bridge"

instance : ToJson DeclRole where
  toJson role := Json.str role.asString

structure TelemetryRow where
  name : Name
  declKind : String
  role : DeclRole
  region : String
  decision : AdmissionDecision
  blockers : List String
  hard : HardEvidence
  soft : SoftEvidence
  reasons : Array AdmissionReason
  proofHead : ProofHeadShape
  statementShape : StatementShape
  thinSurface? : Option ThinSurfaceKind := none
  policyVersion : String := admissionPolicyVersion
  deriving Repr, Inhabited

instance : ToJson TelemetryRow where
  toJson row :=
    let thinField :=
      match row.thinSurface? with
      | some thin => [("thinSurface", toJson thin)]
      | none => []
    Json.mkObj <|
      [ ("name", toJson row.name)
      , ("declKind", toJson row.declKind)
      , ("role", toJson row.role)
      , ("region", toJson row.region)
      , ("decision", toJson row.decision)
      , ("blockers", toJson row.blockers)
      , ("hard", toJson row.hard)
      , ("soft", toJson row.soft)
      , ("reasons", toJson row.reasons.toList)
      , ("proofHead", toJson row.proofHead)
      , ("statementShape", toJson row.statementShape)
      , ("policyVersion", toJson row.policyVersion)
      ] ++ thinField

private def declKindLabel : DeclRole → String
  | .owner => "theorem"
  | .constructor => "definition"
  | .bridge => "bridge"

private def lowerShapeToSoftEvidence (role : DeclRole) (shape : ProofShapeReport) : SoftEvidence :=
  match role, shape.thinSurface? with
  | .owner, some thin =>
      { vacuityHints := [s!"owner_thin_surface:{thin.asString}"] }
  | .constructor, some thin =>
      { vacuityHints := [s!"constructor_thin_surface:{thin.asString}"] }
  | .bridge, some thin =>
      { graphRoleHints := [s!"bridge_thin_surface:{thin.asString}"] }
  | _, none =>
      {}

private def extraBlockingReasons
    (declName : Name)
    (role : DeclRole)
    (region : AdmissionRegion)
    (shape : ProofShapeReport) : Array AdmissionReason := Id.run do
  let mut reasons : Array AdmissionReason := #[]
  if region == .protectedRegion && role == .bridge then
    reasons := reasons.push <|
      mkAdmissionReason declName "policy.protected_bridge_role" "error"
        "bridge declarations are not admissible in protected regions."
  if region == .protectedRegion then
    match shape.thinSurface? with
    | some thin =>
        reasons := reasons.push <|
          mkAdmissionReason declName "proof_shape.thin_surface" "error"
            s!"thin {thin.asString} surfaces are not admissible in protected regions."
    | none => pure ()
  reasons

private def blockerCodes (reasons : Array AdmissionReason) : List String :=
  reasons.toList.filterMap fun reason =>
    if reason.severity = "error" then some reason.code else none

private def commitByRole
    (declName : Name)
    (role : DeclRole)
    (data : StrictDeclData) : CommandElabM Unit := do
  match role with
  | .owner =>
      commitStrictTheorem declName data
  | .constructor =>
      commitStrictDef declName data
  | .bridge =>
      if ← liftTermElabM <| isProp data.typeExpr then
        commitStrictTheorem declName data
      else
        commitStrictDef declName data

def processStrictDecl
    (declNameId : Ident)
    (typeStx : Syntax)
    (valStx : Syntax)
    (role : DeclRole) : CommandElabM Unit := do
  let declName := (← getCurrNamespace) ++ declNameId.getId
  let declKind := declKindLabel role
  validateStrictDeclSyntax declKind declName typeStx valStx
  let data ← elabStrictDecl declKind declName typeStx valStx
  commitByRole declName role data

  let policy := defaultPolicySnapshot
  let region := regionOfDecl policy declName
  let hard ← liftCoreM <| collectHardEvidence policy declName
  let shape := analyzeProofShape data.typeExpr data.valueExpr
  let soft := lowerShapeToSoftEvidence role shape
  let (baseDecision, baseReasons) := evaluateAdmission policy hard soft
  let adjustedDecision := adjustDecisionForRegion region baseDecision
  let extraReasons := extraBlockingReasons declName role region shape
  let reasons := baseReasons ++ extraReasons
  let decision :=
    if extraReasons.isEmpty then adjustedDecision else .blocked
  let telemetry : TelemetryRow :=
    { name := declName
      declKind := declKind
      role := role
      region := region.asString
      decision := decision
      blockers := blockerCodes reasons
      hard := hard
      soft := soft
      reasons := reasons
      proofHead := shape.proofHead
      statementShape := shape.statementShape
      thinSurface? := shape.thinSurface?
    }
  let telemetryJson := (toJson telemetry).compress
  match decision with
  | .blocked =>
      throwError "[INADMISSIBLE] {declName}\n[strict-admission-json] {telemetryJson}"
  | .needsReview =>
      logWarning m!"[NEEDS_REVIEW] {declName}\n[strict-admission-json] {telemetryJson}"
  | .notPromotable =>
      logWarning m!"[NOT_PROMOTABLE] {declName}\n[strict-admission-json] {telemetryJson}"
  | .admitted =>
      logInfo m!"[ADMITTED] {declName}\n[strict-admission-json] {telemetryJson}"

elab "strict_theorem " id:ident " : " type:term " := " val:term : command => do
  processStrictDecl id type.raw val.raw DeclRole.owner

elab "strict_def " id:ident " : " type:term " := " val:term : command => do
  processStrictDecl id type.raw val.raw DeclRole.constructor

elab "strict_bridge " id:ident " : " type:term " := " val:term : command => do
  processStrictDecl id type.raw val.raw DeclRole.bridge

end InfoGeometry.Meta.StrictSurface
