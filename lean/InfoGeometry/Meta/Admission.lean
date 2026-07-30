import Lean
import DAG.JsonInstances

open Lean

namespace InfoGeometry.Meta

/-- Repository-level admission verdict for a kernel-accepted declaration. -/
inductive AdmissionDecision where
  | admitted
  | blocked
  | needsReview
  | notPromotable
  deriving Repr, Inhabited, DecidableEq, BEq

/-- Machine-readable reason attached to an admission verdict. -/
structure AdmissionReason where
  code : String
  severity : String
  message : String
  declName : Name
  deriving Repr, Inhabited

/-- Crisp hard blockers collected before any soft heuristics are considered. -/
structure HardEvidence where
  hasSorryAx : Bool
  forbiddenAxioms : List Name
  unsafeLeakage : Bool
  missingRequiredAttrs : List Name
  repDepthViolation : Bool
  forbiddenRegionKind : Bool
  deriving Repr, Inhabited

/-- Non-blocking architectural or linter hints attached to a declaration. -/
structure SoftEvidence where
  vacuityHints : List String
  graphRoleHints : List String
  plannerHints : List String
  deriving Repr, Inhabited

/-- Snapshot of the repository-level region policy. -/
structure PolicySnapshot where
  protectedNamespaces : List Name
  bridgeNamespaces : List Name
  workbenchNamespaces : List Name
  requiredAttrsByRegion : List (String × List Name)
  deriving Repr, Inhabited

/-- Stable version label for machine-readable admission reports. -/
def admissionPolicyVersion : String := "admission-v1"

/-- Full report emitted by strict admission audits. -/
structure AdmissionReport where
  declName : Name
  region : String
  decision : AdmissionDecision
  hard : HardEvidence
  soft : SoftEvidence
  reasons : Array AdmissionReason
  policyVersion : String
  deriving Repr, Inhabited

def AdmissionDecision.asString : AdmissionDecision → String
  | .admitted => "admitted"
  | .blocked => "blocked"
  | .needsReview => "needs_review"
  | .notPromotable => "not_promotable"

instance : ToJson AdmissionDecision where
  toJson d := Json.str d.asString

instance : ToJson AdmissionReason where
  toJson r :=
    Json.mkObj
      [ ("code", toJson r.code)
      , ("severity", toJson r.severity)
      , ("message", toJson r.message)
      , ("declName", toJson r.declName)
      ]

instance : ToJson HardEvidence where
  toJson h :=
    Json.mkObj
      [ ("hasSorryAx", toJson h.hasSorryAx)
      , ("forbiddenAxioms", toJson h.forbiddenAxioms)
      , ("unsafeLeakage", toJson h.unsafeLeakage)
      , ("missingRequiredAttrs", toJson h.missingRequiredAttrs)
      , ("repDepthViolation", toJson h.repDepthViolation)
      , ("forbiddenRegionKind", toJson h.forbiddenRegionKind)
      ]

instance : ToJson SoftEvidence where
  toJson s :=
    Json.mkObj
      [ ("vacuityHints", toJson s.vacuityHints)
      , ("graphRoleHints", toJson s.graphRoleHints)
      , ("plannerHints", toJson s.plannerHints)
      ]

instance : ToJson PolicySnapshot where
  toJson p :=
    let required :=
      p.requiredAttrsByRegion.map fun (region, attrs) =>
        Json.mkObj
          [ ("region", toJson region)
          , ("attrs", toJson attrs)
          ]
    Json.mkObj
      [ ("protectedNamespaces", toJson p.protectedNamespaces)
      , ("bridgeNamespaces", toJson p.bridgeNamespaces)
      , ("workbenchNamespaces", toJson p.workbenchNamespaces)
      , ("requiredAttrsByRegion", Json.arr required.toArray)
      ]

instance : ToJson AdmissionReport where
  toJson r :=
    Json.mkObj
      [ ("declName", toJson r.declName)
      , ("region", toJson r.region)
      , ("decision", toJson r.decision)
      , ("hard", toJson r.hard)
      , ("soft", toJson r.soft)
      , ("reasons", toJson r.reasons.toList)
      , ("policyVersion", toJson r.policyVersion)
      ]

/-- Construct a machine-readable admission reason. -/
def mkAdmissionReason (declName : Name) (code severity message : String) : AdmissionReason :=
  { code := code, severity := severity, message := message, declName := declName }

/-- Evaluate repository admission from hard evidence first, then soft evidence. -/
def evaluateAdmission
    (policy : PolicySnapshot)
    (hard : HardEvidence)
    (soft : SoftEvidence) : AdmissionDecision × Array AdmissionReason := Id.run do
  let mut reasons : Array AdmissionReason := #[]
  let syntheticDecl := Name.mkSimple "_admission"

  if hard.hasSorryAx then
    reasons := reasons.push <|
      mkAdmissionReason syntheticDecl "trust.sorry" "error"
        "declaration depends on `sorryAx`."
  if !hard.forbiddenAxioms.isEmpty then
    reasons := reasons.push <|
      mkAdmissionReason syntheticDecl "trust.forbidden_axioms" "error"
        s!"declaration depends on forbidden axioms: {String.intercalate ", " (hard.forbiddenAxioms.map toString)}."
  if hard.unsafeLeakage then
    reasons := reasons.push <|
      mkAdmissionReason syntheticDecl "trust.unsafe_leakage" "error"
        "declaration depends on an unsafe declaration."
  if !hard.missingRequiredAttrs.isEmpty then
    let wanted := String.intercalate ", " (hard.missingRequiredAttrs.map toString)
    reasons := reasons.push <|
      mkAdmissionReason syntheticDecl "policy.missing_required_attrs" "error"
        s!"declaration is missing required admission metadata: {wanted}."
  if hard.repDepthViolation then
    reasons := reasons.push <|
      mkAdmissionReason syntheticDecl "architecture.rep_depth" "error"
        "declaration violates the representation-depth adjacency policy."
  if hard.forbiddenRegionKind then
    reasons := reasons.push <|
      mkAdmissionReason syntheticDecl "policy.forbidden_region_kind" "error"
        "declaration kind is forbidden in its current protected region."

  if !reasons.isEmpty then
    return (.blocked, reasons)

  let mut softReasons : Array AdmissionReason := #[]
  if !soft.vacuityHints.isEmpty then
    softReasons := softReasons.push <|
      mkAdmissionReason syntheticDecl "soft.vacuity" "warning"
        s!"declaration has vacuity hints: {String.intercalate " | " soft.vacuityHints}."
  if !soft.graphRoleHints.isEmpty then
    softReasons := softReasons.push <|
      mkAdmissionReason syntheticDecl "soft.graph_role" "warning"
        s!"declaration has graph-role hints: {String.intercalate " | " soft.graphRoleHints}."
  if !soft.plannerHints.isEmpty then
    softReasons := softReasons.push <|
      mkAdmissionReason syntheticDecl "soft.planner" "warning"
        s!"declaration has planner hints: {String.intercalate " | " soft.plannerHints}."

  if !softReasons.isEmpty then
    return (.needsReview, softReasons)

  let _ := policy
  (.admitted, #[])

end InfoGeometry.Meta
