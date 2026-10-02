import InfoGeometry.Meta.HiveEpistemicBridge

namespace InfoGeometry.MetaCompiler.ArangoDependencyExport

open Lean Meta
open KernelContractAudit HiveBridge
open InfoGeometry.Meta.StrictSurface

def declarationKey (name : Name) : String :=
  s!"d_{(hash name).toNat}"

def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def dependencyKind : DAG.EdgeKind → String
  | .type => "type"
  | .value => "value"

private def payload (snapshot : Snapshot) (reports : Array TelemetryRow) : MetaM Json := do
  let names := snapshot.covered.toList.toArray.qsort Name.lt
  let mut keys : Std.HashMap String Name := {}
  let mut vertices : Array Json := #[]
  let mut edges : Array Json := #[]
  for name in names do
    let key := declarationKey name
    if let some previous := keys[key]? then
      unless previous == name do
        throwError "arango.declaration_key_collision: {previous}, {name}"
    keys := keys.insert key name
    let some info := snapshot.environment.find? name
      | throwError "arango.missing_declaration: {name}"
    vertices := vertices.push <| Json.mkObj
      [("_key", toJson key),
       ("declaration", toJson name.toString),
       ("kind", toJson (declarationKind info)),
       ("type", toJson (← ppExpr info.type).pretty),
       ("status", toJson "kernel_environment_declaration")]
    for (prerequisite, kind) in DAG.edgesFromConstantInfo info do
      unless snapshot.covered.contains prerequisite do
        throwError "arango.incomplete_dependency_closure: {name} requires {prerequisite}"
      let targetKey := declarationKey prerequisite
      let role := dependencyKind kind
      edges := edges.push <| Json.mkObj
        [("_key", toJson s!"{key}_{role}_{targetKey}"),
         ("_from", toJson s!"ProofNodes/{key}"),
         ("_to", toJson s!"ProofNodes/{targetKey}"),
         ("relation", toJson "depends_on"),
         ("role", toJson role)]
  return Json.mkObj
    [("schema", toJson "info_geometry.arango_dependency_export.v1"),
     ("scope", toJson "current_kernel_environment"),
     ("vertex_collection", toJson "ProofNodes"),
     ("edge_direction", toJson "dependent_to_prerequisite"),
     ("vertex_order", toJson "declaration_name_not_topological"),
     ("key_scheme", toJson "lean_name_hash_collision_checked_within_payload"),
     ("external_dependencies_included", toJson true),
     ("promotion_allowed", toJson false),
     ("scheduled_targets", toJson (snapshot.requests.map fun request =>
       request.declaration.toString)),
     ("admission_reports", toJson reports),
     ("vertices", toJson vertices),
     ("edges", toJson edges)]

variable {Node : Type} [PartialOrder Node] [DecidableEq Node]
  [Fintype Node] [DecidableLT Node]

def exportPlan {pending : List Node} {request : Node → Request}
    (plan : PreparedPlan pending request) : MetaM Json :=
  withAdmission plan fun reports => payload plan.snapshot reports

def emitPlan {pending : List Node} {request : Node → Request}
    (plan : PreparedPlan pending request) : MetaM Unit := do
  let graph ← exportPlan plan
  logInfo m!"[arango-dependency-export] {graph.compress}"

end InfoGeometry.MetaCompiler.ArangoDependencyExport
