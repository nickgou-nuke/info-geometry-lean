import InfoGeometry.Meta.ArangoDependencyExport
import InfoGeometry.Meta.EpistemicPipelineTests

namespace InfoGeometry.MetaCompiler.ArangoDependencyExportTests

open Lean Meta Elab Command Term
open KernelContractAudit HiveBridge ArangoDependencyExport

run_cmd do
  if declarationKey `InfoGeometry.a_b == declarationKey `InfoGeometry.a.b then
    throwError "distinct declaration names produced colliding keys"

example : dependencyKind DAG.EdgeKind.type = "type" := rfl

example : dependencyKind DAG.EdgeKind.value = "value" := rfl

run_cmd liftTermElabM do
  let expectedType ← Term.elabType (← `(∀ value : Nat, value + 0 = value))
  Term.synthesizeSyntheticMVarsNoPostponing
  let expectedType ← instantiateMVars expectedType
  let request : Fin 1 → Request := fun _ =>
    { declaration := ``PipelineTests.left_add_zero, expectedType }
  let plan ← prepare [0] request
  let rejection : Option String ←
    try
      discard <| exportPlan plan
      pure none
    catch error => pure (some (← error.toMessageData.toString))
  match rejection with
  | none => throwError "QMS review unexpectedly produced an Arango payload"
  | some message =>
      unless message.startsWith "epistemic.admission_blocked" do
        throwError "unexpected export rejection: {message}"

end InfoGeometry.MetaCompiler.ArangoDependencyExportTests
