import InfoGeometry.Meta.HiveEpistemicBridge
import InfoGeometry.Meta.EpistemicPipelineTests

namespace InfoGeometry.MetaCompiler.HiveBridgeTests

open Lean Meta Elab Command Term
open KernelContractAudit HiveBridge

private def expectRejected (code : String) (action : MetaM Unit) : MetaM Unit := do
  let message : Option String ←
    try
      action
      pure none
    catch error => pure (some (← error.toMessageData.toString))
  match message with
  | none => throwError "expected rejection: {code}"
  | some text => unless text.startsWith code do
      throwError "expected {code}, received {text}"

run_cmd liftTermElabM do
  let leftType ← Term.elabType (← `(∀ value : Nat, value + 0 = value))
  let rightType ← Term.elabType (← `(∀ value : Nat, 0 + value = value))
  Term.synthesizeSyntheticMVarsNoPostponing
  let leftType ← instantiateMVars leftType
  let rightType ← instantiateMVars rightType
  let left : Request :=
    { declaration := ``PipelineTests.left_add_zero, expectedType := leftType }
  let right : Request :=
    { declaration := ``PipelineTests.right_add_zero, expectedType := rightType }
  let request : Fin 2 → Request := fun node => if node = 0 then left else right
  let plan ← prepare [1, 0] request
  unless plan.schedule == [0, 1] do
    throwError "existing compiler did not reorder the chain"
  let reports ← audit plan.snapshot
  unless reports.size == 2 do
    throwError "compiled requests lost a declaration"
  expectRejected "epistemic.admission_blocked" <|
    withAdmission plan fun _ => throwError "dispatch must not run on QMS review"
  expectRejected "epistemic.admission_blocked" (emitAdmission plan)
  expectRejected "hive.epistemic.unschedulable" (discard <| prepare [1] request)
  expectRejected "hive.epistemic.unschedulable" (discard <| prepare [0, 0] request)
  let reversed ← prepare [0, 1] (fun node : Fin 2 => if node = 0 then right else left)
  expectRejected "epistemic.invalid_schedule" (emitAdmission reversed)
  let aliases ← prepare [0, 1] (fun _ : Fin 2 => left)
  expectRejected "epistemic.duplicate_target" (emitAdmission aliases)

#print axioms HiveBridge.PreparedPlan.valid
#print axioms HiveBridge.PreparedPlan.permutation

end InfoGeometry.MetaCompiler.HiveBridgeTests
