import InfoGeometry.Meta.EnvironmentDependencyBridge
import InfoGeometry.Meta.KernelContractAudit
import InfoGeometry.Meta.DeclarationDependencyBridgeTests

namespace InfoGeometry.MetaCompiler.PipelineTests

open Lean Meta Elab Command Term
open KernelContractAudit

theorem left_add_zero (value : Nat) : value + 0 = value := Nat.add_zero value

theorem right_add_zero (value : Nat) : 0 + value = value := by
  rw [Nat.add_comm]
  exact left_add_zero value

private def requests : TermElabM (Array Request) := do
  let leftType ← Term.elabType (← `(∀ value : Nat, value + 0 = value))
  let rightType ← Term.elabType (← `(∀ value : Nat, 0 + value = value))
  Term.synthesizeSyntheticMVarsNoPostponing
  let leftType ← instantiateMVars leftType
  let rightType ← instantiateMVars rightType
  return #[{ declaration := ``left_add_zero, expectedType := leftType },
    { declaration := ``right_add_zero, expectedType := rightType }]

private def expectRejected (code : String) (action : MetaM Unit) : MetaM Unit := do
  let message : Option String ←
    try
      action
      pure none
    catch error =>
      pure (some (← error.toMessageData.toString))
  match message with
  | none => throwError "expected rejection: {code}"
  | some text =>
      unless text.startsWith code do
        throwError "expected {code}, received {text}"

run_cmd liftTermElabM do
  let raw ← requests
  let some order := InfoGeometry.Causal.FiniteDependencyCompiler.compile
      (∅ : Finset (Fin 2)) [1, 0]
    | throwError "finite dependency compiler rejected the test chain"
  let contract ← order.toArray.mapM fun node => do
    match raw[node.val]? with
    | some request => pure request
    | none => throwError "compiled node has no reviewed specification"
  let snapshot ← capture contract
  let reports ← audit snapshot
  unless reports.size == 2 do
    throwError "expected both theorem audit reports"
  expectRejected "epistemic.admission_blocked" (discard <| requireAdmission snapshot)
  expectRejected "epistemic.invalid_schedule"
    (discard <| audit { snapshot with requests := contract.reverse })
  expectRejected "epistemic.duplicate_target"
    (discard <| audit { snapshot with requests := contract ++ contract })
  expectRejected "epistemic.incomplete_closure"
    (discard <| audit { snapshot with covered := snapshot.covered.erase ``left_add_zero })
  let mismatch ← capture #[{ declaration := ``left_add_zero, expectedType := mkConst ``False }]
  expectRejected "epistemic.statement_mismatch" (discard <| audit mismatch)
  let notProposition ← capture #[{ declaration := ``left_add_zero, expectedType := mkConst ``Nat }]
  expectRejected "epistemic.not_proposition" (discard <| audit notProposition)
  let openType ← mkFreshExprMVar (mkSort levelZero)
  let openContract ← capture #[{ declaration := ``left_add_zero, expectedType := openType }]
  expectRejected "epistemic.open_specification" (discard <| audit openContract)
  let empty ← capture #[]
  expectRejected "epistemic.empty_request" (discard <| audit empty)

run_cmd liftTermElabM do
  let snapshot ← capture (← requests)
  let some (.thmInfo info) := snapshot.environment.find? ``left_add_zero
    | throwError "test theorem missing from checked environment"
  let altered := ConstantInfo.thmInfo { info with type := mkConst ``False }
  let oldEnvironment := { snapshot.environment with
    constants := snapshot.environment.constants.insert ``left_add_zero altered }
  expectRejected "epistemic.stale_evidence"
    (discard <| audit { snapshot with environment := oldEnvironment })

#audit_epistemic_schedule [left_add_zero, right_add_zero] against
  [(∀ value : Nat, value + 0 = value), (∀ value : Nat, 0 + value = value)]

#print axioms EnvironmentBridge.compiled_environment_closed
#print axioms EnvironmentBridge.EnvironmentCorrespondence.prefix_closed
#print axioms DeclarationBridge.certified_compilation_preserves_named_dependencies

end InfoGeometry.MetaCompiler.PipelineTests
