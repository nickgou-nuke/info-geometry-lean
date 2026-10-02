import InfoGeometry.Causal.FiniteDependencyCompiler
import InfoGeometry.Meta.KernelContractAudit

namespace InfoGeometry.MetaCompiler.HiveBridge

open Lean Meta
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Meta.StrictSurface
open KernelContractAudit

variable {Node : Type} [PartialOrder Node] [DecidableEq Node]
  [Fintype Node] [DecidableLT Node]

structure PreparedPlan (pending : List Node) (request : Node → Request) where
  schedule : List Node
  computed : compile ∅ pending = some schedule
  snapshot : Snapshot
  requests_match : snapshot.requests = (schedule.map request).toArray

theorem PreparedPlan.valid {pending : List Node} {request : Node → Request}
    (plan : PreparedPlan pending request) : ValidSchedule ∅ plan.schedule :=
  (compile_sound plan.computed).1

theorem PreparedPlan.permutation {pending : List Node} {request : Node → Request}
    (plan : PreparedPlan pending request) : plan.schedule.Perm pending :=
  (compile_sound plan.computed).2

def prepare (pending : List Node) (request : Node → Request) :
    CoreM (PreparedPlan pending request) := do
  match computed : compile ∅ pending with
  | none => throwError "hive.epistemic.unschedulable"
  | some schedule =>
      let snapshot ← capture (schedule.map request).toArray
      return { schedule, computed,
        snapshot := { snapshot with requests := (schedule.map request).toArray },
        requests_match := rfl }

def withAdmission {Result : Type} {pending : List Node} {request : Node → Request}
    (plan : PreparedPlan pending request)
    (dispatch : Array TelemetryRow → MetaM Result) : MetaM Result := do
  let reports ← requireAdmission plan.snapshot
  dispatch reports

def emitAdmission {pending : List Node} {request : Node → Request}
    (plan : PreparedPlan pending request) : MetaM Unit :=
  withAdmission plan fun reports => do
    let receipt := Json.mkObj
      [("schema", toJson "info_geometry.hive_epistemic_admission.v1"),
       ("scheduler", toJson "finite_dependency_compiler"),
       ("scope", toJson "current_kernel_environment"),
       ("declarations", toJson (plan.snapshot.requests.map fun item =>
         item.declaration.toString)),
       ("reports", toJson reports)]
    logInfo m!"[hive-epistemic-admission] {receipt.compress}"

end InfoGeometry.MetaCompiler.HiveBridge
