/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorContentNetwork
import Lean.Util.CollectAxioms

/-! Transitive axiom audit of all public and generated declarations in the package. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let sentinels : Array Name := #[
    ``InfoGeometry.Canonical.OperatorContentNetwork.evaluation_locality,
    ``InfoGeometry.Canonical.OperatorContentNetwork.execution_adjacent_swap_defect,
    ``InfoGeometry.Canonical.OperatorContentNetwork.Dependency.dependencyOrder,
    ``InfoGeometry.Canonical.OperatorContentNetwork.PeerStore.merge_comm_iff,
    ``InfoGeometry.Canonical.OperatorContentNetwork.PeerStore.Addressing.compatible_iff_address_injOn,
    ``InfoGeometry.Canonical.OperatorContentNetwork.RankedDAG.resolve_satisfies,
    ``InfoGeometry.Canonical.OperatorContentNetwork.RankedDAG.exists_store_with_noncommuting_results,
    ``InfoGeometry.Canonical.OperatorContentNetwork.PeerStore.resolve_merge_converges,
    ``InfoGeometry.Canonical.OperatorContentNetwork.pathDefect_gauge_ne_zero_iff,
    ``InfoGeometry.Canonical.OperatorContentNetwork.causalBlock_evaluation_surjective,
    ``InfoGeometry.Canonical.OperatorContentNetwork.compress_mul_defect]
  let names := env.constants.fold (init := #[]) fun acc name info =>
    if name.toString.startsWith "InfoGeometry.Canonical.OperatorContentNetwork." ||
        name.toString.startsWith "_private.InfoGeometry.Canonical.OperatorContentNetwork." then
      acc.push (name, info)
    else acc
  for sentinel in sentinels do
    unless names.any (fun entry => entry.1 == sentinel) do
      throwError "Missing audit sentinel: {sentinel}"
  let mut theoremCount : Nat := 0
  for (name, info) in names.qsort (fun a b => Name.quickLt a.1 b.1) do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unapproved axiom dependency: {name}: {axiomName}"
    match info with
    | .thmInfo _ => theoremCount := theoremCount + 1
    | _ => pure ()
    logInfo m!"{name}: {axioms}"
  if theoremCount == 0 then
    throwError "OperatorContentNetwork audit selected no theorem constants"
  logInfo m!"PASS: {names.size} declarations, {theoremCount} theorem constants; only standard Lean axioms."
