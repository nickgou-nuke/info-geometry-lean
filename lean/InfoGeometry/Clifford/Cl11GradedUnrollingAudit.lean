/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import «InfoGeometry».«Clifford».«SplitCliffordMatrixEquiv»
import «InfoGeometry».«Clifford».«Cl11GradedUnrolling»
import «InfoGeometry».«Clifford».«Cl11RecursiveUnrolling»
import «InfoGeometry».«Clifford».«Cl11HomogeneousChains»
import «InfoGeometry».«Algebra».«MatrixRankFactorization»
import «InfoGeometry».«Tensor».«ExactTensorTrain»
import «InfoGeometry».«Tensor».«RankMinimalTensorTrain»
import «InfoGeometry».«Tensor».«TensorTrainMatricization»
import «InfoGeometry».«Clifford».«Cl11PureTensorObstruction»
import «InfoGeometry».«Clifford».«Cl11TensorTrainSynthesis»
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let targets : Array Name := #[`«InfoGeometry».«Clifford».«SplitCliffordMatrixEquiv», `«InfoGeometry».«Clifford».«Cl11GradedUnrolling», `«InfoGeometry».«Clifford».«Cl11RecursiveUnrolling», `«InfoGeometry».«Clifford».«Cl11HomogeneousChains», `«InfoGeometry».«Algebra».«MatrixRankFactorization», `«InfoGeometry».«Tensor».«ExactTensorTrain», `«InfoGeometry».«Tensor».«RankMinimalTensorTrain», `«InfoGeometry».«Tensor».«TensorTrainMatricization», `«InfoGeometry».«Clifford».«Cl11PureTensorObstruction», `«InfoGeometry».«Clifford».«Cl11TensorTrainSynthesis»]
  let commandOnly : Array Name := #[]
  for target in targets do
    unless moduleNames.contains target do
      throwError "Selected module not imported: {target}"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  let mut ownerCounts : NameMap Nat := {}
  let mut allAxioms : Array Name := #[]
  for (name, info) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := moduleNames[idx.toNat]!
    if !targets.contains owner then continue
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial declaration in reviewed module: {name}"
    -- Public API handles imported axiom metadata and private-body lookup.
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Disallowed axiom {ax} in {name}"
      if !allAxioms.contains ax then
        allAxioms := allAxioms.push ax
    count := count + 1
    ownerCounts := ownerCounts.insert owner ((ownerCounts.find? owner).getD 0 + 1)
    logInfo m!"AUDIT_DECL: {owner}: {name}"
  for target in targets do
    let moduleCount := (ownerCounts.find? target).getD 0
    logInfo m!"AUDIT_MODULE_COUNT: {target}: {moduleCount}"
    if commandOnly.contains target then
      if moduleCount != 0 then
        throwError "Command-only module owns declarations: {target}"
      logInfo m!"AUDIT_COMMAND_MODULE: {target}"
    else
      if moduleCount == 0 then
        throwError "No declarations audited in reviewed module: {target}"
      logInfo m!"AUDIT_MODULE: {target}"
  if count == 0 then throwError "No declarations audited"
  logInfo m!"AUDIT_AXIOMS: {allAxioms.qsort Name.lt}"
  logInfo m!"AUDIT_COUNT: {count}"
