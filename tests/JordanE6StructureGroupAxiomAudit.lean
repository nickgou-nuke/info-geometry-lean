/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import «InfoGeometry».«Algebra».«JordanStructureGroup»
import «InfoGeometry».«Algebra».«H3ZornStructureGroup»
import «InfoGeometry».«Algebra».«H3ZornF4DimensionClosure»
import «InfoGeometry».«Algebra».«H3ZornReducedStructureLieAlgebra»
import «InfoGeometry».«Algebra».«H3ZornCubicOperatorGeometry»
import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootCore
import «JordanE6StructureGroupTests»
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Native declaration axiom audit for the Jordan algebra / E₆(₆) structure group
and 78D reduced structure Lie algebra tower.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `«InfoGeometry».«Algebra».«JordanStructureGroup»,
    `«InfoGeometry».«Algebra».«H3ZornStructureGroup»,
    `«InfoGeometry».«Algebra».«H3ZornF4DimensionClosure»,
    `«InfoGeometry».«Algebra».«H3ZornReducedStructureLieAlgebra»,
    `«InfoGeometry».«Algebra».«H3ZornCubicOperatorGeometry»,
    `InfoGeometry.Exceptional.CFSGPort.ChevalleyRootCore,
    `«JordanE6StructureGroupTests»]
  let commandOnly : Array Name := #[]
  for target in targets do
    unless env.header.moduleNames.contains target do
      throwError "Selected module not imported: {target}"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  let mut ownerCounts : NameMap Nat := {}
  let mut allAxioms : Array Name := #[]
  for (name, info) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx.toNat]!
    if !targets.contains owner then continue
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial declaration in reviewed module: {name}"
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
