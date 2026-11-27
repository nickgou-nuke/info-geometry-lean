/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import «InfoGeometry».«Modular».«RieffelVanDaeleBoundedTomita»
import «InfoGeometry».«Canonical».«FilteredGNSTomitaFriedrichsResolvent»
import «InfoGeometry».«Modular».«TwistedCrossedProductAlgebra»
import «InfoGeometry».«Modular».«PowersModularSpectrum»
import «InfoGeometry».«Modular».«ComplexRelativeModularRN»
import «InfoGeometry».«Analysis».«LpSpectralMultiplicationModel»
import «InfoGeometry».«Modular».«TomitaRegularCommutantAndKMSBridge»
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Axiom Audit for the Tomita Frontiers Roadmap (`TT-F1`–`TT-F5`)

Verifies that every declaration in the 7 new `TT-F1`–`TT-F5` modules
(`RieffelVanDaeleBoundedTomita`, `FilteredGNSTomitaFriedrichsResolvent`,
`TwistedCrossedProductAlgebra`, `PowersModularSpectrum`,
`ComplexRelativeModularRN`, `LpSpectralMultiplicationModel`,
`TomitaRegularCommutantAndKMSBridge`) has zero `unsafe` / `partial`
definitions, non-zero audited declaration counts, and depends solely on the
standard foundational axioms `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `«InfoGeometry».«Modular».«RieffelVanDaeleBoundedTomita»,
    `«InfoGeometry».«Canonical».«FilteredGNSTomitaFriedrichsResolvent»,
    `«InfoGeometry».«Modular».«TwistedCrossedProductAlgebra»,
    `«InfoGeometry».«Modular».«PowersModularSpectrum»,
    `«InfoGeometry».«Modular».«ComplexRelativeModularRN»,
    `«InfoGeometry».«Analysis».«LpSpectralMultiplicationModel»,
    `«InfoGeometry».«Modular».«TomitaRegularCommutantAndKMSBridge»]
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
