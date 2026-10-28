/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import «InfoGeometry».«OperatorAlgebra».«DerivationCurvatureVariation»
import «InfoGeometry».«OperatorAlgebra».«DerivationCyclicAction»
import «InfoGeometry».«OperatorAlgebra».«DerivationCyclicActionDerivative»
import «InfoGeometry».«OperatorAlgebra».«DerivationGaugeTransport»
import «InfoGeometry».«OperatorAlgebra».«DerivationMatrixEnergy»
import «InfoGeometry».«OperatorAlgebra».«DerivationMatrixGeometry»
import «InfoGeometry».«Algebra».«NonAssocDerivation»
import «InfoGeometry».«Algebra».«DerivationLieLane»
import «InfoGeometry».«Algebra».«DerivationLieLaneRepresentation»
import «InfoGeometry».«OperatorAlgebra».«DerivationDifferentialForms»
import «InfoGeometry».«Geometry».«AssociativeGaugeConnection»
import «InfoGeometry».«TKK».«GenericRepresentationBridge»
import «YangMillsMatrixGeometryTests»
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `«InfoGeometry».«OperatorAlgebra».«DerivationCurvatureVariation»,
    `«InfoGeometry».«OperatorAlgebra».«DerivationCyclicAction»,
    `«InfoGeometry».«OperatorAlgebra».«DerivationCyclicActionDerivative»,
    `«InfoGeometry».«OperatorAlgebra».«DerivationGaugeTransport»,
    `«InfoGeometry».«OperatorAlgebra».«DerivationMatrixEnergy»,
    `«InfoGeometry».«OperatorAlgebra».«DerivationMatrixGeometry»,
    `«InfoGeometry».«Algebra».«NonAssocDerivation»,
    `«InfoGeometry».«Algebra».«DerivationLieLane»,
    `«InfoGeometry».«Algebra».«DerivationLieLaneRepresentation»,
    `«InfoGeometry».«OperatorAlgebra».«DerivationDifferentialForms»,
    `«InfoGeometry».«Geometry».«AssociativeGaugeConnection»,
    `«InfoGeometry».«TKK».«GenericRepresentationBridge»,
    `«YangMillsMatrixGeometryTests»]
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
