/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.BinaryCarryStar
import InfoGeometry.Canonical.RealCarryMatrix
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Imported-environment trust audit of the real carry and quartic rotor owners.

This includes private and compiler-generated declarations from the four named
owners. It rejects introduced axioms, unsafe/partial declarations, and every
axiom dependency outside the three explicitly permitted Lean foundations.
It does not certify unrelated repository modules or a physical interpretation.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owners : Array Name := #[
    `InfoGeometry.OperatorAlgebra.PeirceSpine.BinaryCarry,
    `InfoGeometry.Algebra.QuarticRotor,
    `InfoGeometry.OperatorAlgebra.PeirceSpine.BinaryCarryStar,
    `InfoGeometry.Canonical.RealCarryMatrix]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for owner in owners do
    unless moduleNames.contains owner do
      throwError "AUDIT_FAILURE: missing imported owner {owner}"
  let mut count : Nat := 0
  let mut theorems : Nat := 0
  let mut counts : NameMap Nat := {}
  let mut used : Array Name := #[]
  for (name, info) in env.constants do
    let some moduleIdx := env.getModuleIdxFor? name | continue
    let some owner := moduleNames[moduleIdx.toNat]? | continue
    if !owners.contains owner then continue
    if let .axiomInfo _ := info then
      throwError "AUDIT_FAILURE: introduced axiom {name}"
    if info.isUnsafe || info.isPartial then
      throwError "AUDIT_FAILURE: unsafe or partial declaration {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "AUDIT_FAILURE: {name} depends on {ax}"
      if !used.contains ax then used := used.push ax
    count := count + 1
    counts := counts.insert owner ((counts.find? owner).getD 0 + 1)
    if let .thmInfo _ := info then theorems := theorems + 1
  for owner in owners do
    let n := (counts.find? owner).getD 0
    if n == 0 then throwError "AUDIT_FAILURE: empty audited owner {owner}"
    logInfo m!"AUDIT_OWNER: {owner}: {n}"
  logInfo m!"AUDIT_AXIOMS: {used.qsort Name.lt}"
  logInfo m!"AUDIT_DECLARATIONS: {count}"
  logInfo m!"AUDIT_THEOREMS_INCLUDING_GENERATED: {theorems}"
  logInfo m!"AUDIT_SUCCESS: {owners.size} owners"
