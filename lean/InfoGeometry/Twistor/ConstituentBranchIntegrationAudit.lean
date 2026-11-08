/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.ConstituentColumnEquivalence
import InfoGeometry.Twistor.ConstituentMomentumTransport
import InfoGeometry.Twistor.ConstituentLinearStabilizer
import InfoGeometry.Twistor.ConstituentPolynomialEmbedding
import InfoGeometry.Twistor.PerjesIncidencePairing
import InfoGeometry.Twistor.PerjesMomentOperator
import Lean.Elab.Command

/-! Exhaustive declaration ownership and transitive axiom audit for the
branch-reconciliation modules. This is not a semantic equivalence certificate.
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owners : Array Name := #[
    `InfoGeometry.Twistor.ConstituentColumnEquivalence,
    `InfoGeometry.Twistor.ConstituentMomentumTransport,
    `InfoGeometry.Twistor.ConstituentLinearStabilizer,
    `InfoGeometry.Twistor.ConstituentPolynomialEmbedding,
    `InfoGeometry.Twistor.PerjesIncidencePairing,
    `InfoGeometry.Twistor.PerjesMomentOperator,
    `InfoGeometry.Twistor.TwistorKinematicTensor,
    `InfoGeometry.Twistor.TwistorConstituentCCR,
    `InfoGeometry.Twistor.TwistorInternalSymmetry]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut counts : NameMap Nat := {}
  let mut theoremCounts : NameMap Nat := {}
  for owner in owners do
    unless modules.contains owner do
      throwError "Missing reconciliation owner: {owner}"
  for (name, info) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let some owner := modules[idx.toNat]? | throwError "Invalid owner index: {name}"
    if !owners.contains owner then continue
    if let .axiomInfo _ := info then
      throwError "Authored axiom: {name}"
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial declaration: {name}"
    for axiomName in (← Lean.collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "Disallowed transitive axiom {axiomName} in {name}"
    counts := counts.insert owner ((counts.find? owner).getD 0 + 1)
    if let .thmInfo _ := info then
      theoremCounts := theoremCounts.insert owner ((theoremCounts.find? owner).getD 0 + 1)
  for owner in owners do
    let count := (counts.find? owner).getD 0
    let theorems := (theoremCounts.find? owner).getD 0
    if count == 0 || theorems == 0 then
      throwError "Owner has no audited declarations or theorems: {owner}"
    logInfo m!"AUDIT_OWNER: {owner}; declarations={count}; theorems={theorems}"
  logInfo "AUDIT_SUCCESS: all listed reconciliation owners passed the transitive axiom audit"
