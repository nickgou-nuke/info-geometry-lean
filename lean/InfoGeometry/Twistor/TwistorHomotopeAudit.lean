/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.OrderedHomotope
import InfoGeometry.Algebra.TwoModeCountRecurrence
import InfoGeometry.Twistor.ConstituentCayleyGram
import InfoGeometry.Twistor.ConstituentInvariantIndependence
import InfoGeometry.Twistor.MomentHomotopeWitness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Declaration trust audit for the ordered homotopes and native twistor invariants

Ownership is selected by imported module, including private and generated
constants. This audit checks declaration kinds and transitive axioms; the
separate source review checks mathematical scope.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owners : Array Name := #[
    `InfoGeometry.OperatorAlgebra.OrderedHomotope,
    `InfoGeometry.Algebra.TwoModeCountRecurrence,
    `InfoGeometry.Twistor.ConstituentWittGram,
    `InfoGeometry.Twistor.ConstituentCayleyGram,
    `InfoGeometry.Twistor.ConstituentInvariantIndependence,
    `InfoGeometry.Twistor.MomentHomotopeWitness]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for owner in owners do
    unless modules.contains owner do
      throwError "TWISTOR_HOMOTOPE_AUDIT_FAILURE: missing owner {owner}"
  let mut count : Nat := 0
  let mut theoremCount : Nat := 0
  let mut counts : NameMap Nat := {}
  for (name, info) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let some owner := modules[idx.toNat]? |
      throwError "TWISTOR_HOMOTOPE_AUDIT_FAILURE: invalid module index for {name}"
    if !owners.contains owner then continue
    if let .axiomInfo _ := info then
      throwError "TWISTOR_HOMOTOPE_AUDIT_FAILURE: introduced axiom {name}"
    if info.isUnsafe || info.isPartial then
      throwError "TWISTOR_HOMOTOPE_AUDIT_FAILURE: unsafe or partial declaration {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "TWISTOR_HOMOTOPE_AUDIT_FAILURE: {name} depends on {ax}"
    count := count + 1
    counts := counts.insert owner ((counts.find? owner).getD 0 + 1)
    if let .thmInfo _ := info then theoremCount := theoremCount + 1
    logInfo m!"TWISTOR_HOMOTOPE_DECL: {owner}: {name}: {axioms}"
  for owner in owners do
    let n := (counts.find? owner).getD 0
    if n == 0 then throwError "TWISTOR_HOMOTOPE_AUDIT_FAILURE: empty owner {owner}"
    logInfo m!"TWISTOR_HOMOTOPE_OWNER: {owner}: {n}"
  logInfo m!"TWISTOR_HOMOTOPE_AUDIT_PASS: {count} declarations, {theoremCount} theorem declarations; only propext, Classical.choice, Quot.sound permitted"
