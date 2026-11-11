/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.ExteriorKleinBoost
import InfoGeometry.Projective.ExteriorKleinIncidenceAction
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Declaration trust audit for the native exterior Klein operator action

Ownership is selected by imported module, including private and generated
constants. This audit checks declaration kinds and transitive axioms; the
separate source review checks mathematical scope.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owners : Array Name := #[
    `InfoGeometry.Projective.ExteriorKleinOperatorAction,
    `InfoGeometry.Projective.ExteriorKleinDeterminantCovariance,
    `InfoGeometry.Projective.ExteriorKleinOperatorExamples,
    `InfoGeometry.Projective.ExteriorKleinBoost,
    `InfoGeometry.Projective.ExteriorKleinIncidenceAction]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for owner in owners do
    unless modules.contains owner do
      throwError "EXTERIOR_KLEIN_AUDIT_FAILURE: missing owner {owner}"
  let mut count : Nat := 0
  let mut theoremCount : Nat := 0
  let mut counts : NameMap Nat := {}
  for (name, info) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let some owner := modules[idx.toNat]? |
      throwError "EXTERIOR_KLEIN_AUDIT_FAILURE: invalid module index for {name}"
    if !owners.contains owner then continue
    if let .axiomInfo _ := info then
      throwError "EXTERIOR_KLEIN_AUDIT_FAILURE: introduced axiom {name}"
    if info.isUnsafe || info.isPartial then
      throwError "EXTERIOR_KLEIN_AUDIT_FAILURE: unsafe or partial declaration {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "EXTERIOR_KLEIN_AUDIT_FAILURE: {name} depends on {ax}"
    count := count + 1
    counts := counts.insert owner ((counts.find? owner).getD 0 + 1)
    if let .thmInfo _ := info then theoremCount := theoremCount + 1
    logInfo m!"EXTERIOR_KLEIN_DECL: {owner}: {name}: {axioms}"
  for owner in owners do
    let n := (counts.find? owner).getD 0
    if n == 0 then throwError "EXTERIOR_KLEIN_AUDIT_FAILURE: empty owner {owner}"
    logInfo m!"EXTERIOR_KLEIN_OWNER: {owner}: {n}"
  logInfo m!"EXTERIOR_KLEIN_AUDIT_PASS: {count} declarations, {theoremCount} theorem declarations; only propext, Classical.choice, Quot.sound permitted"
