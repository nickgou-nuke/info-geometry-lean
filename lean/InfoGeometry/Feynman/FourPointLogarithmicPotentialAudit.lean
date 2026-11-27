/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Feynman.FourPointLogarithmicPotential
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Trust audit and regular witnesses for the four-point logarithmic calculation

Inspect every declaration owned by the two new mathematical modules, including
generated declarations, and reject extra axioms or unsafe/partial definitions.
Concrete witnesses below exercise the regular domain and the orientation sign.
This audit does not assert a cohomology comparison or a Feynman representation.
-/

open Lean Elab Command

namespace InfoGeometry.Feynman.FourPointLogarithmicPotentialAudit

open FourPointLogarithmicPotential
open InfoGeometry.Projective.ThreePointLogarithmicForms

example : ∃! z : ℝ, z ≠ 0 ∧ z ≠ 1 ∧ scatteringCoefficient 2 3 z = 0 :=
  existsUnique_stationary 2 3 (by norm_num) (by norm_num) (by norm_num)

example : HasDerivAt (realLogPotential 2 3) 0 (2 / 5 : ℝ) := by
  convert realLogPotential_hasDerivAt_stationary 2 3
    (by norm_num) (by norm_num) (by norm_num) using 1; norm_num [stationary]

example : HasDerivAt (complexLogPotential 2 3) 0 (2 / 5 : ℂ) := by
  have hz : (2 / 5 : ℂ) ∈ Complex.slitPlane := by
    norm_num [Complex.mem_slitPlane_iff]
  have h1z : 1 - (2 / 5 : ℂ) ∈ Complex.slitPlane := by
    norm_num [Complex.mem_slitPlane_iff]
  convert complexLogPotential_hasDerivAt 2 3 (2 / 5) hz h1z using 1;
    norm_num [scatteringCoefficient]

example : punctureParkeTaylor (2 / 5 : ℚ) = 25 / 6 := by
  norm_num [punctureParkeTaylor]

example : hessianCoefficient (2 : ℚ) 3 (2 / 5) = -(125 / 6) := by
  norm_num [hessianCoefficient]

example : algebraicLocalization (2 : ℚ) 3 (2 / 5) = 5 / 6 := by
  norm_num [algebraicLocalization, punctureParkeTaylor, hessianCoefficient]

-- The Arnold cancellation has three nonzero summands at this configuration.
example :
    wedgeEval (edgeForm (![0, 1, 2] : Fin 3 → ℚ) 0 1)
      (edgeForm ![0, 1, 2] 1 2) ![1, 0, 0] ![0, 1, 0] = 1 := by
  norm_num [wedgeEval, edgeForm_apply]

example :
    wedgeEval (edgeForm (![0, 1, 2] : Fin 3 → ℚ) 1 2)
      (edgeForm ![0, 1, 2] 2 0) ![1, 0, 0] ![0, 1, 0] = -(1 / 2) := by
  norm_num [wedgeEval, edgeForm_apply]

example :
    wedgeEval (edgeForm (![0, 1, 2] : Fin 3 → ℚ) 2 0)
      (edgeForm ![0, 1, 2] 0 1) ![1, 0, 0] ![0, 1, 0] = -(1 / 2) := by
  norm_num [wedgeEval, edgeForm_apply]

end InfoGeometry.Feynman.FourPointLogarithmicPotentialAudit

run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owners : Array Name := #[
    `InfoGeometry.Projective.ThreePointLogarithmicForms,
    `InfoGeometry.Feynman.FourPointLogarithmicPotential]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for owner in owners do
    unless modules.contains owner do
      throwError "FOUR_POINT_AUDIT_FAILURE: missing owner {owner}"
  let mut count : Nat := 0
  let mut counts : NameMap Nat := {}
  let mut used : Array Name := #[]
  for (name, info) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let some owner := modules[idx.toNat]? |
      throwError "FOUR_POINT_AUDIT_FAILURE: invalid module index for {name}"
    if !owners.contains owner then continue
    if let .axiomInfo _ := info then
      throwError "FOUR_POINT_AUDIT_FAILURE: introduced axiom {name}"
    if info.isUnsafe || info.isPartial then
      throwError "FOUR_POINT_AUDIT_FAILURE: unsafe or partial declaration {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "FOUR_POINT_AUDIT_FAILURE: {name} depends on {ax}"
      if !used.contains ax then used := used.push ax
    count := count + 1
    counts := counts.insert owner ((counts.find? owner).getD 0 + 1)
  for owner in owners do
    let n := (counts.find? owner).getD 0
    if n == 0 then throwError "FOUR_POINT_AUDIT_FAILURE: empty owner {owner}"
    logInfo m!"FOUR_POINT_AUDIT_OWNER: {owner}: {n}"
  logInfo m!"FOUR_POINT_AUDIT_AXIOMS: {used.qsort Name.lt}"
  logInfo m!"FOUR_POINT_AUDIT_SUCCESS: {count} declarations in {owners.size} owners"
