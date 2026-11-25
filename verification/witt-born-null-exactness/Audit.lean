/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornLeftInverse
import InfoGeometry.Algebra.ZornLeftDeterminant
import InfoGeometry.Algebra.ZornPrimalDual
import InfoGeometry.Algebra.ZornChiralOperatorReconstruction
import InfoGeometry.Canonical.SouriauAffineActionGroupoid
import InfoGeometry.Geometry.SouriauCotangentGraphSigns
import InfoGeometry.Lie.SplitOctonionCliffordAction
import InfoGeometry.Lie.SplitOctonionCliffordNoninjective
import InfoGeometry.Algebra.ZornNullIncidence
import InfoGeometry.Canonical.ZornCliffordKleinHierarchy
import InfoGeometry.Canonical.ZornCliffordSourceVolume
import InfoGeometry.Lie.SplitOctonionNullPlaneCovariance
import InfoGeometry.Canonical.ZornCliffordRepresentation
import InfoGeometry.Canonical.ZornCliffordWittBorn
import InfoGeometry.Verification.SuppliedTableCounterexample
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

section GroupoidCheck
open InfoGeometry.Canonical.SouriauAffineActionGroupoid
open InfoGeometry.Algebra SouriauCoadjoint
variable {G V : Type*} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [LinearGroupAction G V] (Θ : AffineCoadjointCocycle G V)
example : CategoryTheory.Groupoid (AffineActionGroupoid Θ) := inferInstance
end GroupoidCheck

run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `InfoGeometry.Algebra.ZornLeftInverse,
    `InfoGeometry.Algebra.ZornLeftDeterminant,
    `InfoGeometry.Algebra.ZornPrimalDual,
    `InfoGeometry.Algebra.ZornChiralOperatorReconstruction,
    `InfoGeometry.Canonical.SouriauAffineActionGroupoid,
    `InfoGeometry.Geometry.SouriauCotangentGraphSigns,
    `InfoGeometry.Lie.SplitOctonionCliffordAction,
    `InfoGeometry.Lie.SplitOctonionCliffordNoninjective,
    `InfoGeometry.Algebra.ZornNullIncidence,
    `InfoGeometry.Canonical.ZornCliffordKleinHierarchy,
    `InfoGeometry.Canonical.ZornCliffordSourceVolume,
    `InfoGeometry.Lie.SplitOctonionNullPlaneCovariance,
    `InfoGeometry.Canonical.ZornCliffordRepresentation,
    `InfoGeometry.Canonical.ZornCliffordWittBorn,
    `InfoGeometry.Verification.SuppliedTableCounterexample]
  for target in targets do
    unless env.header.moduleNames.contains target do
      throwError "Selected module not imported: {target}"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  let mut counts : NameMap Nat := {}
  let mut allAxioms : Array Name := #[]
  for (name, info) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx.toNat]!
    if !targets.contains owner then continue
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial declaration: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Disallowed axiom {ax} in {name}"
      if !allAxioms.contains ax then allAxioms := allAxioms.push ax
    count := count + 1
    counts := counts.insert owner ((counts.find? owner).getD 0 + 1)
  for target in targets do
    let n := (counts.find? target).getD 0
    if n == 0 then throwError "No declarations audited in {target}"
    logInfo m!"AUDIT_MODULE_COUNT: {target}: {n}"
  logInfo m!"AUDIT_AXIOMS: {allAxioms.qsort Name.lt}"
  logInfo m!"AUDIT_COUNT: {count}"
