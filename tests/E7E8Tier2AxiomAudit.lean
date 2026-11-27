/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import «InfoGeometry».«Algebra».«H3ZornE7SerreHom»
import «InfoGeometry».«Algebra».«SplitE8SerreHom»
import «InfoGeometry».«Algebra».«CompactOctonionG2Derivations»
import «InfoGeometry».«Algebra».«CompactE8MagicSquare»
import «InfoGeometry».«Algebra».«H3ZornFreudenthalTKK5E8»
import «InfoGeometry».«Algebra».«CompactOctonion»
import «InfoGeometry».«Algebra».«H3Octonion»
import «InfoGeometry».«Algebra».«H3OctonionLieAlgebra»
import «InfoGeometry».«Algebra».«H3OctonionSimplicity»
import «InfoGeometry».«Algebra».«H3OctonionTKKLieAlgebra»
import «InfoGeometry».«Algebra».«AlternativeDerivations»
import «InfoGeometry».«Algebra».«H3ZornAutomorphismConjugation»
import «InfoGeometry».«Exceptional».«GenericGradedJacobiClosure»
import «InfoGeometry».«Lie».«SplitOctonionStandardDerivationCovariance»
import «InfoGeometry».«Lie».«CanonicalZornDerivationDimension»
import «E7E8Tier2Tests»
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Axiom and safety audit for the Exceptional Algebra Tier-2 owner modules
(`H3ZornE7SerreHom`, `SplitE8SerreHom`, `CompactOctonionG2Derivations`,
`CompactE8MagicSquare`, `H3ZornFreudenthalTKK5E8`), their compact-octonion/Albert
and supporting dependencies (`CompactOctonion`, `H3Octonion`, `H3OctonionLieAlgebra`,
`H3OctonionSimplicity`, `H3OctonionTKKLieAlgebra`, `AlternativeDerivations`,
`H3ZornAutomorphismConjugation`, `GenericGradedJacobiClosure`,
`SplitOctonionStandardDerivationCovariance`, `CanonicalZornDerivationDimension`),
and the Tier-2 E2E test suite (`E7E8Tier2Tests`).
Verifies that every declaration depends only on `[propext, Classical.choice, Quot.sound]`
with no unsafe or partial definitions.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `«InfoGeometry».«Algebra».«H3ZornE7SerreHom»,
    `«InfoGeometry».«Algebra».«SplitE8SerreHom»,
    `«InfoGeometry».«Algebra».«CompactOctonionG2Derivations»,
    `«InfoGeometry».«Algebra».«CompactE8MagicSquare»,
    `«InfoGeometry».«Algebra».«H3ZornFreudenthalTKK5E8»,
    `«InfoGeometry».«Algebra».«CompactOctonion»,
    `«InfoGeometry».«Algebra».«H3Octonion»,
    `«InfoGeometry».«Algebra».«H3OctonionLieAlgebra»,
    `«InfoGeometry».«Algebra».«H3OctonionSimplicity»,
    `«InfoGeometry».«Algebra».«H3OctonionTKKLieAlgebra»,
    `«InfoGeometry».«Algebra».«AlternativeDerivations»,
    `«InfoGeometry».«Algebra».«H3ZornAutomorphismConjugation»,
    `«InfoGeometry».«Exceptional».«GenericGradedJacobiClosure»,
    `«InfoGeometry».«Lie».«SplitOctonionStandardDerivationCovariance»,
    `«InfoGeometry».«Lie».«CanonicalZornDerivationDimension»,
    `«E7E8Tier2Tests»]
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
