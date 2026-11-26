/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import «InfoGeometry».«Algebra».«H3ZornE6SerreHom»
import «InfoGeometry».«Algebra».«H3ZornE6ChevalleyBruhat»
import «InfoGeometry».«Algebra».«H3ZornMinusculeCFSGBridge»
import «InfoGeometry».«Algebra».«H3OctonionZornComplexification»
import «InfoGeometry».«Algebra».«H3ZornF4Simplicity»
import «InfoGeometry».«Algebra».«H3OctonionSimplicity»
import «InfoGeometry».«Algebra».«H3ZornF4DimensionClosure»
import «InfoGeometry».«Algebra».«H3ZornReducedStructureLieAlgebra»
import «InfoGeometry».«Algebra».«H3ZornStructureGroup»
import «InfoGeometry».«Canonical».«H3ZornTKKNative»
import «InfoGeometry».«Canonical».«H3ZornJordanTripleBridge»
import «InfoGeometry».«Algebra».«H3ZornFreudenthalQuartic»
import «InfoGeometry».«Algebra».«H3ZornFreudenthalScaling»
import «InfoGeometry».«Algebra».«H3ZornFreudenthalQuarticPolarization»
import «InfoGeometry».«Algebra».«FreudenthalComplete»
import «InfoGeometry».«Exceptional».«Freudenthal»
import «InfoGeometry».«Exceptional».«FreudenthalAction»
import «InfoGeometry».«Exceptional».«FreudenthalChargeLinear»
import «InfoGeometry».«Exceptional».«FreudenthalCubicJordanBridge»
import «InfoGeometry».«Exceptional».«STUFreudenthalQuarticScaling»
import «InfoGeometry».«Exceptional».«STUFreudenthalBoundary»
import «InfoGeometry».«Algebra».«H3ZornFreudenthalLeviAction»
import «InfoGeometry».«Algebra».«H3ZornFreudenthalE7Group»
import «InfoGeometry».«Canonical».«NativeTitsE8Carrier»
import «InfoGeometry».«Canonical».«SplitFreudenthalTitsE8Carrier»
import «InfoGeometry».«Lie».«CanonicalZornIsKilling»
import «InfoGeometry».«Lie».«CanonicalZornRootSystemComparison»
import «InfoGeometry».«Lie».«SplitG2RealFormCapstone»
import «InfoGeometry».«Lie».«SplitOctonionStandardDerivation»
import «InfoGeometry».«Algebra».«JordanTKKLieAlgebra»
import «InfoGeometry».«Canonical».«H3ZornTKKLieAlgebra»
import «InfoGeometry».«Algebra».«H3OctonionTKKLieAlgebra»
import «InfoGeometry».«Algebra».«H3ZornE7RootSystem»
import «InfoGeometry».«Algebra».«H3ZornE7Simplicity»
import «InfoGeometry».«Algebra».«MagicSquareTitsBracket»
import «InfoGeometry».«Algebra».«SplitE8RootSystem»
import «InfoGeometry».«Algebra».«SplitE8Simplicity»
import «E6ClosureTests»
import «E7TKKFreudenthalTests»
import «E8MagicSquareTests»
import «E6E7E8CrossFeatureTests»
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Axiom audit for the E2E test suites (`E6ClosureTests`, `E7TKKFreudenthalTests`,
`E8MagicSquareTests`, `E6E7E8CrossFeatureTests`) and all 37 `E₆` Serre/Chevalley/Bruhat/
Complexification/`F₄`/`Str₀`/`TKK`/`E₇`/`Freudenthal`/`E₇(7)`/`Tits E₈`/`G₂`/
`Magic Square E₈(8)` owner and direct-import modules not audited separately in
`JordanE6CompleteAxiomAudit` (41 modules total).
Verifies that every declaration depends only on `[propext, Classical.choice, Quot.sound]`
with no unsafe or partial definitions.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `«InfoGeometry».«Algebra».«H3ZornE6SerreHom»,
    `«InfoGeometry».«Algebra».«H3ZornE6ChevalleyBruhat»,
    `«InfoGeometry».«Algebra».«H3ZornMinusculeCFSGBridge»,
    `«InfoGeometry».«Algebra».«H3OctonionZornComplexification»,
    `«InfoGeometry».«Algebra».«H3ZornF4Simplicity»,
    `«InfoGeometry».«Algebra».«H3OctonionSimplicity»,
    `«InfoGeometry».«Algebra».«H3ZornF4DimensionClosure»,
    `«InfoGeometry».«Algebra».«H3ZornReducedStructureLieAlgebra»,
    `«InfoGeometry».«Algebra».«H3ZornStructureGroup»,
    `«InfoGeometry».«Canonical».«H3ZornTKKNative»,
    `«InfoGeometry».«Canonical».«H3ZornJordanTripleBridge»,
    `«InfoGeometry».«Algebra».«H3ZornFreudenthalQuartic»,
    `«InfoGeometry».«Algebra».«H3ZornFreudenthalScaling»,
    `«InfoGeometry».«Algebra».«H3ZornFreudenthalQuarticPolarization»,
    `«InfoGeometry».«Algebra».«FreudenthalComplete»,
    `«InfoGeometry».«Exceptional».«Freudenthal»,
    `«InfoGeometry».«Exceptional».«FreudenthalAction»,
    `«InfoGeometry».«Exceptional».«FreudenthalChargeLinear»,
    `«InfoGeometry».«Exceptional».«FreudenthalCubicJordanBridge»,
    `«InfoGeometry».«Exceptional».«STUFreudenthalQuarticScaling»,
    `«InfoGeometry».«Exceptional».«STUFreudenthalBoundary»,
    `«InfoGeometry».«Algebra».«H3ZornFreudenthalLeviAction»,
    `«InfoGeometry».«Algebra».«H3ZornFreudenthalE7Group»,
    `«InfoGeometry».«Canonical».«NativeTitsE8Carrier»,
    `«InfoGeometry».«Canonical».«SplitFreudenthalTitsE8Carrier»,
    `«InfoGeometry».«Lie».«CanonicalZornIsKilling»,
    `«InfoGeometry».«Lie».«CanonicalZornRootSystemComparison»,
    `«InfoGeometry».«Lie».«SplitG2RealFormCapstone»,
    `«InfoGeometry».«Lie».«SplitOctonionStandardDerivation»,
    `«InfoGeometry».«Algebra».«JordanTKKLieAlgebra»,
    `«InfoGeometry».«Canonical».«H3ZornTKKLieAlgebra»,
    `«InfoGeometry».«Algebra».«H3OctonionTKKLieAlgebra»,
    `«InfoGeometry».«Algebra».«H3ZornE7RootSystem»,
    `«InfoGeometry».«Algebra».«H3ZornE7Simplicity»,
    `«InfoGeometry».«Algebra».«MagicSquareTitsBracket»,
    `«InfoGeometry».«Algebra».«SplitE8RootSystem»,
    `«InfoGeometry».«Algebra».«SplitE8Simplicity»,
    `«E6ClosureTests»,
    `«E7TKKFreudenthalTests»,
    `«E8MagicSquareTests»,
    `«E6E7E8CrossFeatureTests»]
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
