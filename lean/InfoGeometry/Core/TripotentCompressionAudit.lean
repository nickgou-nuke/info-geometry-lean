/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentCompressionCStar
import InfoGeometry.Core.TripotentCompressionHilbert
import InfoGeometry.Core.CornerCentrality
import InfoGeometry.OperatorAlgebra.TriadicCompressionCounterexample
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Elab.Command

/-!
# Declaration and dependency audit for tripotent compression

Audit every declaration owned by the selected modules, including private and
generated declarations. Direct dependencies from both declaration types and
proof/definition values are reported separately from transitive foundational
axioms. Neither report proves a physical interpretation.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owners : Array Name := #[
    `InfoGeometry.Physics.Algebra.TripotentPeirceProjectors,
    `InfoGeometry.Core.PeirceDecomposition,
    `InfoGeometry.Core.PeirceCompressionDefect,
    `InfoGeometry.Core.PeirceCompressionCStar,
    `InfoGeometry.Core.CornerCentrality,
    `InfoGeometry.Core.TripotentCompression,
    `InfoGeometry.Core.TripotentCompressionCStar,
    `InfoGeometry.Core.TripotentCompressionHilbert,
    `InfoGeometry.OperatorAlgebra.TriadicCompressionCounterexample]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for owner in owners do
    unless modules.contains owner do
      throwError "TRIADIC_COMPRESSION_AUDIT_FAILURE: missing owner {owner}"
  let mut count : Nat := 0
  let mut theoremCount : Nat := 0
  let mut counts : NameMap Nat := {}
  for (name, info) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let some owner := modules[idx.toNat]? |
      throwError "TRIADIC_COMPRESSION_AUDIT_FAILURE: invalid module index for {name}"
    if !owners.contains owner then continue
    if let .axiomInfo _ := info then
      throwError "TRIADIC_COMPRESSION_AUDIT_FAILURE: introduced axiom {name}"
    if info.isUnsafe || info.isPartial then
      throwError "TRIADIC_COMPRESSION_AUDIT_FAILURE: unsafe or partial declaration {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "TRIADIC_COMPRESSION_AUDIT_FAILURE: {name} depends on {ax}"
    count := count + 1
    counts := counts.insert owner ((counts.find? owner).getD 0 + 1)
    if let .thmInfo _ := info then theoremCount := theoremCount + 1
    logInfo m!"TRIADIC_COMPRESSION_DECL: {owner}: {name}: {axioms}"
    let mut dependencies := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      for dependency in value.getUsedConstants do
        unless dependencies.contains dependency do
          dependencies := dependencies.push dependency
    for dependency in dependencies do
      let some depIdx := env.getModuleIdxFor? dependency | continue
      let some depOwner := modules[depIdx.toNat]? | continue
      if owners.contains depOwner then
        logInfo m!"TRIADIC_COMPRESSION_EDGE: {dependency} -> {name}"
  for owner in owners do
    let n := (counts.find? owner).getD 0
    if n == 0 then throwError "TRIADIC_COMPRESSION_AUDIT_FAILURE: empty owner {owner}"
    logInfo m!"TRIADIC_COMPRESSION_OWNER: {owner}: {n}"
  logInfo m!"TRIADIC_COMPRESSION_AUDIT_PASS: {count} declarations, {theoremCount} theorem declarations; only propext, Classical.choice, Quot.sound permitted"
