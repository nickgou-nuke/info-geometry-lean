/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.PeirceStarColimit
import InfoGeometry.Examples.RealMatrixModeWitness
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Data.Json

/-!
# Native declaration audit for the real Peirce star-colimit packet

This command inspects every declaration owned by the five selected modules,
including private and generated declarations. Ownership comes from Lean's
module metadata. Reference edges come from the elaborated type and available
proof or definition value, with external references retained. The axiom audit
uses Lean's public transitive collector.

This is verification tooling, not a new mathematical theorem or a hand-written
dependency order. Its JSONL declaration and summary records are accepted by
`tools/quality/operator_geometry_dependency_order.py`.
-/

open Lean Elab Command

namespace PeirceStarColimitAudit

private def owners : Array Name := #[
  `InfoGeometry.Core.PeirceStarFunctoriality,
  `InfoGeometry.OperatorAlgebra.SquareZeroModeActions,
  `InfoGeometry.Canonical.RealStarColimitUniversal,
  `InfoGeometry.Canonical.PeirceStarColimit,
  `InfoGeometry.Examples.RealMatrixModeWitness
]

private def ownerOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index.toNat]!
  | none => env.mainModule

private def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

run_cmd do
  -- Use private visibility for both enumeration and value lookup. The public
  -- `collectAxioms` function independently uses private visibility internally.
  let env := (← getEnv).setExporting false
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for owner in owners do
    unless env.header.moduleNames.contains owner do
      throwError "Requested owner module is not imported: {owner}"
  let mut names : Array Name := #[]
  let mut ownerCounts : NameMap Nat := {}
  for (name, _) in env.constants.toList do
    let owner := ownerOf env name
    if owners.contains owner then
      names := names.push name
      ownerCounts := ownerCounts.insert owner ((ownerCounts.find? owner).getD 0 + 1)
  names := names.qsort Name.lt
  for owner in owners do
    if (ownerCounts.find? owner).getD 0 == 0 then
      throwError "No declarations found in requested owner module: {owner}"
  if names.isEmpty then
    throwError "No declarations found in requested owner modules"
  for name in names do
    let some info := env.find? name | throwError "Missing owned declaration: {name}"
    if info.isUnsafe || info.isPartial || kindOf info == "axiom" then
      throwError "Rejected declaration {name}: unsafe, partial, or local axiom"
    let needsValue := match info with
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ => true
      | _ => false
    let value? := info.value? (allowOpaque := true)
    if needsValue && value?.isNone then
      throwError "Missing proof or definition value for owned declaration: {name}"
    let axioms := (← collectAxioms name).qsort Name.lt
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Rejected transitive axiom {axiomName} in declaration {name}"
    let typeDeps := info.type.getUsedConstantsAsSet.toArray.qsort Name.lt
    let valueDeps := match value? with
      | some value => value.getUsedConstantsAsSet.toArray.qsort Name.lt
      | none => #[]
    -- The native utility includes type and value references, plus the native
    -- structural references for any inductive, constructor, or recursor.
    let dependencies := info.getUsedConstantsAsSet.toArray.qsort Name.lt
    for dependency in dependencies do
      if (env.find? dependency).isNone then
        throwError "Unresolved declaration reference {dependency} in {name}"
    let ownedDeps := dependencies.filter fun dependency =>
      owners.contains (ownerOf env dependency)
    let externalDeps := dependencies.filter fun dependency =>
      !owners.contains (ownerOf env dependency)
    liftIO <| IO.println (Json.mkObj [
      ("record", toJson "declaration"),
      ("name", toJson name.toString),
      ("module", toJson (ownerOf env name).toString),
      ("kind", toJson (kindOf info)),
      ("unsafe", toJson info.isUnsafe),
      ("partial", toJson info.isPartial),
      ("value_present", toJson value?.isSome),
      ("axioms", toJson (axioms.map Name.toString)),
      ("type_dependencies", toJson (typeDeps.map Name.toString)),
      ("value_dependencies", toJson (valueDeps.map Name.toString)),
      ("dependencies", toJson (dependencies.map Name.toString)),
      ("owned_dependencies", toJson (ownedDeps.map Name.toString)),
      ("external_dependencies", toJson (externalDeps.map Name.toString))
    ]).compress
  for owner in owners do
    liftIO <| IO.println (Json.mkObj [
      ("record", toJson "owner_count"),
      ("module", toJson owner.toString),
      ("declarations", toJson ((ownerCounts.find? owner).getD 0))
    ]).compress
  let ownerCountsJson := Json.mkObj (owners.toList.map fun owner =>
    (owner.toString, toJson ((ownerCounts.find? owner).getD 0)))
  liftIO <| IO.println (Json.mkObj [
    ("record", toJson "summary"),
    ("declarations", toJson names.size),
    ("modules", toJson (owners.map Name.toString)),
    ("owner_counts", ownerCountsJson),
    ("axiom_whitelist", toJson (allowed.map Name.toString)),
    ("reference_scope", toJson "elaborated type and value; external references retained"),
    ("ownership_scope", toJson "exact module metadata, including private and generated declarations"),
    ("status", toJson "PASS")
  ]).compress

end PeirceStarColimitAudit
