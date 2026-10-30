/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.WheelerEpilogueWitness
import InfoGeometry.WheelerEpilogueRegression
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Data.Json

open Lean Elab Command

namespace WheelerEpilogueAudit

private def owners : Array Name := #[
  `InfoGeometry.WheelerEpilogue,
  `InfoGeometry.WheelerEpilogueWitness,
  `InfoGeometry.WheelerEpilogueRegression
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
  let env := (← getEnv).setExporting false
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut names : Array Name := #[]
  let mut counts : NameMap Nat := {}
  for (name, _) in env.constants.toList do
    let owner := ownerOf env name
    if owners.contains owner then
      names := names.push name
      counts := counts.insert owner ((counts.find? owner).getD 0 + 1)
  for owner in owners do
    unless env.header.moduleNames.contains owner do
      throwError "Owner not imported: {owner}"
    if (counts.find? owner).getD 0 == 0 then
      throwError "Empty owner audit: {owner}"
  for name in names.qsort Name.lt do
    let some info := env.find? name | throwError "Missing declaration: {name}"
    -- Macro implementations are executable meta-level tooling, not proof
    -- declarations. Audit the mathematical declarations and regression
    -- theorems; record (rather than certify as mathematics) generated macro
    -- implementations separately.
    if info.isUnsafe then
      if ownerOf env name == `InfoGeometry.WheelerEpilogueRegression then
        liftIO <| IO.println (Json.mkObj [
          ("record", toJson "meta_tooling"), ("name", toJson name.toString),
          ("reason", toJson "unsafe macro implementation; not a mathematical proof")]).compress
        continue
      throwError "Unsafe mathematical declaration: {name}"
    if info.isPartial || kindOf info == "axiom" then
      throwError "Partial declaration or local axiom: {name}"
    let value? := info.value? (allowOpaque := true)
    if (kindOf info == "theorem" || kindOf info == "definition" ||
        kindOf info == "opaque") && value?.isNone then
      throwError "Missing declaration body: {name}"
    let axioms := (← collectAxioms name).qsort Name.lt
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Disallowed axiom {ax} in {name}"
    let deps := info.getUsedConstantsAsSet.toArray.qsort Name.lt
    liftIO <| IO.println (Json.mkObj [
      ("record", toJson "declaration"),
      ("name", toJson name.toString),
      ("module", toJson (ownerOf env name).toString),
      ("kind", toJson (kindOf info)),
      ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial),
      ("value_present", toJson value?.isSome),
      ("axioms", toJson (axioms.map Name.toString)),
      ("dependencies", toJson (deps.map Name.toString)),
      ("owned_dependencies", toJson ((deps.filter fun d => owners.contains (ownerOf env d)).map Name.toString)),
      ("external_dependencies", toJson ((deps.filter fun d => !owners.contains (ownerOf env d)).map Name.toString))
    ]).compress
  liftIO <| IO.println (Json.mkObj [
    ("record", toJson "summary"), ("status", toJson "PASS"),
    ("modules", toJson (owners.map Name.toString)),
    ("axiom_whitelist", toJson (allowed.map Name.toString)),
    ("scope", toJson "mathematics and regression proofs; meta-tooling separately reported")
  ]).compress

end WheelerEpilogueAudit
