/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.ArnoldSDiffFlowErlangenClosure
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Data.Json

/-! Audit every declaration owned by the mathematical owners checked for this integration, including generated
declarations. Dependencies come from the checked types and proof/definition
values, and axioms are collected transitively. This is verification tooling. -/

open Lean Elab Command

namespace ArnoldSDiffFlowErlangenDeclarationAudit

private def owners : Array Name := #[
  `InfoGeometry.Canonical.FlowConjugation,
  `InfoGeometry.Canonical.SmoothDiffeomorphismPushforward,
  `InfoGeometry.Canonical.SmoothFlowGenerator,
  `InfoGeometry.Erlangen.SymmetryClosure,
  `InfoGeometry.Canonical.OperatorErlangenCompatibility,
  `InfoGeometry.Canonical.SmoothVectorFieldSpanSymmetry,
  `InfoGeometry.Canonical.ArnoldSDiffFlowErlangenClosure
]

private def ownerOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
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
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if owners.contains (ownerOf env name) then
      names := names.push name
  names := names.qsort Name.lt
  for owner in owners do
    unless env.header.moduleNames.contains owner do
      throwError "Requested owner not imported: {owner}"
    unless names.any (fun name => ownerOf env name == owner) do
      throwError "No declarations found in requested owner: {owner}"
  for name in names do
    let some info := env.find? name | throwError "Missing declaration {name}"
    let axioms ← collectAxioms name
    if info.isUnsafe || info.isPartial || kindOf info == "axiom" then
      throwError "Rejected declaration {name}: unsafe, partial, or local axiom"
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Rejected axiom {ax} in declaration {name}"
    let dependencies := info.getUsedConstantsAsSet.toArray.qsort Name.lt
    let ownedDeps := dependencies.filter fun d => owners.contains (ownerOf env d)
    liftIO <| IO.println (Json.mkObj [
      ("record", toJson "declaration"),
      ("name", toJson name.toString),
      ("module", toJson (ownerOf env name).toString),
      ("kind", toJson (kindOf info)),
      ("unsafe", toJson info.isUnsafe),
      ("partial", toJson info.isPartial),
      ("axioms", toJson (axioms.map Name.toString)),
      ("dependencies", toJson (dependencies.map Name.toString)),
      ("owned_dependencies", toJson (ownedDeps.map Name.toString))
    ]).compress
  liftIO <| IO.println (Json.mkObj [
    ("record", toJson "summary"),
    ("declarations", toJson names.size),
    ("modules", toJson (owners.map Name.toString)),
    ("owner_counts", Json.mkObj (owners.toList.map fun owner =>
      (owner.toString, toJson ((names.filter fun name => ownerOf env name == owner).size)))),
    ("axiom_whitelist", toJson (allowed.map Name.toString)),
    ("status", toJson "PASS")
  ]).compress

end ArnoldSDiffFlowErlangenDeclarationAudit
