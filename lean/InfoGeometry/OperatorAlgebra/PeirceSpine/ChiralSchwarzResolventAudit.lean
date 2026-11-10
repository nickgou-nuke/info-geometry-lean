/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralSchwarzCentralizer
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralSchwarzResolvent
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetRelativeLog
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Data.Json

/-!
# Declaration audit for the chiral Schwarz and resolvent extension

This verification module inspects every declaration owned by the seven new
mathematical modules, including generated declarations. It rejects unsafe or
partial declarations, local axioms, and transitive axiom dependencies outside
the repository's foundational whitelist. Dependencies are read from the checked
types and proof or definition values.

The topological order is computed from these actual dependencies. Independent
branches remain incomparable in the dependency relation: the printed linear
extension does not assert an implication between adjacent declarations.
This is verification tooling, not an additional mathematical axiom.
-/

open Lean Elab Command

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralSchwarzResolventAudit

private def owners : Array Name := #[
  `InfoGeometry.OperatorAlgebra.QuadraticResolventCalculus,
  `InfoGeometry.OperatorAlgebra.SquareZeroCStarRigidity,
  `InfoGeometry.OperatorAlgebra.LogarithmicResolventPositivity,
  `InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralSchwarzCounterexample,
  `InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralSchwarzCentralizer,
  `InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralSchwarzResolvent,
  `InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetRelativeLog
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
    if !(names.any fun name => ownerOf env name == owner) then
      throwError "No declarations found in requested owner module {owner}"
  let mut pending := names
  let mut ordered : Array Name := #[]
  for _ in [:names.size] do
    if pending.isEmpty then
      break
    let mut remaining : Array Name := #[]
    let before := ordered.size
    for name in pending do
      let some info := env.find? name | throwError "Missing declaration {name}"
      let deps := info.getUsedConstantsAsSet.toArray.filter fun d => names.contains d
      if deps.all ordered.contains then
        ordered := ordered.push name
      else
        remaining := remaining.push name
    if ordered.size == before then
      throwError "Cycle in owned declaration dependencies: {remaining}"
    pending := remaining
  if !pending.isEmpty then
    throwError "Incomplete declaration dependency order"
  let mut theoremCount := 0
  let mut edgeCount := 0
  for name in names do
    let some info := env.find? name | throwError "Missing declaration {name}"
    let axioms ← collectAxioms name
    if info.isUnsafe || info.isPartial || kindOf info == "axiom" then
      throwError "Rejected declaration {name}: unsafe, partial, or local axiom"
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Rejected axiom {ax} in declaration {name}"
    let dependencies := info.getUsedConstantsAsSet.toArray.qsort Name.lt
    let ownedDeps := dependencies.filter fun d => names.contains d
    if kindOf info == "theorem" then
      theoremCount := theoremCount + 1
    edgeCount := edgeCount + ownedDeps.size
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
    ("theorems", toJson theoremCount),
    ("owned_dependency_edges", toJson edgeCount),
    ("modules", toJson (owners.map Name.toString)),
    ("axiom_whitelist", toJson (allowed.map Name.toString)),
    ("dependency_order", toJson (ordered.map Name.toString)),
    ("acyclic", toJson true),
    ("status", toJson "PASS")
  ]).compress

end InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralSchwarzResolventAudit
