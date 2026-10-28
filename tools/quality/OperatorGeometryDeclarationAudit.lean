/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceKrausGeometry
import InfoGeometry.OperatorAlgebra.OperatorGeometryExamples
import InfoGeometry.OperatorAlgebra.OperatorExtensionExamples
import InfoGeometry.OperatorAlgebra.MatrixCasimirExamples
import InfoGeometry.OperatorAlgebra.PeircePairExamples
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Data.Json

/-! Audit every declaration owned by the fourteen mathematical modules, including generated
declarations. Dependencies come from the checked types and proof/definition
values, and axioms are collected transitively. This is verification tooling. -/

open Lean Elab Command

namespace OperatorGeometryDeclarationAudit

private def owners : Array Name := #[
  `InfoGeometry.OperatorAlgebra.MatrixOperatorIdentities,
  `InfoGeometry.OperatorAlgebra.MatrixTraceGeometry,
  `InfoGeometry.OperatorAlgebra.PeirceTraceGeometry,
  `InfoGeometry.OperatorAlgebra.PeirceKrausGeometry,
  `InfoGeometry.OperatorAlgebra.OperatorGeometryExamples,
  `InfoGeometry.OperatorAlgebra.PeirceChiralGeometry,
  `InfoGeometry.OperatorAlgebra.MatrixMaurerCartan,
  `InfoGeometry.OperatorAlgebra.MatrixConservation,
  `InfoGeometry.OperatorAlgebra.MatrixCayleyGeometry,
  `InfoGeometry.OperatorAlgebra.OperatorExtensionExamples,
  `InfoGeometry.OperatorAlgebra.MatrixCasimirExamples,
  `InfoGeometry.OperatorAlgebra.PeircePairGeometry,
  `InfoGeometry.OperatorAlgebra.PeircePairPositivity,
  `InfoGeometry.OperatorAlgebra.PeircePairExamples
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
  if names.isEmpty then
    throwError "No declarations found in requested owner modules"
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
    ("axiom_whitelist", toJson (allowed.map Name.toString)),
    ("status", toJson "PASS")
  ]).compress

end OperatorGeometryDeclarationAudit
