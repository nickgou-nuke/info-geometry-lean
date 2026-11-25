/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CotangentLieAlgebra
import InfoGeometry.Geometry.CotangentUnitLinearization
import InfoGeometry.Geometry.SkewGraphNeutralPairing
import InfoGeometry.Geometry.MatrixDiracGraphs
import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Lean.Data.Json

/-!
Audit all declarations owned by the four capstone modules. Ownership is
read from the imported Lean environment, rather than inferred from a name
prefix or a hand-maintained list of theorems. The source owners provide no
axiom or audit-exemption input to this command.

The imported-owner enumeration follows the maintained repository audit
pattern in `tools/quality/TwoBoundaryDeclarationAudit.lean`. Public
`Lean.collectAxioms` resolves transitive axiom dependencies, including
imported axiom metadata and dependencies through private bodies.
-/

open Lean Elab Command

namespace CapstoneDeclarationAudit

private def owners : Array Name := #[
  `InfoGeometry.Lie.CotangentLieAlgebra,
  `InfoGeometry.Geometry.CotangentUnitLinearization,
  `InfoGeometry.Geometry.SkewGraphNeutralPairing,
  `InfoGeometry.Geometry.MatrixDiracGraphs
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
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if owners.contains (ownerOf env name) then
      names := names.push name
  names := names.qsort Name.lt
  for owner in owners do
    unless env.header.moduleNames.contains owner do
      throwError "Requested owner was not imported: {owner}"
    unless names.any (fun name => ownerOf env name == owner) do
      throwError "Requested owner has no audited declarations: {owner}"
  let mut unionAxioms : Array Name := #[]
  for name in names do
    let some info := env.find? name | throwError "Missing declaration: {name}"
    if info.isUnsafe || info.isPartial || kindOf info == "axiom" then
      throwError "Rejected owned declaration: {name}"
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Rejected transitive axiom {axiomName} in {name}"
      if !unionAxioms.contains axiomName then
        unionAxioms := unionAxioms.push axiomName
    liftIO <| IO.println (Json.mkObj [
      ("record", toJson "declaration"),
      ("name", toJson name.toString),
      ("module", toJson (ownerOf env name).toString),
      ("kind", toJson (kindOf info)),
      ("unsafe", toJson info.isUnsafe),
      ("partial", toJson info.isPartial),
      ("axioms", toJson ((axioms.qsort Name.lt).map Name.toString))
    ]).compress
  for owner in owners do
    liftIO <| IO.println (Json.mkObj [
      ("record", toJson "module"),
      ("module", toJson owner.toString),
      ("declarations", toJson (names.filter (fun name => ownerOf env name == owner)).size)
    ]).compress
  liftIO <| IO.println (Json.mkObj [
    ("record", toJson "summary"),
    ("status", toJson "PASS"),
    ("declarations", toJson names.size),
    ("modules", toJson (owners.map Name.toString)),
    ("axioms", toJson ((unionAxioms.qsort Name.lt).map Name.toString)),
    ("axiom_whitelist", toJson (allowed.map Name.toString))
  ]).compress

end CapstoneDeclarationAudit
