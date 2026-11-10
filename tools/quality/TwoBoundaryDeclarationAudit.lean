/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.KrausBoundaryDuality
import InfoGeometry.Quantum.FinitePartialTrace
import InfoGeometry.Quantum.FiniteAttentionCanonicalBridges
import InfoGeometry.OperatorAlgebra.SemilinearSheetGeometry
import InfoGeometry.Quantum.BoundaryInstrument
import InfoGeometry.Quantum.MixedBoundaryReadout
import InfoGeometry.Quantum.MatrixBoundaryPurification
import InfoGeometry.Quantum.SemilinearBoundaryReversal
import InfoGeometry.Quantum.TwoBoundaryOperatorExamples
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Data.Json

/-!
Enumerate all declarations, including private and generated declarations, in
exactly the touched operator owners. Check transitive foundational axioms and
record actual constants in checked types and values for the dependency order.
This command supplies no mathematical assumption to the imported owners.
-/

open Lean Elab Command

namespace TwoBoundaryDeclarationAudit

private def owners : Array Name := #[
  `InfoGeometry.Quantum.KrausBoundaryDuality,
  `InfoGeometry.Quantum.FinitePartialTrace,
  `InfoGeometry.Quantum.FiniteAttentionCanonicalBridges,
  `InfoGeometry.OperatorAlgebra.SemilinearSheetGeometry,
  `InfoGeometry.Quantum.BoundaryInstrument,
  `InfoGeometry.Quantum.MixedBoundaryReadout,
  `InfoGeometry.Quantum.MatrixBoundaryPurification,
  `InfoGeometry.Quantum.SemilinearBoundaryReversal,
  `InfoGeometry.Quantum.TwoBoundaryOperatorExamples
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
      throwError "Requested owner module was not imported: {owner}"
    unless names.any (fun name => ownerOf env name == owner) do
      throwError "No declarations found in requested owner module {owner}"
  for name in names do
    let some info := env.find? name | throwError "Missing declaration {name}"
    let axioms ← collectAxioms name
    if info.isUnsafe || info.isPartial || kindOf info == "axiom" then
      throwError "Rejected declaration {name}: unsafe, partial, or local axiom"
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Rejected axiom {ax} in declaration {name}"
    let typeDeps := info.type.getUsedConstantsAsSet
    let valueDeps := match info.value? (allowOpaque := true) with
      | some value => value.getUsedConstantsAsSet
      | none => ({} : NameSet)
    let dependencies := (typeDeps ++ valueDeps).toArray.qsort Name.lt
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
    ("empty_modules", toJson (#[] : Array String)),
    ("axiom_whitelist", toJson (allowed.map Name.toString)),
    ("status", toJson "PASS")
  ]).compress

end TwoBoundaryDeclarationAudit
