/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ArnoldSDiffFlowErlangenClosure
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Data.Json

/-!
# Declaration audit and action-selection consumers

The consumer examples check the material instance-selection boundary:
importing the field owner leaves ordinary pointwise action available, while
opening `VectorFieldPushforward` selects the actual derivative action, also
inside a product with the measure action. This distinction is not established
by an axiom scan alone.

The audit enumerates every declaration owned by the five mathematical modules,
including private and generated declarations, using native module ownership
rather than namespace prefixes. It rejects owned axioms, unsafe and partial
declarations, and any transitive axiom outside the stated foundational list.
Native dependency sets are recorded for review; no quotient-manifold or PDE
interpretation is certified by this tooling.
-/

noncomputable section

open InfoGeometry.Canonical

namespace ArnoldSDiffFlowErlangenAudit

section OutsideScope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Importing the owner does not globally replace ordinary pointwise action.
example (g : smoothDiffeomorphismSubgroup E) (X : E → E) (y : E) :
    (g • X) y = g.val (X y) := rfl

end OutsideScope

section InsideScope

open scoped VectorFieldPushforward

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- The scope selects derivative pushforward, including its inverse basepoint.
example (g : smoothDiffeomorphismSubgroup E) (X : E → E) (y : E) :
    (g • X) y = fderiv ℝ (g.val : E → E) (g.val.symm y) (X (g.val.symm y)) := rfl

-- The selected SMul is coherent with the selected group-action laws.
example (g h : smoothDiffeomorphismSubgroup E) (X : E → E) :
    (g * h) • X = g • (h • X) := mul_smul g h X

variable [MeasurableSpace E] [BorelSpace E]

-- The product carrier retains measure pushforward in its first factor.
example (g : smoothDiffeomorphismSubgroup E) (μ : MeasureTheory.Measure E) (X : E → E) :
    (g • (μ, X)).1 = μ.map (g.val : E → E) := rfl

-- Its field factor uses derivative pushforward, not pointwise composition.
example (g : smoothDiffeomorphismSubgroup E) (μ : MeasureTheory.Measure E)
    (X : E → E) (y : E) :
    (g • (μ, X)).2 y =
      fderiv ℝ (g.val : E → E) (g.val.symm y) (X (g.val.symm y)) := rfl

end InsideScope

open Lean Elab Command

private def owners : Array Name := #[
  `InfoGeometry.Canonical.ArnoldBeltramiSmoothFlow,
  `InfoGeometry.Canonical.FlowConjugation,
  `InfoGeometry.Canonical.FlowErlangenClosure,
  `InfoGeometry.Canonical.SmoothVectorFieldPushforward,
  `InfoGeometry.Canonical.ArnoldSDiffFlowErlangenClosure
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
  for (name, _) in env.constants.toList do
    if owners.contains (ownerOf env name) then
      names := names.push name
  names := names.qsort Name.lt
  for owner in owners do
    if !(names.any fun name => ownerOf env name == owner) then
      throwError "No declarations found in requested owner module {owner}"
  for name in names do
    let some info := env.checked.get.find? name |
      throwError "Missing checked declaration {name}"
    let axioms ← collectAxioms name
    if info.isUnsafe || info.isPartial || kindOf info == "axiom" then
      throwError "Rejected declaration {name}: unsafe, partial, or local axiom"
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Rejected axiom {ax} in declaration {name}"
    let dependencies := info.getUsedConstantsAsSet.toArray.qsort Name.lt
    let ownedDeps := dependencies.filter fun dependency => owners.contains (ownerOf env dependency)
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
  if (← MonadLog.hasErrors) then
    throwError "Consumer or declaration audit logged an error; refusing a success summary"
  let moduleCounts := owners.map fun owner => Json.mkObj [
    ("module", toJson owner.toString),
    ("declarations", toJson (names.filter fun name => ownerOf env name == owner).size)
  ]
  liftIO <| IO.println (Json.mkObj [
    ("record", toJson "summary"),
    ("declarations", toJson names.size),
    ("module_counts", Json.arr moduleCounts),
    ("modules", toJson (owners.map Name.toString)),
    ("axiom_whitelist", toJson (allowed.map Name.toString)),
    ("status", toJson "PASS")
  ]).compress

end ArnoldSDiffFlowErlangenAudit
