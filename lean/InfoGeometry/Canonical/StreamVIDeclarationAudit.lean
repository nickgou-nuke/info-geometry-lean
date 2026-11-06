/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.VandermondeSuperalgebraColorPartitionStatisticsPoset
import Mathlib.Logic.Relation
import Mathlib.Order.Defs.PartialOrder
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Data.Json
import Lean.Elab.Command
import Lean.Parser.Extension

/-!
# Stream VI declaration dependencies and their native reachability order

The seeds are every declaration owned by the five new mathematical modules,
the two added inverse theorems, and named existing mathematical anchors. The
audit follows all project-owned constants appearing in their checked types
and proof or definition values, including private and generated constants.
Native-library dependencies are recorded too, and axiom collection follows
all dependencies transitively.

This is specifically the type/value declaration graph. It does not add the
inductive/constructor/recursor bookkeeping edges that
`ConstantInfo.getUsedConstantsAsSet` supplies in addition to expression
constants. No actual type/value edge is removed, including self-edges; a cycle
causes rejection. An edge points from a prerequisite to its consumer.

After extraction, ordinary command elaboration creates literal declaration
names and edges. Kernel reduction checks that every edge increases its rank
and has endpoints in range. The pure constructor below then equips `Fin N`
with the reflexive-transitive closure of those edges as a native partial
order. The topological ranks are a termination certificate; they are not its
order relation. Independent declarations need not be comparable.

The kernel certificate concerns the generated finite graph. The connection
of its literal names and edges to the currently loaded environment is made
by this inspection command, not by an axiom or a purported internal theorem
about the Lean kernel. Source freshness is a separate build obligation.
-/

open Lean Elab Command

namespace InfoGeometry.Canonical.StreamVIDeclarationAudit

/-- Strictly increasing edge ranks make actual graph reachability a partial
order. This constructor does not replace reachability with the rank order. -/
@[instance_reducible]
def partialOrderOfRankedEdges {n : ℕ} (edges : List (Nat × Nat))
    (hforward : ∀ e ∈ edges, e.1 < e.2) : PartialOrder (Fin n) where
  le a b := Relation.ReflTransGen
    (fun x y : Fin n => (x.val, y.val) ∈ edges) a b
  lt a b :=
    Relation.ReflTransGen (fun x y : Fin n => (x.val, y.val) ∈ edges) a b ∧
      ¬Relation.ReflTransGen (fun x y : Fin n => (x.val, y.val) ∈ edges) b a
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ hab hbc := hab.trans hbc
  le_antisymm a b hab hba := by
    have hmono : ∀ {x y : Fin n},
        Relation.ReflTransGen
          (fun u v : Fin n => (u.val, v.val) ∈ edges) x y →
        x.val ≤ y.val := by
      intro x y hxy
      induction hxy with
      | refl => exact Nat.le_refl _
      | tail _ hstep ih =>
          exact Nat.le_trans ih (Nat.le_of_lt (hforward _ hstep))
    exact Fin.ext (Nat.le_antisymm (hmono hab) (hmono hba))

private def owners : Array Name := #[
  `InfoGeometry.Algebra.Quantum.CubicBraidedNilpotence,
  `InfoGeometry.Algebra.PolynomialAlternantDivisibility,
  `InfoGeometry.Algebra.BlockSchurFactorization,
  `InfoGeometry.Canonical.CattoGurseyMomentCurve,
  `InfoGeometry.Canonical.VandermondeSuperalgebraColorPartitionStatisticsPoset
]

private def addedInverseDeclarations : Array Name := #[
  `InfoGeometry.Algebra.OperatorCyclotomicParafermions.ringInverse_one_sub_eq_operatorGeometricSum,
  `InfoGeometry.Algebra.OperatorCyclotomicParafermions.ringInverse_one_sub_eq_sum
]

private def anchors : Array Name := #[
  `InfoGeometry.Algebra.LinearInvolutionProjectors.plus_add_minus,
  `InfoGeometry.Algebra.LinearInvolutionProjectors.plus_sub_minus,
  `InfoGeometry.Algebra.LinearInvolutionProjectors.plus_comp_plus,
  `InfoGeometry.Algebra.LinearInvolutionProjectors.minus_comp_minus,
  `InfoGeometry.Algebra.LinearInvolutionProjectors.plus_comp_minus,
  `InfoGeometry.Algebra.LinearInvolutionProjectors.minus_comp_plus,
  `InfoGeometry.Physics.Algebra.projPos_idempotent,
  `InfoGeometry.Physics.Algebra.projNeg_idempotent,
  `InfoGeometry.Physics.Algebra.projZero_idempotent,
  `InfoGeometry.Physics.Algebra.proj_sum_eq_id,
  `InfoGeometry.Physics.Algebra.projPos_sub_projNeg,
  `InfoGeometry.Physics.Algebra.projPos_mul_projNeg_eq_zero,
  `InfoGeometry.Physics.Algebra.projNeg_mul_projPos_eq_zero,
  `InfoGeometry.Physics.Algebra.projPos_mul_projZero_eq_zero,
  `InfoGeometry.Physics.Algebra.projZero_mul_projPos_eq_zero,
  `InfoGeometry.Physics.Algebra.projNeg_mul_projZero_eq_zero,
  `InfoGeometry.Physics.Algebra.projZero_mul_projNeg_eq_zero,
  `InfoGeometry.Canonical.PeirceV4GrandCanonicalFourierBridge.v4Fourier_sector_inversion,
  `InfoGeometry.Canonical.CattoGurseyBlockGrading.supertrace_identity_6_21,
  `InfoGeometry.Canonical.GLSupermatrixGradedLie.supertrace_superbracket_eq_zero,
  `InfoGeometry.Projective.ExteriorBladeIncidence.ιMulti_ne_zero_of_linearIndependent
]

private def allowedAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

private def ownerOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

private def projectPrefix (n : Name) : Bool :=
  Name.isPrefixOf `InfoGeometry n || Name.isPrefixOf `InfoGeometryCore n

/-- Module ownership includes private declarations and project declarations
whose public namespace is not itself prefixed by `InfoGeometry`. -/
private def isProjectConstant (env : Environment) (n : Name) : Bool :=
  projectPrefix n || projectPrefix (ownerOf env n)

private def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

/-- Only constants in the checked type and, when present, actual value. -/
private def typeValueDependencies (info : ConstantInfo) : Array Name :=
  let deps := info.type.getUsedConstantsAsSet
  let deps := match info.value? (allowOpaque := true) with
    | some value => deps ++ value.getUsedConstantsAsSet
    | none => deps
  deps.toArray.qsort Name.lt

private def validateDeclaration (env : Environment) (name : Name) :
    CommandElabM (Array Name) := do
  let some info := env.checked.get.find? name |
    throwError "Missing checked declaration {name}"
  if info.isUnsafe || info.isPartial || kindOf info == "axiom" then
    throwError "Rejected declaration {name}: unsafe, partial, or local axiom"
  let axioms ← collectAxioms name
  for axiomName in axioms do
    if !allowedAxioms.contains axiomName then
      throwError "Rejected axiom {axiomName} in declaration {name}"
  return axioms

/-- Parse and elaborate an ordinary Lean command; no unchecked declaration
insertion or native decision procedure is used. -/
private def elabLiteralCommand (source : String) : CommandElabM Unit := do
  match Lean.Parser.runParserCategory (← getEnv) `command source with
  | .error error => throwError "Generated graph declaration did not parse: {error}"
  | .ok command =>
      elabCommand command
      if (← MonadLog.hasErrors) then
        throwError "Generated graph declaration logged an elaboration error"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
run_cmd do
  let env := (← getEnv).setExporting false
  let mut names : Array Name := #[]
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    if owners.contains (ownerOf env name) then
      names := names.push name
      seen := seen.insert name
  for owner in owners do
    if !(names.any fun name => ownerOf env name == owner) then
      throwError "No declarations found in requested owner module {owner}"
  for name in addedInverseDeclarations ++ anchors do
    if (env.checked.get.find? name).isNone then
      throwError "Requested named anchor is missing: {name}"
    if !seen.contains name then
      names := names.push name
      seen := seen.insert name
  let seeds := names.qsort Name.lt
  let seedSet := seen

  -- Extend the seed set through every actual project type/value dependency.
  let mut dependencyTable : NameMap (Array Name) := {}
  let mut cursor := 0
  while cursor < names.size do
    let name := names[cursor]!
    cursor := cursor + 1
    let some info := env.checked.get.find? name |
      throwError "Missing checked dependency {name}"
    let dependencies := typeValueDependencies info
    dependencyTable := dependencyTable.insert name dependencies
    for dependency in dependencies do
      if isProjectConstant env dependency && !seen.contains dependency then
        names := names.push dependency
        seen := seen.insert dependency
  names := names.qsort Name.lt

  -- A topological enumeration assigns ranks without changing the edge set.
  let mut pending := names
  let mut ordered : Array Name := #[]
  let mut placed : NameSet := {}
  for _ in [:names.size] do
    if pending.isEmpty then
      break
    let before := ordered.size
    let mut remaining : Array Name := #[]
    for name in pending do
      let some dependencies := dependencyTable.find? name |
        throwError "No dependency record for {name}"
      let projectDependencies := dependencies.filter seen.contains
      if projectDependencies.all placed.contains then
        ordered := ordered.push name
        placed := placed.insert name
      else
        remaining := remaining.push name
    if ordered.size == before then
      throwError "Cycle in the project type/value declaration graph: {remaining}"
    pending := remaining
  if !pending.isEmpty then
    throwError "Incomplete project declaration dependency order"

  let mut rank : NameMap Nat := {}
  for i in [:ordered.size] do
    rank := rank.insert ordered[i]! i
  let mut edges : Array (Nat × Nat) := #[]
  let mut theoremCount := 0
  for i in [:ordered.size] do
    let name := ordered[i]!
    let some info := env.checked.get.find? name |
      throwError "Missing checked declaration {name}"
    let axioms ← validateDeclaration env name
    let some dependencies := dependencyTable.find? name |
      throwError "No dependency record for {name}"
    let projectDependencies := dependencies.filter seen.contains
    let mut dependencyIndices : Array Nat := #[]
    for dependency in projectDependencies do
      let some j := rank.find? dependency |
        throwError "Unranked project dependency {dependency} of {name}"
      if i ≤ j then
        throwError "Dependency edge is not forward: {dependency} -> {name}"
      dependencyIndices := dependencyIndices.push j
      edges := edges.push (j, i)
    if kindOf info == "theorem" then
      theoremCount := theoremCount + 1
    liftIO <| IO.println (Json.mkObj [
      ("record", toJson "declaration"),
      ("index", toJson i),
      ("name", toJson name.toString),
      ("module", toJson (ownerOf env name).toString),
      ("kind", toJson (kindOf info)),
      ("seed", toJson (seedSet.contains name)),
      ("unsafe", toJson info.isUnsafe),
      ("partial", toJson info.isPartial),
      ("axioms", toJson (axioms.map Name.toString)),
      ("dependencies", toJson (dependencies.map Name.toString)),
      ("project_dependencies", toJson (projectDependencies.map Name.toString)),
      ("project_dependency_indices", toJson dependencyIndices)
    ]).compress

  -- String.quote emits Lean string-literal syntax for the declaration names.
  let nameLiterals := String.intercalate ", "
    (ordered.toList.map fun name => name.toString.quote)
  let edgeLiterals := String.intercalate ", "
    (edges.toList.map fun e => s!"({e.1}, {e.2})")
  let count := toString ordered.size
  elabLiteralCommand
    ("def declarationNames : Array String := #[" ++ nameLiterals ++ "]")
  elabLiteralCommand
    ("def dependencyEdges : List (Nat × Nat) := [" ++ edgeLiterals ++ "]")
  elabLiteralCommand
    "theorem dependencyEdges_forward : ∀ e ∈ dependencyEdges, e.1 < e.2 := by decide"
  elabLiteralCommand
    ("theorem declarationNames_size : declarationNames.size = " ++ count ++
      " := by decide")
  elabLiteralCommand
    ("theorem dependencyEdges_bounded : ∀ e ∈ dependencyEdges, e.1 < " ++ count ++
      " ∧ e.2 < " ++ count ++ " := by decide")
  elabLiteralCommand
    ("@[instance_reducible] def declarationPartialOrder : PartialOrder (Fin " ++ count ++ ") := " ++
      "partialOrderOfRankedEdges (n := " ++ count ++ ") " ++
      "dependencyEdges dependencyEdges_forward")
  elabLiteralCommand
    ("theorem declarationPartialOrder_le_iff (i j : Fin " ++ count ++ ") : " ++
      "declarationPartialOrder.le i j ↔ Relation.ReflTransGen " ++
      "(fun a b : Fin " ++ count ++ " => (a.val, b.val) ∈ dependencyEdges) i j := Iff.rfl")

  -- Failed elaboration cannot be hidden by an informational success record.
  -- Every generated declaration must exist and pass the same axiom audit.
  let certificateDeclarations : Array Name := #[
    `InfoGeometry.Canonical.StreamVIDeclarationAudit.partialOrderOfRankedEdges,
    `InfoGeometry.Canonical.StreamVIDeclarationAudit.declarationNames,
    `InfoGeometry.Canonical.StreamVIDeclarationAudit.dependencyEdges,
    `InfoGeometry.Canonical.StreamVIDeclarationAudit.dependencyEdges_forward,
    `InfoGeometry.Canonical.StreamVIDeclarationAudit.declarationNames_size,
    `InfoGeometry.Canonical.StreamVIDeclarationAudit.dependencyEdges_bounded,
    `InfoGeometry.Canonical.StreamVIDeclarationAudit.declarationPartialOrder,
    `InfoGeometry.Canonical.StreamVIDeclarationAudit.declarationPartialOrder_le_iff
  ]
  let certificateEnv := (← getEnv).setExporting false
  for name in certificateDeclarations do
    let axioms ← validateDeclaration certificateEnv name
    liftIO <| IO.println (Json.mkObj [
      ("record", toJson "graph_certificate"),
      ("name", toJson name.toString),
      ("axioms", toJson (axioms.map Name.toString))
    ]).compress

  if (← MonadLog.hasErrors) then
    throwError "Declaration audit logged an error; refusing a success summary"
  liftIO <| IO.println (Json.mkObj [
    ("record", toJson "summary"),
    ("graph", toJson "project type/value declaration dependencies"),
    ("seeds", toJson (seeds.map Name.toString)),
    ("declarations", toJson names.size),
    ("theorems", toJson theoremCount),
    ("project_dependency_edges", toJson edges.size),
    ("modules", toJson (owners.map Name.toString)),
    ("added_inverse_declarations", toJson (addedInverseDeclarations.map Name.toString)),
    ("named_existing_anchors", toJson (anchors.map Name.toString)),
    ("axiom_whitelist", toJson (allowedAxioms.map Name.toString)),
    ("dependency_order", toJson (ordered.map Name.toString)),
    ("dependency_edges", toJson edges),
    ("edge_direction", toJson "prerequisite -> consumer"),
    ("partial_order_relation", toJson "Relation.ReflTransGen of literal dependencyEdges"),
    ("graph_certificate_declarations", toJson (certificateDeclarations.map Name.toString)),
    ("acyclic", toJson true),
    ("status", toJson "PASS")
  ]).compress

end InfoGeometry.Canonical.StreamVIDeclarationAudit
