import Mathlib
import InfoGeometry.Tooling.VacuityCritic

open Matrix
open Set

set_option autoImplicit false

namespace PipelineSpec

open InfoGeometry.Tooling.VacuityCritic

/-! Section 1: Pipeline Types -/

inductive EdgeLabel : Type where
  | proved
  | hole
  | pending
deriving DecidableEq

structure DepNode where
  name : String
  fields : List InspectionField
  dependencies : List (String × EdgeLabel)

def DepNode.toDeclaration (n : DepNode) : InspectedDeclaration :=
  ⟨n.name, n.fields⟩

def DepNode.passes (n : DepNode) : Bool :=
  VacuityCritic.passes n.toDeclaration

def DepNode.hasHoleEdge (n : DepNode) : Bool :=
  n.dependencies.any fun (_, label) => label == EdgeLabel.hole

def DepNode.hasInspectionHole (n : DepNode) : Bool :=
  n.passes == false

def DepNode.hasAnyHole (n : DepNode) : Bool :=
  n.hasInspectionHole || n.hasHoleEdge

structure PipelineState where
  nodes : List DepNode
  orientedDAG : List DepNode
  detectedHoles : List String
  verdict : String

lemma passes_ignores_deps (n : DepNode) (deps : List (String × EdgeLabel)) :
    ({ n with dependencies := deps } : DepNode).passes = n.passes := by
  simp [DepNode.passes, DepNode.toDeclaration]

/-! Section 2: Pipeline Stage Signatures -/

def stage_extractDAG (declarations : List String) : List DepNode :=
  declarations.map fun name => { name, fields := [], dependencies := [] }

def stage_orient (dag : List DepNode) : List DepNode :=
  dag.map fun node =>
    let passesNode := node.passes
    { node with
      dependencies := node.dependencies.map fun (dep, _) =>
        (dep, if passesNode then EdgeLabel.proved else EdgeLabel.hole) }

def stage_detect (dag : List DepNode) : List String :=
  dag.filterMap fun node => if node.hasAnyHole then some node.name else none

def stage_verdict (holes : List String) : String :=
  if holes.isEmpty then
    "All declarations pass inspection. No inspection holes detected."
  else
    " Detected " ++ toString holes.length ++ " inspection hole(s): "
      ++ holes.foldl (fun acc h => acc ++ h ++ " ") ""

def runPipeline (declarations : List String) : PipelineState :=
  let dag := stage_extractDAG declarations
  let oriented := stage_orient dag
  let holes := stage_detect oriented
  let verdict := stage_verdict holes
  { nodes := dag, orientedDAG := oriented, detectedHoles := holes, verdict }

/-! Section 3: Stable Bridge Theorem -/

theorem empty_inspection_fails (name : String) :
    VacuityCritic.passes ({ name := name, fields := [] } : InspectedDeclaration) = false := by
  exact VacuityCritic.passes_empty_fields name

lemma length_filter_eq_sum_map_bool {alpha : Type} (l : List alpha) (p : alpha -> Bool) :
    (l.filter p).length = (l.map (fun x => if p x then (1 : Nat) else 0)).sum := by
  induction l with
  | nil => simp
  | cons h t ih =>
      by_cases hp : p h = true
      · simp [hp, ih]
        omega
      · have hp' : p h = false := Bool.eq_false_iff.mpr hp
        simp [hp', ih]

lemma detect_extract_orient_eq_self (declarations : List String) :
    stage_detect (stage_orient (stage_extractDAG declarations)) = declarations := by
  induction declarations with
  | nil =>
      simp [stage_extractDAG, stage_orient, stage_detect]
  | cons head tail ih =>
      simpa [stage_extractDAG, stage_orient, stage_detect, DepNode.hasAnyHole,
        DepNode.hasInspectionHole, DepNode.hasHoleEdge, DepNode.passes,
        DepNode.toDeclaration, VacuityCritic.passes,
        InspectedDeclaration.hasInspectablePayload,
        InspectedDeclaration.fieldsPass] using congrArg (List.cons head) ih

lemma detect_eq_filter_not_pass (declarations : List String) :
    stage_detect (stage_orient (stage_extractDAG declarations)) =
    declarations.filter fun s => not (passes ({ name := s, fields := [] } : InspectedDeclaration)) := by
  rw [detect_extract_orient_eq_self]
  simp [VacuityCritic.passes, InspectedDeclaration.hasInspectablePayload,
    InspectedDeclaration.fieldsPass]

/-! Section 4: Missing Theorem Holes
(spec_total_holes_agrees, tri_facet_unified, exact_coexact_annihilate,
delta_projector_eq_causal_delta) require delta_proj, detect, d, delta, O
from an inspection-detector / scalar-causal module not yet implemented. -/

end PipelineSpec
