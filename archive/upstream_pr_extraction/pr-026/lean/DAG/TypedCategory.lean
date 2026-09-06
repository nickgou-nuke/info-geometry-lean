import Lean
import Lean.Data.Json
import DAG.Basic
import DAG.JsonInstances
import InfoGeometry.Meta.Architecture

open Lean
open InfoGeometry.Meta

namespace DAG

instance : Inhabited DAG.EdgeKind := ⟨DAG.EdgeKind.value⟩

/-- Shared schema version for typed declaration/process category exports. -/
def schemaVersion : Nat := 4

instance : ToJson RepDepth where
  toJson
    | .count => "count"
    | .projective => "projective"
    | .operator => "operator"
    | .krein => "krein"
    | .transport => "transport"
    | .thermo => "thermo"

inductive DependencyRole
  | head
  | requiredArg
  | transportArg
  | witness
  | closureSupport
  | ornament
  | remoteSupport
  | unknown
  deriving Repr, BEq, Inhabited, ToJson, Hashable

inductive BoundaryClass
  | internal
  | localInterface
  | bridge
  | capstone
  | mixed
  | unclear
  deriving Repr, BEq, Inhabited, ToJson, Hashable

inductive LocalityClass
  | local
  | adjacent
  | remote
  | mixed
  deriving Repr, BEq, Inhabited, ToJson, Hashable

inductive NormalizationClass
  | definitional
  | propositional
  | structural
  deriving Repr, BEq, Inhabited, ToJson, Hashable

inductive CanonicalityClass
  | stableSpine
  | capstone
  | derived
  deriving Repr, BEq, Inhabited, ToJson, Hashable

inductive PolarityClass
  | neutral
  | sameLayer
  | descending
  | remote
  | mixed
  | regressive
  deriving Repr, BEq, Inhabited, ToJson, Hashable

inductive DerivationalRole
  | vertical
  | primitiveTranslator
  | capstoneCoherence
  | violation
  deriving Repr, BEq, Inhabited, ToJson, Hashable

inductive DefectKind
  | remoteAttachment
  | failedLocalFactorization
  | unresolvedComparison
  | illicitBoundaryCrossing
  | mixedPolarity
  | regressiveFlow
  | typeOnlySupport
  | boundaryBypass
  | unclearPolarity
  deriving Repr, BEq, Inhabited, ToJson, Hashable

inductive FlowProvenanceKind
  | directObserved
  | boundedComposite
  deriving Repr, BEq, Inhabited, ToJson, Hashable

inductive EdgeUse
  | typeOnly
  | valueOnly
  | both
  deriving Repr, BEq, Inhabited, ToJson, Hashable

/-- Theorem-role classification for declaration-level typed DAG objects. -/
inductive DeclNodeRole
  | owner
  | translator
  | coherence
  | capstone
  | infrastructure
  deriving Repr, BEq, Inhabited, ToJson, Hashable

/-- Canonical morphism kinds for the finite typed declaration/process category. -/
inductive DeclMorphismKind
  | dependency
  | translator
  | coherence
  | obstruction
  | quotientWitness
  deriving Repr, BEq, Inhabited, ToJson, Hashable

structure FeatureBundle where
  layer : String
  layerNat : Nat
  locality : LocalityClass
  normalization : NormalizationClass
  canonicality : CanonicalityClass
  polarity : PolarityClass
  deriving Repr, BEq, Inhabited, ToJson

structure WeightedName where
  name : Name
  weight : Nat
  deriving Repr, Inhabited, ToJson

structure DirectEdgeEvidence where
  src : Name
  dst : Name
  edgeUse : EdgeUse
  srcDepthNat? : Option Nat := none
  dstDepthNat? : Option Nat := none
  srcModule : String
  dstModule : String
  deriving Repr, Inhabited

structure FeatureInput where
  dep : Name
  feature : FeatureBundle
  deriving Repr, Inhabited, ToJson

structure FlowEdge where
  schemaVersion : Nat := schemaVersion
  src : Name
  dst : Name
  edgeUse : EdgeUse
  edgeKind : DAG.EdgeKind
  provenanceKind : FlowProvenanceKind
  inferredRole : DependencyRole
  inferredBoundary : BoundaryClass
  depthHint? : Option Nat
  inferredPolarity : PolarityClass
  srcFeature : FeatureBundle
  dstFeature : FeatureBundle
  defectTags : Array DefectKind
  deriving Repr, Inhabited, ToJson

structure ProcessEvent where
  schemaVersion : Nat := schemaVersion
  node : Name
  module : String
  kind : String
  role : DerivationalRole
  boundaryClass : BoundaryClass
  directDeps : Array Name
  directValueDeps : Array Name
  directTypeDeps : Array Name
  closureDeps : Array Name
  featureInputs : Array FeatureInput
  featureIn : Array FeatureBundle
  featureOut : Array FeatureBundle
  headCandidates : Array WeightedName
  supportCandidates : Array Name
  comparisonCandidates : Array Name
  novelty : Nat
  deriving Repr, Inhabited, ToJson

structure PathStep where
  schemaVersion : Nat := schemaVersion
  src : Name
  dst : Name
  edgeUse : EdgeUse
  edgeKind : DAG.EdgeKind
  inferredRole : DependencyRole
  provenanceKind : FlowProvenanceKind
  inferredBoundary : BoundaryClass
  boundaryCrossing : Bool
  featureIn : FeatureBundle
  featureOut : FeatureBundle
  deriving Repr, Inhabited, ToJson

structure Defect where
  kind : DefectKind
  atStep : Nat
  cost : Nat
  witness : Option Name := none
  deriving Repr, Inhabited, ToJson

structure LawfulPathCandidate where
  schemaVersion : Nat := schemaVersion
  src : Name
  dst : Name
  steps : Array PathStep
  totalDefectCost : Nat
  defects : Array Defect
  sharedComparisonCandidates : Array Name
  deriving Repr, Inhabited, ToJson

structure DefectRow where
  schemaVersion : Nat := schemaVersion
  locus : String
  src : Name
  dst : Name
  defect : Defect
  deriving Repr, Inhabited, ToJson

structure DeclFlowSummary where
  depth : RepDepth
  kind : String
  capstone : Bool
  directEvidence : Array DirectEdgeEvidence
  feature : FeatureBundle
  deriving Inhabited

structure ComparisonGroupKey where
  role : DerivationalRole
  layerNat : Nat
  boundaryClass : BoundaryClass
  deriving Repr, BEq, Inhabited, Hashable

/-- Lean-owned typed object in the declaration/process category. -/
structure TypedDeclObject where
  decl : Name
  module : String
  kind : String
  depth : RepDepth
  role : DeclNodeRole
  boundary : BoundaryClass
  capstone : Bool
  feature : FeatureBundle
  deriving Repr, Inhabited, ToJson

/-- Lean-owned typed morphism in the declaration/process category. -/
structure TypedDeclMorphism where
  schemaVersion : Nat := schemaVersion
  src : Name
  dst : Name
  kind : DeclMorphismKind
  role : DependencyRole
  provenance : FlowProvenanceKind
  boundary : BoundaryClass
  polarity : PolarityClass
  edgeUse : EdgeUse
  edgeKind : DAG.EdgeKind
  srcDepth? : Option Nat := none
  dstDepth? : Option Nat := none
  defects : Array DefectKind := #[]
  deriving Repr, Inhabited, ToJson

/-- Finite compatible cone over typed declaration/process morphisms. -/
structure CompatibleCone where
  schemaVersion : Nat := schemaVersion
  apex : TypedDeclObject
  legs : Array TypedDeclMorphism
  sharedComparisons : Array Name := #[]
  deriving Repr, Inhabited, ToJson

/-- Lawful cone: a compatible cone plus explicit bounded defect accounting. -/
structure LawfulCone where
  base : CompatibleCone
  totalDefectCost : Nat
  defects : Array Defect := #[]
  deriving Repr, Inhabited, ToJson

/-- Explicit finite composite path in the typed declaration/process category. -/
structure TypedCompositePath where
  schemaVersion : Nat := schemaVersion
  src : Name
  dst : Name
  steps : Array TypedDeclMorphism
  deriving Repr, Inhabited, ToJson

/-- Lawful finite composite path in the typed declaration/process category. -/
structure LawfulTypedCompositePath where
  base : TypedCompositePath
  totalDefectCost : Nat
  defects : Array Defect := #[]
  sharedComparisonCandidates : Array Name := #[]
  deriving Repr, Inhabited, ToJson

/-- Translate process-flow derivational roles into typed declaration-node roles. -/
def DeclNodeRole.ofDerivationalRole : DerivationalRole → DeclNodeRole
  | .vertical => .owner
  | .primitiveTranslator => .translator
  | .capstoneCoherence => .coherence
  | .violation => .infrastructure

/--
Canonical typed object extracted from a process event.

This is the declaration-level object authority for the finite typed
declaration/process category: the exporter computes the process event, and this
bridge turns that event into the canonical object row without Python-side role
guessing.
-/
def ProcessEvent.toTypedDeclObject (ev : ProcessEvent) : TypedDeclObject :=
  let feature := ev.featureOut[0]!
  let role :=
    if ev.boundaryClass == .capstone then .capstone
    else DeclNodeRole.ofDerivationalRole ev.role
  { decl := ev.node
    module := ev.module
    kind := ev.kind
    depth := RepDepth.ofNat feature.layerNat
    role := role
    boundary := ev.boundaryClass
    capstone := ev.boundaryClass == .capstone
    feature := feature }

/--
Typed object extracted from a declaration-flow summary together with the
process-level role and boundary classification computed by the exporter.
-/
def DeclFlowSummary.toTypedDeclObject
    (decl : Name)
    (module : String)
    (role : DerivationalRole)
    (boundary : BoundaryClass) :
    DeclFlowSummary → TypedDeclObject
  | summary =>
      let nodeRole :=
        if summary.capstone || boundary == .capstone then .capstone
        else DeclNodeRole.ofDerivationalRole role
      { decl := decl
        module := module
        kind := summary.kind
        depth := summary.depth
        role := nodeRole
        boundary := boundary
        capstone := summary.capstone || boundary == .capstone
        feature := summary.feature }

/--
Canonical finite semantic morphism rows induced by a process event.

These rows are the Lean-owned source of the higher-level graph semantics that
Python currently renames into `translator_of`, `coheres_with`, and `obstructs`.
-/
def ProcessEvent.semanticTypedMorphisms (ev : ProcessEvent) : Array TypedDeclMorphism :=
  let mkRows
      (dsts : Array Name)
      (kind : DeclMorphismKind)
      (boundary : BoundaryClass)
      (polarity : PolarityClass) : Array TypedDeclMorphism :=
    dsts.map fun dst =>
      { src := ev.node
        dst := dst
        kind := kind
        role :=
          match kind with
          | .translator => .transportArg
          | .coherence => .closureSupport
          | .obstruction => .remoteSupport
          | .quotientWitness => .witness
          | .dependency => .requiredArg
        provenance := .boundedComposite
        boundary := boundary
        polarity := polarity
        edgeUse := .both
        edgeKind := .value }
  mkRows ev.supportCandidates .translator ev.boundaryClass .sameLayer ++
    mkRows ev.comparisonCandidates .coherence ev.boundaryClass .sameLayer ++
    mkRows ev.closureDeps .obstruction .bridge .remote

/--
Refine a direct flow-edge row into the canonical typed morphism vocabulary.

The morphism kind is inferred from Lean-side edge role/boundary data only; no
Python renaming layer is consulted.
-/
def FlowEdge.typedKind (edge : FlowEdge) : DeclMorphismKind :=
  match edge.inferredRole with
  | .transportArg => .translator
  | .closureSupport => .coherence
  | .witness => .quotientWitness
  | .remoteSupport => .obstruction
  | _ =>
      if edge.inferredBoundary == .bridge && edge.inferredPolarity == .remote then
        .obstruction
      else
        .dependency

/--
Bridge a `FlowEdge` export row into the canonical typed morphism vocabulary.
This is definitional: no new semantics are invented here.
-/
def FlowEdge.toTypedDeclMorphism (edge : FlowEdge) : TypedDeclMorphism :=
  { src := edge.src
    dst := edge.dst
    kind := edge.typedKind
    role := edge.inferredRole
    provenance := edge.provenanceKind
    boundary := edge.inferredBoundary
    polarity := edge.inferredPolarity
    edgeUse := edge.edgeUse
    edgeKind := edge.edgeKind
    srcDepth? := edge.srcFeature.layerNat
    dstDepth? := edge.dstFeature.layerNat
    defects := edge.defectTags }

/--
Refine a path step into the canonical typed morphism vocabulary.

This mirrors `FlowEdge.typedKind` using the information preserved in the
bounded path witness itself.
-/
def PathStep.typedKind (step : PathStep) : DeclMorphismKind :=
  match step.inferredRole with
  | .transportArg => .translator
  | .closureSupport => .coherence
  | .witness => .quotientWitness
  | .remoteSupport => .obstruction
  | _ =>
      if step.inferredBoundary == .bridge && step.featureOut.polarity == .remote then
        .obstruction
      else
        .dependency

/--
Bridge a `LawfulPathCandidate` export row into the canonical typed path vocabulary.
The step morphisms are kept finite and explicit.
-/
def LawfulPathCandidate.toLawfulTypedCompositePath : LawfulPathCandidate → LawfulTypedCompositePath
  | path =>
      let typedSteps := path.steps.map fun step =>
        { src := step.src
          dst := step.dst
          kind := step.typedKind
          role := step.inferredRole
          provenance := step.provenanceKind
          boundary := step.inferredBoundary
          polarity := step.featureOut.polarity
          edgeUse := step.edgeUse
          edgeKind := step.edgeKind
          srcDepth? := step.featureIn.layerNat
          dstDepth? := step.featureOut.layerNat
          defects := #[] }
      { base :=
          { src := path.src
            dst := path.dst
            steps := typedSteps }
        totalDefectCost := path.totalDefectCost
        defects := path.defects
        sharedComparisonCandidates := path.sharedComparisonCandidates }

/-- Canonical finite compatible cone induced by a process event. -/
def ProcessEvent.toCompatibleCone (ev : ProcessEvent) : CompatibleCone :=
  { apex := ev.toTypedDeclObject
    legs := ev.semanticTypedMorphisms
    sharedComparisons := ev.comparisonCandidates }

/--
Lawful cone induced by a process event and bounded path witnesses.

The defect accounting is aggregated only from those lawful paths whose
destination is one of the semantic legs exported for the cone.
-/
def ProcessEvent.toLawfulCone
    (paths : Array LawfulPathCandidate)
    (ev : ProcessEvent) : LawfulCone :=
  let base := ev.toCompatibleCone
  let legDsts := base.legs.map (·.dst)
  let relevantPaths := paths.filter fun path => path.src == ev.node && legDsts.contains path.dst
  let totalDefectCost := relevantPaths.foldl (init := 0) fun n path => n + path.totalDefectCost
  let defects := relevantPaths.foldl (init := #[]) fun acc path => acc ++ path.defects
  { base := base
    totalDefectCost := totalDefectCost
    defects := defects }

end DAG
