import Lean
import Lean.Data.Json
import DAG.Basic
import DAG.JsonInstances
import InfoGeometry.Meta.Architecture

open Lean
open InfoGeometry.Meta

namespace DAG

instance : Inhabited DAG.EdgeKind := ⟨DAG.EdgeKind.value⟩

private def schemaVersion : Nat := 4

inductive DependencyRole
  | head
  | requiredArg
  | transportArg
  | witness
  | closureSupport
  | ornament
  | remoteSupport
  | unknown
  deriving Repr, BEq, Inhabited, ToJson

inductive BoundaryClass
  | internal
  | localInterface
  | bridge
  | capstone
  | mixed
  | unclear
  deriving Repr, BEq, Inhabited, ToJson

inductive LocalityClass
  | local
  | adjacent
  | remote
  | mixed
  deriving Repr, BEq, Inhabited, ToJson

inductive NormalizationClass
  | definitional
  | propositional
  | structural
  deriving Repr, BEq, Inhabited, ToJson

inductive CanonicalityClass
  | stableSpine
  | capstone
  | derived
  deriving Repr, BEq, Inhabited, ToJson

inductive PolarityClass
  | neutral
  | sameLayer
  | descending
  | remote
  | mixed
  | regressive
  deriving Repr, BEq, Inhabited, ToJson

inductive DerivationalRole
  | vertical
  | primitiveTranslator
  | capstoneCoherence
  | violation
  deriving Repr, BEq, Inhabited, ToJson

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
  deriving Repr, BEq, Inhabited, ToJson

inductive FlowProvenanceKind
  | directObserved
  | boundedComposite
  deriving Repr, BEq, Inhabited, ToJson

inductive EdgeUse
  | typeOnly
  | valueOnly
  | both
  deriving Repr, BEq, Inhabited, ToJson

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

private def dottedName (s : String) : Name :=
  (s.splitOn ".").foldl (init := Name.anonymous) fun acc part =>
    if part.isEmpty then acc else Name.str acc part

private def moduleNameFor (env : Environment) (declName : Name) : String :=
  match env.getModuleIdxFor? declName with
  | some midx =>
      let mods : List Name := env.header.moduleNames.toList
      let idx : Nat := midx.toNat
      if h : idx < mods.length then
        toString (mods.get ⟨idx, h⟩)
      else
        "<unknown>"
  | none =>
      toString env.mainModule

private def kindString : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .quotInfo _ => "quot"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

private def depthLabel : RepDepth → String
  | .count => "count"
  | .projective => "projective"
  | .operator => "operator"
  | .krein => "krein"
  | .transport => "transport"
  | .thermo => "thermo"

private def normalizationClassOf (kind : String) : NormalizationClass :=
  match kind with
  | "theorem" => .propositional
  | "def" => .definitional
  | "opaque" => .definitional
  | _ => .structural

private def sortNames (xs : Array Name) : Array Name :=
  xs.qsort fun a b => toString a < toString b

private def uniqueNames (xs : Array Name) : Array Name := Id.run do
  let mut out := #[]
  for x in xs do
    if !out.contains x then
      out := out.push x
  return sortNames out

private def uniqueNats (xs : Array Nat) : Array Nat := Id.run do
  let mut out := #[]
  for x in xs do
    if !out.contains x then
      out := out.push x
  return out.qsort (· < ·)

private def uniqueFeatures (xs : Array FeatureBundle) : Array FeatureBundle := Id.run do
  let mut out := #[]
  for x in xs do
    if !out.contains x then
      out := out.push x
  return out

private def lowerDepths (targetDepthNat : Nat) (depths : Array Nat) : Array Nat :=
  (depths.filter fun d => d < targetDepthNat).qsort (· < ·)

private def nearestLowerDepth? (targetDepthNat : Nat) (depths : Array Nat) : Option Nat :=
  let lowers := lowerDepths targetDepthNat depths
  if lowers.isEmpty then none else some lowers[lowers.size - 1]!

private def reachesPrev (targetDepthNat : Nat) (depths : Array Nat) : Bool :=
  targetDepthNat > 0 && depths.contains (targetDepthNat - 1)

private def reachesBelowPrev (targetDepthNat : Nat) (depths : Array Nat) : Bool :=
  depths.any fun d => d + 1 < targetDepthNat

private def reachesAbove (targetDepthNat : Nat) (depths : Array Nat) : Bool :=
  depths.any fun d => targetDepthNat < d

private def derivationalRoleOf (capstone : Bool) (targetDepthNat : Nat) (directDepDepthNats : Array Nat) : DerivationalRole :=
  if capstone then
    .capstoneCoherence
  else if reachesAbove targetDepthNat directDepDepthNats || reachesBelowPrev targetDepthNat directDepDepthNats then
    .violation
  else if reachesPrev targetDepthNat directDepDepthNats then
    .primitiveTranslator
  else
    .vertical

private def localityClassOf (targetDepthNat : Nat) (directDepDepthNats : Array Nat) : LocalityClass :=
  let above := reachesAbove targetDepthNat directDepDepthNats
  let below := reachesBelowPrev targetDepthNat directDepDepthNats
  let prev := reachesPrev targetDepthNat directDepDepthNats
  if above || (below && prev) then .mixed
  else if below then .remote
  else if prev then .adjacent
  else .local

private def polarityClassOf (targetDepthNat : Nat) (directDepDepthNats : Array Nat) : PolarityClass :=
  let above := reachesAbove targetDepthNat directDepDepthNats
  let below := reachesBelowPrev targetDepthNat directDepDepthNats
  let prev := reachesPrev targetDepthNat directDepDepthNats
  if above then .regressive
  else if below && prev then .mixed
  else if below then .remote
  else if prev then .descending
  else if directDepDepthNats.contains targetDepthNat then .sameLayer
  else .neutral

private def canonicalityClassOf (capstone : Bool) : CanonicalityClass :=
  if capstone then .capstone else .stableSpine

private def boundaryClassOf (role : DerivationalRole) (locality : LocalityClass) : BoundaryClass :=
  match role, locality with
  | .capstoneCoherence, _ => .capstone
  | .primitiveTranslator, _ => .bridge
  | .vertical, .local => .internal
  | .vertical, .adjacent => .localInterface
  | .violation, .mixed => .mixed
  | .violation, .remote => .mixed
  | .violation, _ => .unclear
  | _, .mixed => .mixed
  | _, _ => .unclear

private def mergeEdgeUse (a b : EdgeUse) : EdgeUse :=
  match a, b with
  | .both, _ => .both
  | _, .both => .both
  | .valueOnly, .typeOnly => .both
  | .typeOnly, .valueOnly => .both
  | .valueOnly, .valueOnly => .valueOnly
  | .typeOnly, .typeOnly => .typeOnly

private def edgeUseOfKind (kind : DAG.EdgeKind) : EdgeUse :=
  match kind with
  | .type => .typeOnly
  | .value => .valueOnly

private def edgeUseHasType : EdgeUse → Bool
  | .typeOnly | .both => true
  | .valueOnly => false

private def edgeUseHasValue : EdgeUse → Bool
  | .valueOnly | .both => true
  | .typeOnly => false

private def dominantEdgeKindOf (edgeUse : EdgeUse) : DAG.EdgeKind :=
  if edgeUseHasValue edgeUse then .value else .type

private def directEdgeEvidenceOf (env : Environment) (declName : Name) : Array DirectEdgeEvidence := Id.run do
  let mut out : Array DirectEdgeEvidence := #[]
  let srcModule := moduleNameFor env declName
  let srcDepthNat? := (repDepth? env declName).map RepDepth.toNat
  if let some ci := env.find? declName then
    for (dep, kind) in DAG.edgesFromConstantInfo ci do
      if let some depDepth := repDepth? env dep then
        let mut replaced := false
        let mut next := #[]
        for ev in out do
          if ev.dst == dep then
            replaced := true
            next := next.push { ev with edgeUse := mergeEdgeUse ev.edgeUse (edgeUseOfKind kind) }
          else
            next := next.push ev
        if !replaced then
          next := next.push {
            src := declName
            dst := dep
            edgeUse := edgeUseOfKind kind
            srcDepthNat? := srcDepthNat?
            dstDepthNat? := some depDepth.toNat
            srcModule := srcModule
            dstModule := moduleNameFor env dep
          }
        out := next
  return out.qsort fun a b => toString a.dst < toString b.dst

private def closureTaggedDependencies (env : Environment) (declName : Name) : Array Name := Id.run do
  let mut out := #[]
  for dep in transitivelyUsedConstants env declName do
    if dep != declName && (repDepth? env dep).isSome then
      out := out.push dep
  return uniqueNames out

private def featureBundleOf
    (depth : RepDepth)
    (kind : String)
    (capstone : Bool)
    (targetDepthNat : Nat)
    (directDepDepthNats : Array Nat) : FeatureBundle :=
  {
    layer := depthLabel depth
    layerNat := targetDepthNat
    locality := localityClassOf targetDepthNat directDepDepthNats
    normalization := normalizationClassOf kind
    canonicality := canonicalityClassOf capstone
    polarity := polarityClassOf targetDepthNat directDepDepthNats
  }

private def edgePolarityOf
    (srcFeature dstFeature : FeatureBundle)
    (role : DependencyRole) : PolarityClass :=
  if srcFeature.polarity == .mixed || dstFeature.polarity == .mixed then
    .mixed
  else if dstFeature.layerNat > srcFeature.layerNat then
    .regressive
  else if dstFeature.layerNat + 1 < srcFeature.layerNat then
    if role == .remoteSupport then .remote else .mixed
  else if dstFeature.layerNat + 1 == srcFeature.layerNat then
    .descending
  else if dstFeature.layerNat == srcFeature.layerNat then
    .sameLayer
  else
    .neutral

private def edgeBoundaryOf
    (capstone : Bool)
    (srcFeature dstFeature : FeatureBundle)
    (role : DependencyRole) : BoundaryClass :=
  if capstone then
    .capstone
  else if role == .transportArg then
    .bridge
  else if srcFeature.polarity == .mixed || dstFeature.polarity == .mixed then
    .mixed
  else if srcFeature.layerNat == dstFeature.layerNat then
    .internal
  else if srcFeature.layerNat == dstFeature.layerNat + 1 then
    .localInterface
  else
    .unclear

private def dependencyRoleOf
    (targetDepthNat : Nat)
    (depDepthNat : Nat)
    (edgeUse : EdgeUse) : DependencyRole :=
  if targetDepthNat < depDepthNat then
    .remoteSupport
  else if depDepthNat + 1 < targetDepthNat then
    .remoteSupport
  else if depDepthNat + 1 = targetDepthNat then
    if edgeUseHasValue edgeUse then .transportArg else .requiredArg
  else
    if edgeUseHasValue edgeUse then .head else .witness

private def headWeightOf (role : DependencyRole) (edgeUse : EdgeUse) : Nat :=
  if edgeUseHasValue edgeUse then
    match role with
    | .head => 100
    | .transportArg => 95
    | .closureSupport => 65
    | .remoteSupport => 5
    | .ornament => 20
    | .unknown => 1
    | _ => 25
  else
    match role with
    | .requiredArg => 75
    | .witness => 45
    | .remoteSupport => 5
    | .ornament => 20
    | .unknown => 1
    | _ => 10

private def defectSeverity : DefectKind → Nat
  | .illicitBoundaryCrossing => 5
  | .regressiveFlow => 5
  | .boundaryBypass => 4
  | .remoteAttachment => 3
  | .failedLocalFactorization => 3
  | .unresolvedComparison => 1
  | .mixedPolarity => 2
  | .unclearPolarity => 2
  | .typeOnlySupport => 1

private def uniqueDefectKinds (xs : Array DefectKind) : Array DefectKind := Id.run do
  let mut out := #[]
  for x in xs do
    if !out.contains x then
      out := out.push x
  return out

private def defectTagsForEdge
    (capstone : Bool)
    (srcFeature dstFeature : FeatureBundle)
    (role : DependencyRole)
    (edgeBoundary : BoundaryClass)
    (edgePolarity : PolarityClass) : Array DefectKind := Id.run do
  let mut out := #[]
  if role == .remoteSupport then
    out := out.push .remoteAttachment
  if dstFeature.layerNat > srcFeature.layerNat then
    out := out.push .regressiveFlow
  if dstFeature.layerNat + 1 < srcFeature.layerNat && !capstone then
    out := out.push .boundaryBypass
    out := out.push .failedLocalFactorization
  if edgeBoundary == .mixed then
    out := out.push .illicitBoundaryCrossing
  if edgePolarity == .mixed then
    out := out.push .mixedPolarity
  if edgePolarity == .neutral && role == .remoteSupport then
    out := out.push .unclearPolarity
  return uniqueDefectKinds out

private def depKindString (env : Environment) (dep : Name) : String :=
  match env.find? dep with
  | some ci => kindString ci
  | none => "opaque"

private def buildFlowEdgesForDecl
    (env : Environment)
    (declName : Name)
    (depth : RepDepth)
    (kind : String)
    (capstone : Bool)
    (directEvidence : Array DirectEdgeEvidence) : Array FlowEdge :=
  let directDepDepthNats := uniqueNats <| directEvidence.filterMap (·.dstDepthNat?)
  let srcFeature := featureBundleOf depth kind capstone depth.toNat directDepDepthNats
  directEvidence.map fun ev =>
    let dep := ev.dst
    let edgeUse := ev.edgeUse
    let edgeKind := dominantEdgeKindOf edgeUse
    let depDepthNat := ev.dstDepthNat?.getD depth.toNat
    let depDepth := RepDepth.ofNat depDepthNat
    let depEdges := directEdgeEvidenceOf env dep
    let depFeature := featureBundleOf depDepth (depKindString env dep) (capstoneAttr.hasTag env dep)
      depDepth.toNat (uniqueNats <| depEdges.filterMap (·.dstDepthNat?))
    let inferredRole := dependencyRoleOf depth.toNat depDepthNat edgeUse
    let inferredBoundary := edgeBoundaryOf capstone srcFeature depFeature inferredRole
    let inferredPolarity := edgePolarityOf srcFeature depFeature inferredRole
    {
      src := declName
      dst := dep
      edgeUse := edgeUse
      edgeKind := edgeKind
      provenanceKind := .directObserved
      inferredRole := inferredRole
      inferredBoundary := inferredBoundary
      depthHint? := some depDepthNat
      inferredPolarity := inferredPolarity
      srcFeature := srcFeature
      dstFeature := depFeature
      defectTags := defectTagsForEdge capstone srcFeature depFeature inferredRole inferredBoundary inferredPolarity
    }

private def flowEdgesRaw (env : Environment) : Array FlowEdge :=
  env.constants.fold (init := #[]) fun acc declName ci =>
    match repDepth? env declName with
    | none => acc
    | some depth =>
        let kind := kindString ci
        let capstone := capstoneAttr.hasTag env declName
        let directEvidence := directEdgeEvidenceOf env declName
        acc ++ buildFlowEdgesForDecl env declName depth kind capstone directEvidence

private def flowEdgesFor (flowEdges : Array FlowEdge) (src : Name) : Array FlowEdge :=
  (flowEdges.filter fun edge => edge.src == src).qsort fun a b => toString a.dst < toString b.dst

private def buildHeadCandidates (edges : Array FlowEdge) : Array WeightedName :=
  let candidates : Array WeightedName :=
    edges.foldl (init := #[]) fun acc edge =>
      let weight := headWeightOf edge.inferredRole edge.edgeUse
      if weight == 0 then
        acc
      else
        acc.push ({ name := edge.dst, weight := weight } : WeightedName)
  candidates.qsort fun a b =>
    if a.weight == b.weight then toString a.name < toString b.name else a.weight > b.weight

private def directNamesByKind (edges : Array FlowEdge) (kind : DAG.EdgeKind) : Array Name :=
  uniqueNames <| edges.foldl (init := #[]) fun acc edge =>
    if (kind == .value && edgeUseHasValue edge.edgeUse) || (kind == .type && edgeUseHasType edge.edgeUse) then
      acc.push edge.dst
    else
      acc

private def supportCandidatesOf (edges : Array FlowEdge) : Array Name :=
  uniqueNames <| edges.foldl (init := #[]) fun acc edge =>
    if edge.inferredRole == .head || edge.inferredRole == .transportArg then acc else acc.push edge.dst

private def processEventsBase (env : Environment) (flowEdges : Array FlowEdge) : Array ProcessEvent :=
  env.constants.fold (init := #[]) fun acc declName ci =>
    match repDepth? env declName with
    | none => acc
    | some depth =>
        let kind := kindString ci
        let capstone := capstoneAttr.hasTag env declName
        let directEvidence := directEdgeEvidenceOf env declName
        let directDepDepthNats := uniqueNats <| directEvidence.filterMap (·.dstDepthNat?)
        let role := derivationalRoleOf capstone depth.toNat directDepDepthNats
        let boundaryClass := boundaryClassOf role (localityClassOf depth.toNat directDepDepthNats)
        let featureOut := featureBundleOf depth kind capstone depth.toNat directDepDepthNats
        let edges := flowEdgesFor flowEdges declName
        let novelty :=
          (if role == .primitiveTranslator then 2 else if role == .capstoneCoherence then 1 else 0) +
          edges.foldl (init := 0) fun n edge =>
            n + match edge.inferredRole with
              | .head => 2
              | .transportArg => 2
              | .requiredArg => 1
              | .remoteSupport => 0
              | _ => 0
        acc.push {
          node := declName
          module := moduleNameFor env declName
          kind := kind
          role := role
          boundaryClass := boundaryClass
          directDeps := uniqueNames (edges.map (·.dst))
          directValueDeps := directNamesByKind edges .value
          directTypeDeps := directNamesByKind edges .type
          closureDeps := closureTaggedDependencies env declName
          featureInputs := edges.map (fun edge => { dep := edge.dst, feature := edge.dstFeature })
          featureIn := uniqueFeatures (edges.map (·.dstFeature))
          featureOut := #[featureOut]
          headCandidates := buildHeadCandidates edges
          supportCandidates := supportCandidatesOf edges
          comparisonCandidates := #[]
          novelty := novelty
        }

private def addComparisonCandidates (events : Array ProcessEvent) : Array ProcessEvent := Id.run do
  let mut out := #[]
  for ev in events do
    let role := ev.role
    let some outFeature := ev.featureOut[0]? | out := out.push ev; continue
    let candidates := events.foldl (init := #[]) fun acc other =>
      if other.node == ev.node then acc
      else
        match other.featureOut[0]? with
        | some otherOut =>
            if other.role == role && otherOut.layerNat == outFeature.layerNat && other.boundaryClass == ev.boundaryClass then
              acc.push other.node
            else acc
        | none => acc
    out := out.push { ev with comparisonCandidates := uniqueNames candidates }
  return out.qsort fun a b => toString a.node < toString b.node

private def edgeKey (src dst : Name) : String :=
  s!"{toString src}→{toString dst}"

private def flowEdgeMap (edges : Array FlowEdge) : Std.HashMap String FlowEdge :=
  edges.foldl (init := {}) fun acc edge => acc.insert (edgeKey edge.src edge.dst) edge

private def adjacencyOfEdges (edges : Array FlowEdge) : Std.HashMap Name (Array Name) :=
  edges.foldl (init := {}) fun acc edge =>
    let current := acc.getD edge.src #[]
    acc.insert edge.src (uniqueNames (current.push edge.dst))

private def predecessorMap
    (adj : Std.HashMap Name (Array Name))
    (src : Name) : Std.HashMap Name Name := Id.run do
  let mut pred : Std.HashMap Name Name := {}
  let mut seen : NameSet := {}
  let mut queue : Array Name := #[src]
  let mut front : Nat := 0
  seen := seen.insert src
  while front < queue.size do
    let u := queue[front]!
    front := front + 1
    for v in adj.getD u #[] do
      if !seen.contains v then
        seen := seen.insert v
        pred := pred.insert v u
        queue := queue.push v
  return pred

private def reconstructPath (pred : Std.HashMap Name Name) (src dst : Name) : Option (Array Name) := Id.run do
  if src == dst then
    return some #[src]
  if !(pred.contains dst) then
    return none
  let mut rev : Array Name := #[dst]
  let mut cur := dst
  while cur != src do
    match pred.get? cur with
    | none => return none
    | some p =>
        rev := rev.push p
        cur := p
  return some rev.reverse

private def defectOfTag (tag : DefectKind) (stepIdx : Nat) (witness : Name) : Defect :=
  {
    kind := tag
    atStep := stepIdx
    cost := defectSeverity tag
    witness := some witness
  }

private def unresolvedComparisonDefect (dst : Name) (stepIdx : Nat) : Defect :=
  {
    kind := .unresolvedComparison
    atStep := stepIdx
    cost := defectSeverity .unresolvedComparison
    witness := some dst
  }

private def pathStepOf (edge : FlowEdge) : PathStep :=
  {
    src := edge.src
    dst := edge.dst
    edgeUse := edge.edgeUse
    edgeKind := edge.edgeKind
    inferredRole := edge.inferredRole
    provenanceKind := edge.provenanceKind
    inferredBoundary := edge.inferredBoundary
    boundaryCrossing := edge.inferredBoundary == .bridge || edge.inferredBoundary == .localInterface || edge.inferredBoundary == .capstone
    featureIn := edge.srcFeature
    featureOut := edge.dstFeature
  }

-- Bounded ancestry path candidates: declaration -> direct/transitive dependency chain.
private def lawfulPathsRaw (events : Array ProcessEvent) (edges : Array FlowEdge) : Array LawfulPathCandidate := Id.run do
  let adj := adjacencyOfEdges edges
  let edgeMap := flowEdgeMap edges
  let mut out := #[]
  for srcEv in events do
    let pred := predecessorMap adj srcEv.node
    for dstEv in events do
      if dstEv.node == srcEv.node then
        continue
      match reconstructPath pred srcEv.node dstEv.node with
      | none => pure ()
      | some nodes =>
          if nodes.size < 2 || nodes.size > 3 then
            continue
          let mut steps := #[]
          let mut edgeDefects := #[]
          let mut ok := true
          for i in [:nodes.size - 1] do
            let u := nodes[i]!
            let v := nodes[i + 1]!
            match edgeMap.get? (edgeKey u v) with
            | none => ok := false
            | some edge =>
                steps := steps.push (pathStepOf edge)
                for tag in edge.defectTags do
                  edgeDefects := edgeDefects.push (defectOfTag tag i edge.dst)
          if ok then
            let sharedComparisonCandidates :=
              uniqueNames (srcEv.comparisonCandidates.filter fun n => dstEv.comparisonCandidates.contains n)
            let pathLocalDefects :=
              if nodes.size > 2 && sharedComparisonCandidates.isEmpty then
                #[unresolvedComparisonDefect dstEv.node (nodes.size - 2)]
              else
                #[]
            let edgeDefectCost := edgeDefects.foldl (init := 0) fun n d => n + d.cost
            let pathLocalDefectCost := pathLocalDefects.foldl (init := 0) fun n d => n + d.cost
            let totalCost := edgeDefectCost + pathLocalDefectCost
            out := out.push {
              src := srcEv.node
              dst := dstEv.node
              steps := steps
              totalDefectCost := totalCost
              defects := pathLocalDefects
              sharedComparisonCandidates := sharedComparisonCandidates
            }
  return out.qsort fun a b =>
    if toString a.src == toString b.src then toString a.dst < toString b.dst else toString a.src < toString b.src

private def edgeDefectRowsOf (edges : Array FlowEdge) : Array DefectRow :=
  edges.foldl (init := #[]) fun acc edge =>
    edge.defectTags.foldl (init := acc) fun acc' tag =>
      acc'.push {
        locus := "edge"
        src := edge.src
        dst := edge.dst
        defect := defectOfTag tag 0 edge.dst
      }

private def pathDefectRowsOf (paths : Array LawfulPathCandidate) : Array DefectRow :=
  paths.foldl (init := #[]) fun acc path =>
    path.defects.foldl (init := acc) fun acc' defect =>
      acc'.push {
        locus := "path"
        src := path.src
        dst := path.dst
        defect := defect
      }

private def createDirAllFrom (path : System.FilePath) : IO Unit :=
  match path.parent with
  | some p => IO.FS.createDirAll p
  | none => pure ()

private def writeJsonl {α} [ToJson α] (path : System.FilePath) (rows : Array α) : IO Unit := do
  createDirAllFrom path
  let lines := String.intercalate "\n" <| rows.toList.map (fun row => (toJson row).compress)
  IO.FS.writeFile path (if lines.isEmpty then "" else lines ++ "\n")

private def runExport (importModsStr outDirStr : String) : IO UInt32 := do
  let importMods := importModsStr.splitOn "," |>.map dottedName
  let imports : Array Import := importMods.foldl (init := #[]) fun acc m =>
    acc.push { module := m }
  let env ← importModules imports {} 0
  let flowEdges := (flowEdgesRaw env).qsort fun a b =>
    if toString a.src == toString b.src then toString a.dst < toString b.dst else toString a.src < toString b.src
  let events := addComparisonCandidates (processEventsBase env flowEdges)
  let paths := lawfulPathsRaw events flowEdges
  let defects := edgeDefectRowsOf flowEdges ++ pathDefectRowsOf paths
  let outDir := System.FilePath.mk outDirStr
  writeJsonl (outDir / "flow-edges.jsonl") flowEdges
  writeJsonl (outDir / "process-events.jsonl") events
  writeJsonl (outDir / "lawful-path-candidates.jsonl") paths
  writeJsonl (outDir / "defects.jsonl") defects
  IO.println s!"[ProcessFlowExport] modules={importModsStr} edges={flowEdges.size} events={events.size} paths={paths.size} defects={defects.size} wrote {outDirStr}"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [importModsStr, outDir] =>
      runExport importModsStr outDir
  | _ =>
      IO.eprintln "usage: ProcessFlowExport <import-module[,module2,...]> <output-dir>"
      IO.eprintln "example: lake env lean --run lean/DAG/ProcessFlowExport.lean InfoGeometry.Audit artifacts/dag/process-flow"
      return 1

end DAG

def main (args : List String) : IO UInt32 :=
  DAG.main args
