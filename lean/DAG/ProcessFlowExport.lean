import Lean
import Lean.Data.Json
import DAG.Basic
import DAG.JsonInstances
import DAG.TypedCategory
import InfoGeometry.Meta.Architecture

open Lean
open InfoGeometry.Meta

namespace DAG

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
    let mut visited : NameSet := {}
    let mut queue : Array (Name × EdgeUse) := #[]
    for (dep, kind) in DAG.edgesFromConstantInfo ci do
      queue := queue.push (dep, edgeUseOfKind kind)
    let mut i := 0
    while i < queue.size do
      let (curr, use) := queue[i]!
      i := i + 1
      if visited.contains curr then continue
      visited := visited.insert curr
      if let some depDepth := repDepth? env curr then
        let mut replaced := false
        let mut next := #[]
        for ev in out do
          if ev.dst == curr then
            replaced := true
            next := next.push { ev with edgeUse := mergeEdgeUse ev.edgeUse use }
          else
            next := next.push ev
        if !replaced then
          next := next.push {
            src := declName
            dst := curr
            edgeUse := use
            srcDepthNat? := srcDepthNat?
            dstDepthNat? := some depDepth.toNat
            srcModule := srcModule
            dstModule := moduleNameFor env curr
          }
        out := next
      else
        if let some nextCi := env.find? curr then
          for (nextDep, nextKind) in DAG.edgesFromConstantInfo nextCi do
            queue := queue.push (nextDep, mergeEdgeUse use (edgeUseOfKind nextKind))
  return out.qsort fun a b => toString a.dst < toString b.dst

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

private def declFlowSummaryMap (env : Environment) : Std.HashMap Name DeclFlowSummary := Id.run do
  let mut out : Std.HashMap Name DeclFlowSummary := {}
  for (declName, ci) in env.constants do
    match repDepth? env declName with
    | none => pure ()
    | some depth =>
        let kind := kindString ci
        let capstone := capstoneAttr.hasTag env declName
        let directEvidence := directEdgeEvidenceOf env declName
        let directDepDepthNats := uniqueNats <| directEvidence.filterMap (·.dstDepthNat?)
        let feature := featureBundleOf depth kind capstone depth.toNat directDepDepthNats
        out := out.insert declName {
          depth := depth
          kind := kind
          capstone := capstone
          directEvidence := directEvidence
          feature := feature
        }
  return out

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
    (summaries : Std.HashMap Name DeclFlowSummary)
    (declName : Name)
    (summary : DeclFlowSummary) : Array FlowEdge :=
  let depth := summary.depth
  let capstone := summary.capstone
  let directEvidence := summary.directEvidence
  let srcFeature := summary.feature
  directEvidence.map fun ev =>
    let dep := ev.dst
    let edgeUse := ev.edgeUse
    let edgeKind := dominantEdgeKindOf edgeUse
    let depDepthNat := ev.dstDepthNat?.getD depth.toNat
    let depFeature :=
      match summaries.get? dep with
      | some depSummary => depSummary.feature
      | none =>
          let depDepth := RepDepth.ofNat depDepthNat
          let depEdges := directEdgeEvidenceOf env dep
          featureBundleOf depDepth (depKindString env dep) (capstoneAttr.hasTag env dep)
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

private def flowEdgesRaw (env : Environment) (summaries : Std.HashMap Name DeclFlowSummary) : Array FlowEdge :=
  env.constants.fold (init := #[]) fun acc declName _ =>
    match summaries.get? declName with
    | none => acc
    | some summary =>
        acc ++ buildFlowEdgesForDecl env summaries declName summary

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

private def adjacencyOfEdges (edges : Array FlowEdge) : Std.HashMap Name (Array Name) :=
  edges.foldl (init := {}) fun acc edge =>
    let current := acc.getD edge.src #[]
    acc.insert edge.src (uniqueNames (current.push edge.dst))

private def closureTaggedDependenciesOfAdj
    (adj : Std.HashMap Name (Array Name))
    (declName : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut out := #[]
  let mut queue : Array Name := adj.getD declName #[]
  let mut front : Nat := 0
  for dep in queue do
    if dep != declName && !seen.contains dep then
      seen := seen.insert dep
      out := out.push dep
  while front < queue.size do
    let u := queue[front]!
    front := front + 1
    for v in adj.getD u #[] do
      if v != declName && !seen.contains v then
        seen := seen.insert v
        out := out.push v
        queue := queue.push v
  return uniqueNames out

private def processEventsBase
    (env : Environment)
    (summaries : Std.HashMap Name DeclFlowSummary)
    (flowEdges : Array FlowEdge) : Array ProcessEvent :=
  let adj := adjacencyOfEdges flowEdges
  env.constants.fold (init := #[]) fun acc declName _ =>
    match summaries.get? declName with
    | none => acc
    | some summary =>
        let depth := summary.depth
        let capstone := summary.capstone
        let directEvidence := summary.directEvidence
        let directDepDepthNats := uniqueNats <| directEvidence.filterMap (·.dstDepthNat?)
        let role := derivationalRoleOf capstone depth.toNat directDepDepthNats
        let boundaryClass := boundaryClassOf role (localityClassOf depth.toNat directDepDepthNats)
        let featureOut := summary.feature
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
          kind := summary.kind
          role := role
          boundaryClass := boundaryClass
          directDeps := uniqueNames (edges.map (·.dst))
          directValueDeps := directNamesByKind edges .value
          directTypeDeps := directNamesByKind edges .type
          closureDeps := closureTaggedDependenciesOfAdj adj declName
          featureInputs := edges.map (fun edge => { dep := edge.dst, feature := edge.dstFeature })
          featureIn := uniqueFeatures (edges.map (·.dstFeature))
          featureOut := #[featureOut]
          headCandidates := buildHeadCandidates edges
          supportCandidates := supportCandidatesOf edges
          comparisonCandidates := #[]
          novelty := novelty
        }

private def comparisonGroups (events : Array ProcessEvent) :
    Std.HashMap ComparisonGroupKey (Array Name) :=
  events.foldl (init := {}) fun acc ev =>
    match ev.featureOut[0]? with
    | none => acc
    | some outFeature =>
        let key : ComparisonGroupKey := {
          role := ev.role
          layerNat := outFeature.layerNat
          boundaryClass := ev.boundaryClass
        }
        let current := acc.getD key #[]
        acc.insert key (current.push ev.node)

private def addComparisonCandidates (events : Array ProcessEvent) : Array ProcessEvent := Id.run do
  let groups := comparisonGroups events
  let mut out := #[]
  for ev in events do
    let candidates :=
      match ev.featureOut[0]? with
      | none => #[]
      | some outFeature =>
          let key : ComparisonGroupKey := {
            role := ev.role
            layerNat := outFeature.layerNat
            boundaryClass := ev.boundaryClass
          }
          uniqueNames <| (groups.getD key #[]).filter fun other => other != ev.node
    out := out.push { ev with comparisonCandidates := candidates }
  return out.qsort fun a b => toString a.node < toString b.node

private def edgeKey (src dst : Name) : String :=
  s!"{toString src}→{toString dst}"

private def flowEdgeMap (edges : Array FlowEdge) : Std.HashMap String FlowEdge :=
  edges.foldl (init := {}) fun acc edge => acc.insert (edgeKey edge.src edge.dst) edge

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

private def sharedComparisonCandidatesOf (srcEv dstEv : ProcessEvent) : Array Name :=
  uniqueNames <| srcEv.comparisonCandidates.filter fun n => dstEv.comparisonCandidates.contains n

private def appendDirectPathCandidates
    (srcEv : ProcessEvent)
    (directDsts : Array Name)
    (eventMap : Std.HashMap Name ProcessEvent)
    (edgeMap : Std.HashMap String FlowEdge)
    (seen : NameSet)
    (out : Array TypedPathCandidate) : NameSet × Array TypedPathCandidate := Id.run do
  let mut seen' := seen
  let mut out' := out
  for dst in directDsts do
    if seen'.contains dst then
      continue
    match eventMap.get? dst, edgeMap.get? (edgeKey srcEv.node dst) with
    | some dstEv, some edge =>
        let shared := sharedComparisonCandidatesOf srcEv dstEv
        let edgeDefectCost := edge.defectTags.foldl (init := 0) fun n tag => n + defectSeverity tag
        out' := out'.push {
          src := srcEv.node
          dst := dstEv.node
          steps := #[pathStepOf edge]
          totalDefectCost := edgeDefectCost
          defects := #[]
          sharedComparisonCandidates := shared
        }
        seen' := seen'.insert dst
    | _, _ => pure ()
  return (seen', out')

private def appendTwoStepPathCandidates
    (srcEv : ProcessEvent)
    (adj : Std.HashMap Name (Array Name))
    (eventMap : Std.HashMap Name ProcessEvent)
    (edgeMap : Std.HashMap String FlowEdge)
    (seen : NameSet)
    (out : Array TypedPathCandidate) : NameSet × Array TypedPathCandidate := Id.run do
  let mut seen' := seen
  let mut out' := out
  let directDsts := adj.getD srcEv.node #[]
  for mid in directDsts do
    let some edge₁ := edgeMap.get? (edgeKey srcEv.node mid) | continue
    for dst in adj.getD mid #[] do
      if dst == srcEv.node || seen'.contains dst then
        continue
      match eventMap.get? dst, edgeMap.get? (edgeKey mid dst) with
      | some dstEv, some edge₂ =>
          let shared := sharedComparisonCandidatesOf srcEv dstEv
          let pathLocalDefects :=
            if shared.isEmpty then
              #[unresolvedComparisonDefect dstEv.node 1]
            else
              #[]
          let edgeDefectCost :=
            edge₁.defectTags.foldl (init := 0) fun n tag => n + defectSeverity tag
              +
            edge₂.defectTags.foldl (init := 0) fun n tag => n + defectSeverity tag
          let pathLocalDefectCost := pathLocalDefects.foldl (init := 0) fun n d => n + d.cost
          out' := out'.push {
            src := srcEv.node
            dst := dstEv.node
            steps := #[pathStepOf edge₁, pathStepOf edge₂]
            totalDefectCost := edgeDefectCost + pathLocalDefectCost
            defects := pathLocalDefects
            sharedComparisonCandidates := shared
          }
          seen' := seen'.insert dst
      | _, _ => pure ()
  return (seen', out')

-- Bounded ancestry path candidates: declaration -> direct/transitive dependency chain.
private def lawfulPathsRaw (events : Array ProcessEvent) (edges : Array FlowEdge) : Array TypedPathCandidate := Id.run do
  let adj := adjacencyOfEdges edges
  let edgeMap := flowEdgeMap edges
  let eventMap : Std.HashMap Name ProcessEvent :=
    events.foldl (init := {}) fun acc ev => acc.insert ev.node ev
  let mut out := #[]
  for srcEv in events do
    let directDsts := adj.getD srcEv.node #[]
    let (seenDirect, outAfterDirect) :=
      appendDirectPathCandidates srcEv directDsts eventMap edgeMap {} out
    let (_, outAfterTwoStep) :=
      appendTwoStepPathCandidates srcEv adj eventMap edgeMap seenDirect outAfterDirect
    out := outAfterTwoStep
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

private def pathDefectRowsOf (paths : Array TypedPathCandidate) : Array DefectRow :=
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
  IO.println s!"[ProcessFlowExport] starting import modules={importModsStr}"
  let env ← importModules imports {} 0
  IO.println s!"[ProcessFlowExport] imported modules={importModsStr}"
  let summaries := declFlowSummaryMap env
  IO.println s!"[ProcessFlowExport] summaries={summaries.size}"
  let flowEdges := (flowEdgesRaw env summaries).qsort fun a b =>
    if toString a.src == toString b.src then toString a.dst < toString b.dst else toString a.src < toString b.src
  IO.println s!"[ProcessFlowExport] flowEdges={flowEdges.size}"
  let events := addComparisonCandidates (processEventsBase env summaries flowEdges)
  IO.println s!"[ProcessFlowExport] events={events.size}"
  let typedObjects := events.map ProcessEvent.toTypedDeclObject
  IO.println s!"[ProcessFlowExport] typedObjects={typedObjects.size}"
  let semanticMorphisms := events.foldl (init := #[]) fun acc ev =>
    acc ++ ev.semanticTypedMorphisms
  IO.println s!"[ProcessFlowExport] semanticMorphisms={semanticMorphisms.size}"
  let paths := lawfulPathsRaw events flowEdges
  IO.println s!"[ProcessFlowExport] paths={paths.size}"
  let typedPaths := paths.map TypedPathCandidate.toTypedCompositePathWithDefects
  IO.println s!"[ProcessFlowExport] typedPaths={typedPaths.size}"
  let lawfulCones := events.map (ProcessEvent.toTypedCone paths)
  IO.println s!"[ProcessFlowExport] lawfulCones={lawfulCones.size}"
  let defects := edgeDefectRowsOf flowEdges ++ pathDefectRowsOf paths
  IO.println s!"[ProcessFlowExport] defects={defects.size}"
  let outDir := System.FilePath.mk outDirStr
  writeJsonl (outDir / "flow-edges.jsonl") flowEdges
  writeJsonl (outDir / "process-events.jsonl") events
  writeJsonl (outDir / "typed-decl-objects.jsonl") typedObjects
  writeJsonl (outDir / "typed-semantic-morphisms.jsonl") semanticMorphisms
  writeJsonl (outDir / "lawful-path-candidates.jsonl") paths
  writeJsonl (outDir / "lawful-typed-composite-paths.jsonl") typedPaths
  writeJsonl (outDir / "lawful-cones.jsonl") lawfulCones
  writeJsonl (outDir / "defects.jsonl") defects
  IO.println s!"[ProcessFlowExport] modules={importModsStr} edges={flowEdges.size} events={events.size} typedObjects={typedObjects.size} semanticMorphisms={semanticMorphisms.size} paths={paths.size} typedPaths={typedPaths.size} lawfulCones={lawfulCones.size} defects={defects.size} wrote {outDirStr}"
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
