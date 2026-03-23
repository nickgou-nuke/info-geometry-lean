import Lean
import Lean.Data.Json
import DAG.Basic
import DAG.Hydrate
import DAG.Analysis

open Lean

namespace DAG

structure StructuralRootContributionRow where
  componentId : String
  representative : String
  paths : Nat
deriving Repr, ToJson

structure StructuralLayerRow where
  depth : Nat
  size : Nat
  componentIds : Array String
  representatives : Array String
deriving Repr, ToJson

structure StructuralChainRow where
  depth : Nat
  componentIds : Array String
  representatives : Array String
deriving Repr, ToJson

structure StructuralEdgeRow where
  sourceComponentId : String
  sourceRepresentative : String
  targetComponentId : String
  targetRepresentative : String
deriving Repr, ToJson

structure StructuralMembershipRow where
  declName : String
  componentId : String
  componentIndex : Nat
  representative : String
deriving Repr, ToJson

structure StructuralComponentRow where
  componentId : String
  componentIndex : Nat
  representative : String
  size : Nat
  members : Array String
  dependencyComponentIds : Array String
  dependencyRepresentatives : Array String
  reverseDependentComponentIds : Array String
  reverseDependentRepresentatives : Array String
  depthMin : Nat
  depthMax : Nat
  depthSpread : Nat
  isRoot : Bool
  isCapstone : Bool
  rootContributionCount : Nat
  rootContributions : Array StructuralRootContributionRow
  strictDominatorComponentIds : Array String
  strictDominatorRepresentatives : Array String
  strictDominatorCount : Nat
  canonicalRootWitnessComponentIds : Array String
  canonicalRootWitness : Array String
deriving Repr, ToJson

structure StructuralPayload where
  schemaVersion : Nat
  orientation : String
  nodeCount : Nat
  componentCount : Nat
  rootCount : Nat
  capstoneCount : Nat
  layerCount : Nat
  maxDepth : Nat
  roots : Array String
  rootComponentIds : Array String
  capstones : Array String
  capstoneComponentIds : Array String
  layers : Array StructuralLayerRow
  deepestChains : Array StructuralChainRow
  components : Array StructuralComponentRow
  componentEdges : Array StructuralEdgeRow
  membership : Array StructuralMembershipRow
deriving Repr, ToJson

private def stableComponentId (members : Array String) : String :=
  let basis := String.intercalate "\n" members.toList
  let h : UInt64 := hash basis
  s!"component:{h.toNat}"

private def sortedComponentMembers (h : HydratedGraph String) (si : Nat) : Array String :=
  let members := h.sccs[si]!.map (fun v => h.toGraph.nodes[v]!)
  members.qsort (fun a b => a < b)

private def representativeString (memberLists : Array (Array String)) (si : Nat) : String :=
  match memberLists[si]![0]? with
  | some name => name
  | none => ""

private def bitsetHas (bytes : ByteArray) (i : Nat) : Bool :=
  let bi := i / 8
  if bi < bytes.size then
    let bit : UInt8 := 1 <<< (i % 8).toUInt8
    ((bytes[bi]! &&& bit) != 0)
  else
    false

private def dominatorIndices (h : HydratedGraph String) (si : Nat) : Array Nat :=
  Id.run do
    let mut out := #[]
    let bytes := h.doms[si]!
    for i in [:h.dag.size] do
      if bitsetHas bytes i then
        out := out.push i
    out

private def depthMaxCore (h : HydratedGraph String) : Array (Option Nat) × Array (Option Nat) :=
  Id.run do
    let n := h.dag.size
    let roots := rootSet h
    let orderFromRoots := h.topo.reverse
    let mut depth : Array (Option Nat) := arrayReplicate n none
    let mut pred : Array (Option Nat) := arrayReplicate n none

    for r in roots do
      depth := depth.set! r (some 0)

    for u in orderFromRoots do
      let some du := depth[u]! | continue
      for v in h.preds[u]! do
        let cand := du + 1
        match depth[v]! with
        | none =>
            depth := depth.set! v (some cand)
            pred := pred.set! v (some u)
        | some dv =>
            if cand > dv then
              depth := depth.set! v (some cand)
              pred := pred.set! v (some u)

    (depth, pred)

private def canonicalRootWitnessComponents (pred : Array (Option Nat)) (target : Nat) : Array Nat :=
  Id.run do
    let mut chain : Array Nat := #[]
    let mut cur : Option Nat := some target
    while cur.isSome do
      let u := cur.get!
      chain := chain.push u
      cur := pred[u]!
    chain.reverse

private def natSetOf (xs : Array Nat) : Std.HashSet Nat :=
  xs.foldl (init := ({} : Std.HashSet Nat)) (fun acc x => acc.insert x)

private def componentPathCountsUpwardStructural
  (preds : Array (Array Nat))
  (orderFromRoots : Array Nat)
  (src : Nat)
  : Array Nat :=
  Id.run do
    let n := preds.size
    let mut counts := arrayReplicate n 0
    counts := counts.set! src 1

    for ti in [:orderFromRoots.size] do
      let u := orderFromRoots[ti]!
      let cu := counts[u]!
      if cu != 0 then
        for ei in [:preds[u]!.size] do
          let v := preds[u]![ei]!
          let old := counts[v]!
          counts := counts.set! v (old + cu)

    counts

private def buildPayload (h : HydratedGraph String) : StructuralPayload :=
  Id.run do
    let roots := rootSet h
    let caps := capstoneSet h
    let rootSetHash := natSetOf roots
    let capSetHash := natSetOf caps
    let dMin := depthMinFromRoots h
    let dSpread := depthSpreadFromRoots h
    let (dMax, pred) := depthMaxCore h
    let layersRaw := topologicalLayersFromRoots h
    let deepestRaw := deepestRootChains h
    let orderFromRoots := h.topo.reverse
    let rootPathCountsByRoot : Array (Nat × Array Nat) := Id.run do
      let mut out := #[]
      for r in roots do
        out := out.push (r, componentPathCountsUpwardStructural h.preds orderFromRoots r)
      pure out

    let memberLists : Array (Array String) := Id.run do
      let mut out := #[]
      for si in [:h.sccs.size] do
        out := out.push (sortedComponentMembers h si)
      pure out
    let componentIds : Array String :=
      memberLists.map stableComponentId
    let representatives : Array String := Id.run do
      let mut out := #[]
      for si in [:memberLists.size] do
        out := out.push (representativeString memberLists si)
      pure out

    let rootsOut := roots.map (fun si => representatives[si]!)
    let rootIds := roots.map (fun si => componentIds[si]!)
    let capstonesOut := caps.map (fun si => representatives[si]!)
    let capstoneIds := caps.map (fun si => componentIds[si]!)

    let layers : Array StructuralLayerRow :=
      layersRaw.mapIdx fun depth comps =>
        {
          depth := depth
          size := comps.size
          componentIds := comps.map (fun si => componentIds[si]!)
          representatives := comps.map (fun si => representatives[si]!)
        }

    let mut maxDepth := 0
    for i in [:dMax.size] do
      match dMax[i]! with
      | none => pure ()
      | some d =>
          if d > maxDepth then
            maxDepth := d

    let deepestChains : Array StructuralChainRow :=
      deepestRaw.map fun comps =>
        {
          depth := if comps.size == 0 then 0 else comps.size - 1
          componentIds := comps.map (fun si => componentIds[si]!)
          representatives := comps.map (fun si => representatives[si]!)
        }

    let mut componentEdges : Array StructuralEdgeRow := #[]
    for si in [:h.dag.size] do
      for sj in h.dag[si]! do
        componentEdges := componentEdges.push {
          sourceComponentId := componentIds[si]!
          sourceRepresentative := representatives[si]!
          targetComponentId := componentIds[sj]!
          targetRepresentative := representatives[sj]!
        }

    let mut membership : Array StructuralMembershipRow := #[]
    for si in [:memberLists.size] do
      for name in memberLists[si]! do
        membership := membership.push {
          declName := name
          componentId := componentIds[si]!
          componentIndex := si
          representative := representatives[si]!
        }
    membership := membership.qsort (fun a b => a.declName < b.declName)

    let components : Array StructuralComponentRow := Id.run do
      let mut out := #[]
      for si in [:h.dag.size] do
        let dependencies := h.dag[si]!
        let reverseDependents := h.preds[si]!
        let rootContribs := Id.run do
          let mut contribs : Array (Nat × Nat) := #[]
          for entry in rootPathCountsByRoot do
            let ri := entry.1
            let counts := entry.2
            let c := counts[si]!
            if c != 0 then
              contribs := contribs.push (ri, c)
          pure (contribs.qsort (fun a b => a.2 > b.2))
        let strictDominators := (dominatorIndices h si).filter (fun dj => dj != si)
        let witnessCompIds := canonicalRootWitnessComponents pred si
        out := out.push {
          componentId := componentIds[si]!
          componentIndex := si
          representative := representatives[si]!
          size := memberLists[si]!.size
          members := memberLists[si]!
          dependencyComponentIds := dependencies.map (fun sj => componentIds[sj]!)
          dependencyRepresentatives := dependencies.map (fun sj => representatives[sj]!)
          reverseDependentComponentIds := reverseDependents.map (fun sj => componentIds[sj]!)
          reverseDependentRepresentatives := reverseDependents.map (fun sj => representatives[sj]!)
          depthMin := match dMin[si]! with | some d => d | none => 0
          depthMax := match dMax[si]! with | some d => d | none => 0
          depthSpread := match dSpread[si]! with | some d => d | none => 0
          isRoot := rootSetHash.contains si
          isCapstone := capSetHash.contains si
          rootContributionCount := rootContribs.size
          rootContributions := rootContribs.map fun (ri, paths) => {
            componentId := componentIds[ri]!
            representative := representatives[ri]!
            paths := paths
          }
          strictDominatorComponentIds := strictDominators.map (fun dj => componentIds[dj]!)
          strictDominatorRepresentatives := strictDominators.map (fun dj => representatives[dj]!)
          strictDominatorCount := strictDominators.size
          canonicalRootWitnessComponentIds := witnessCompIds.map (fun sj => componentIds[sj]!)
          canonicalRootWitness := witnessCompIds.map (fun sj => representatives[sj]!)
        }
      pure out

    {
      schemaVersion := 1
      orientation := "Edges are declaration -> dependency on the condensed SCC DAG. Roots are SCCs with empty dependency out-neighborhoods. The structure artifact adds stable component ids, component membership, dominator summaries, and canonical root witness paths."
      nodeCount := h.toGraph.nodes.size
      componentCount := h.sccs.size
      rootCount := roots.size
      capstoneCount := caps.size
      layerCount := layers.size
      maxDepth := maxDepth
      roots := rootsOut
      rootComponentIds := rootIds
      capstones := capstonesOut
      capstoneComponentIds := capstoneIds
      layers := layers
      deepestChains := deepestChains
      components := components
      componentEdges := componentEdges
      membership := membership
    }

def buildStructuralPayload (h : HydratedGraph String) : StructuralPayload :=
  buildPayload h

def writeStructuralJsonOutput (payload : StructuralPayload) (outPath : String) : IO Unit := do
  let path := System.FilePath.mk outPath
  if let some p := path.parent then
    IO.FS.createDirAll p
  IO.FS.writeFile path (toJson payload).pretty

end DAG
