import Lean
import Lean.Server.Requests
import Lean.Server.Utils
import Lean.Server.FileWorker.Utils
import Lean.Data.Json.FromToJson.Basic
import Lean.Server.Snapshots

import DAG.Basic
import DAG.Util
-- We need definitions from BlockExport
import DAG.BlockExport

open Lean
open Lean.Server
open Lean.Server.RequestM
open DAG
open Lean.Server.Snapshots

namespace DAG.Server

/-- Parameters for server-side slicing. -/
structure SliceParams where
  /-- The constant you want a slice for. -/
  target : Name
  /-- Any position inside the open file (required by RPC protocol, even if you don't use it). -/
  pos : Lsp.Position := { line := 0, character := 0 }
  /-- If true, include block text in the response. -/
  withText : Bool := false
  /-- If true, union in “context-like” blocks (namespace/section/end/open/attribute/set_option/...). -/
  withContext : Bool := true

deriving FromJson, ToJson

/-- Parameters for rendering a slice. -/
structure RenderParams where
  /-- The export data. -/
  exportData : Export
  /-- The indices to render. -/
  blocks : Array Nat
  /-- Any position (RPC requirement). -/
  pos : Lsp.Position := { line := 0, character := 0 }

deriving FromJson, ToJson

/-- Metadata for a sliceable target. -/
structure TargetInfo where
  /-- Fully qualified name. -/
  name : Name
  /-- Range in the document. -/
  range : Lsp.Range
deriving ToJson, FromJson

/-- Parameters for full semantic block export over the current document. -/
structure SemanticBlocksParams where
  /-- If true, include block text in the underlying export. -/
  withText : Bool := false
deriving FromJson, ToJson

/-- Conservative “context command” test based on the command text prefix. -/
def isContextText (txt : String) : Bool :=
  let t := txt.trimAscii
  t.startsWith "import"    || t.startsWith "prelude"  || t.startsWith "module" ||
  t.startsWith "/-!"       || t.startsWith "--"       ||
  t.startsWith "namespace" || t.startsWith "section"  || t.startsWith "end" ||
  t.startsWith "universe"  || t.startsWith "open"     || t.startsWith "attribute" ||
  t.startsWith "set_option"|| t.startsWith "local"    || t.startsWith "scoped" ||
  t.startsWith "notation"  || t.startsWith "infix"    || t.startsWith "prefix" ||
  t.startsWith "postfix"   || t.startsWith "macro"    || t.startsWith "macro_rules" ||
  t.startsWith "syntax"    ||
  t.startsWith "variable"  || t.startsWith "variables"||
  t.startsWith "parameter" || t.startsWith "parameters"

/-- Build a `DAG.Export` from a prefix of snapshots (running in IO to resolve InfoTrees). -/
def exportFromSnaps (doc : FileWorker.EditableDocument) (snaps : Array Snapshot) (withText : Bool) :
    IO (Export × Array Bool) := do
  let inputCtx := doc.meta.mkInputContext
  let mut blocks : Array Block := #[]
  let mut decls : Array Name := #[]
  let mut producer : Array Nat := #[]
  let mut isCtx : Array Bool := #[]
  let mut scopeStack : List ScopeFrame := []
  let baseSeen : NameSet :=
    match doc.initSnap.processedResult.get with
    | some headerState =>
        headerState.cmdState.env.constants.fold (init := ({} : NameSet)) fun s n _ => s.insert n
    | none => {}
  let mut seen : NameSet := baseSeen
  let mut prevEnd : String.Pos.Raw := ⟨0⟩

  for i in [:snaps.size] do
    let some snap := snaps[i]? | continue

    -- Extract the end position from the snapshot
    let stop := snap.endPos

    -- Compute span for this command
    let start := prevEnd
    prevEnd := stop

    -- If the parser didn't advance, skip this snapshot to avoid empty blocks
    if start >= stop then
      continue

    -- update scope stack using the syntax of the command
    match snap.stx with
    | `(namespace $id:ident) =>
        scopeStack := { kind := ScopeKind.namespace, name := id.getId } :: scopeStack
    | `(section) =>
        scopeStack := { kind := ScopeKind.section, name := Name.anonymous } :: scopeStack
    | `(section $id:ident) =>
        scopeStack := { kind := ScopeKind.section, name := id.getId } :: scopeStack
    | `(end $_id?) =>
        if !scopeStack.isEmpty then
          scopeStack := scopeStack.tail
    | _ => pure ()

    let txtFull := toString (inputCtx.substring start stop)
    if txtFull.trimAscii.isEmpty then
      continue

    let startPos := inputCtx.fileMap.toPosition start
    let stopPos  := inputCtx.fileMap.toPosition stop
    let ctxFlag := isContextText txtFull

    -- produced decls: stage2 diff against `seen`
    let (newDecls0, seen') :=
      snap.env.constants.foldStage2
        (fun (acc : Array Name × NameSet) n _ =>
          let (arr, s) := acc
          if s.contains n then
            (arr, s)
          else
            let s := s.insert n
            (arr.push n, s))
        (#[], seen)
    seen := seen'
    let newDecls : Array Name := newDecls0.qsort Name.lt

    let blockIdx := blocks.size
    if newDecls.size > 0 then
      decls := decls ++ newDecls
      producer := producer ++ Array.replicate newDecls.size blockIdx

    let (primaryDecls, auxDecls) := classifyProducedDecls newDecls
    let primarySpineTags := collectPrimarySpineTags snap.env primaryDecls
    let spineTags := summarizeSpineTags primarySpineTags

    blocks := blocks.push
      { idx := blockIdx
        stableId := mkStableBlockId start stop
        startUtf8 := start
        stopUtf8 := stop
        startPos := startPos
        stopPos := stopPos
        text := if withText then txtFull else ""
        scopes := scopeStack.reverse.toArray
        primaryProduces := primaryDecls
        auxProduces := auxDecls
        primarySpineTags := primarySpineTags
        spineTags := spineTags
        affects := #[]
        morphisms := #[]
        docStrings := #[]
        typeStrings := #[] }

    isCtx := isCtx.push ctxFlag

  if snaps.isEmpty then
    let graph : DAG.Graph Name := { nodes := #[], nodeToIdx := {}, forward := #[] }
    let blockGraph : DAG.Graph Nat := { nodes := #[], nodeToIdx := {}, forward := #[] }
    let ex : Export := {
      file := doc.meta.uri,
      header := "",
      blocks := #[],
      decls := #[],
      producer := #[],
      graph := graph,
      blockGraph := blockGraph,
      skeletonMap := #[]
    }
    return (ex, #[])
  else
    match snaps[snaps.size - 1]? with
    | some lastSnap =>
      let env := lastSnap.env
      let graph := buildGraphFromEnvOn env decls
      let prodMap := producerMap decls producer
      let blockGraph := buildBlockGraph graph prodMap blocks.size

      let hydratedG := DAG.hydrate graph
      let skelPairs := DAG.extractTheorySkeletonWithPreferred hydratedG (primaryDeclSet blocks) 1
      let mut skelMap : Array (Name × Nat) := #[]
      for i in [:skelPairs.size] do
        let (n, _, rank) := skelPairs[i]!
        skelMap := skelMap.push (n, rank)

      let ex : Export := {
         file := doc.meta.uri,
         header := "", -- header from snaps is harder to isolate, leave empty for now
         blocks := blocks,
         decls := decls,
         producer := producer,
         graph := graph,
         blockGraph := blockGraph,
         skeletonMap := skelMap
      }
      return (ex, isCtx)
    | none =>
      let graph : DAG.Graph Name := { nodes := #[], nodeToIdx := {}, forward := #[] }
      let blockGraph : DAG.Graph Nat := { nodes := #[], nodeToIdx := {}, forward := #[] }
      let ex : Export := {
         file := doc.meta.uri,
         header := "",
         blocks := #[],
         decls := #[],
         producer := #[],
         graph := graph,
         blockGraph := blockGraph,
         skeletonMap := #[]
      }
      return (ex, #[])

private def semanticBlockIndices (blocks : Array Block) : Array Nat :=
  Id.run do
    let mut out := #[]
    for blk in blocks do
      if !blk.primaryProduces.isEmpty then
        out := out.push blk.idx
    out

private def buildSemanticBlockGraph (e : Export) : DAG.Graph Nat :=
  Id.run do
    let selected := semanticBlockIndices e.blocks
    let mut nodeToIdx : Std.HashMap Nat Nat := {}
    for i in [:selected.size] do
      nodeToIdx := nodeToIdx.insert selected[i]! i

    let mut forward : Array (Array (Nat × EdgeKind)) := Array.replicate selected.size #[]
    let mut seen : Std.HashSet (Nat × Nat × EdgeKind) := {}
    for i in [:selected.size] do
      let origU := selected[i]!
      for (origV, k) in e.blockGraph.forward[origU]! do
        let some j := nodeToIdx.get? origV | continue
        if !seen.contains (i, j, k) then
          seen := seen.insert (i, j, k)
          forward := forward.modify i (·.push (j, k))

    { nodes := selected, nodeToIdx := nodeToIdx, forward := forward }

private def pickBlockRep (comp : Array Nat) : Nat :=
  comp.foldl (init := comp[0]!) fun best x => min best x

private def semanticBlockSkeleton (h : HydratedGraph Nat) (minVulnerability : Nat := 1) :
    Array (Nat × Nat × Nat) :=
  Id.run do
    let mut out := #[]
    for si in [:h.sccs.size] do
      let comp := h.sccs[si]!
      if comp.isEmpty then
        continue
      let origBlock := pickBlockRep (comp.map fun vi => h.toGraph.nodes[vi]!)
      let (vulPaths, vulSrcs) := vulnerabilityOf h origBlock
      if vulSrcs >= minVulnerability then
        out := out.push (origBlock, vulPaths, vulSrcs)
    out.qsort fun a b =>
      if a.2.2 == b.2.2 then a.2.1 > b.2.1 else a.2.2 > b.2.2

private def blockJson (blk : Block) : Json :=
  Json.mkObj
    [ ("idx", toJson blk.idx)
    , ("stableId", toJson blk.stableId)
    , ("startPos", toJson blk.startPos)
    , ("stopPos", toJson blk.stopPos)
    , ("primaryProduces", toJson blk.primaryProduces)
    , ("spineTags", toJson blk.spineTags)
    ]

private def skeletonEntryJson (blocks : Array Block) (entry : Nat × Nat × Nat) : Json :=
  let (origIdx, vulPaths, vulSrcs) := entry
  let blk := blocks[origIdx]!
  Json.mkObj
    [ ("idx", toJson blk.idx)
    , ("stableId", toJson blk.stableId)
    , ("vulPaths", toJson vulPaths)
    , ("vulSrcs", toJson vulSrcs)
    , ("startPos", toJson blk.startPos)
    , ("stopPos", toJson blk.stopPos)
    , ("primaryProduces", toJson blk.primaryProduces)
    , ("spineTags", toJson blk.spineTags)
    ]

def semanticBlocksPayload (ex : Export) : Json :=
  let rawPrimaryBlockCount := ex.blocks.foldl (init := 0) fun acc blk =>
    acc + if blk.primaryProduces.isEmpty then 0 else 1
  let semanticG := buildSemanticBlockGraph ex
  let hydrated := hydrate semanticG
  let skeleton := semanticBlockSkeleton hydrated 1
  let edgeCount := semanticG.forward.foldl (init := 0) fun acc row => acc + row.size
  let semanticBlocks := semanticG.nodes.map fun origIdx => blockJson (ex.blocks[origIdx]!)
  Json.mkObj
    [ ("sourceFile", toJson ex.file)
    , ("rawBlocks", toJson ex.blocks.size)
    , ("rawDecls", toJson ex.decls.size)
    , ("rawPrimaryBlocks", toJson rawPrimaryBlockCount)
    , ("semanticBlockNodes", toJson semanticG.nodes.size)
    , ("semanticBlockEdges", toJson edgeCount)
    , ("semanticSkeletonNodes", toJson skeleton.size)
    , ("blocks", Json.arr semanticBlocks)
    , ("skeleton", Json.arr <| skeleton.map (skeletonEntryJson ex.blocks))
    ]

private def exportCurrentDocFromSnapshots (doc : FileWorker.EditableDocument) (withText : Bool) :
    RequestM (RequestTask (Export × Array Bool)) := do
  let t := IO.AsyncList.waitAll doc.cmdSnaps
  RequestM.mapTaskCostly t fun (snapsList, term?) => do
    match term? with
    | some err => throw (RequestError.ofIoError err)
    | none =>
        let snaps := snapsList.toArray
        exportFromSnaps doc snaps withText

@[server_rpc_method]
def semanticBlocks (params : SemanticBlocksParams) : RequestM (RequestTask Json) := do
  let doc ← readDoc
  let exportTask ← exportCurrentDocFromSnapshots doc params.withText
  RequestM.mapRequestTaskCheap exportTask fun (ex, _) =>
    pure (semanticBlocksPayload ex)

/-- Server RPC: Discover all sliceable targets in the document. -/
@[server_rpc_method]
def getTargets (_pos : Lsp.Position) : RequestM (RequestTask (Array TargetInfo)) := do
  let doc ← readDoc
  let exportTask ← exportCurrentDocFromSnapshots doc false
  RequestM.mapRequestTaskCheap exportTask fun (ex, _) => do
    let mut out := #[]
    for block in ex.blocks do
      if block.primaryProduces.isEmpty then
        continue
      let range : Lsp.Range := {
        start := { line := block.startPos.line - 1, character := block.startPos.column },
        «end» := { line := block.stopPos.line - 1, character := block.stopPos.column }
      }
      for name in block.primaryProduces do
        out := out.push { name := name, range := range }
    return out

/-- Server RPC: compute a slice (block indices) for `params.target` in the currently open document. -/
@[server_rpc_method]
def sliceFor (params : SliceParams) : RequestM (RequestTask Json) := do
  let doc ← readDoc
  let exportTask ← exportCurrentDocFromSnapshots doc params.withText
  RequestM.mapRequestTaskCheap exportTask fun (ex, isCtx) => do
    let target := params.target

    let base : Array Nat := minimalBlocksFor ex target
    let mut chosen : Std.HashSet Nat := {}
    for b in base do
      chosen := chosen.insert b

    if params.withContext && ex.blocks.size > 0 then
      chosen := chosen.insert 0

    if params.withContext && base.size > 0 then
      let hi := base.foldl (fun m x => Nat.max m x) 0
      for i in [:ex.blocks.size] do
        if i ≤ hi && isCtx[i]! then
          chosen := chosen.insert i

    let blocks := chosen.toArray.qsort (· < ·)
    let payload :=
      Json.mkObj
        [ ("file", toJson ex.file)
        , ("target", toJson target)
        , ("blocks", toJson blocks)
        , ("export", toJson ex)
        ]
    pure payload

/-- Server RPC: render a slice into text. -/
@[server_rpc_method]
def renderSlice (params : RenderParams) : RequestM (RequestTask String) := do
  return RequestTask.pure (renderIndices params.exportData params.blocks)

end DAG.Server
