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
  let mut seen : NameSet := {}
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
            if DAG.isFromMainModule snap.env n then
              (arr.push n, s)
            else
              (arr, s))
        (#[], seen)
    seen := seen'
    let newDecls : Array Name := newDecls0.qsort Name.lt

    let blockIdx := blocks.size
    if newDecls.size > 0 then
      decls := decls ++ newDecls
      producer := producer ++ Array.replicate newDecls.size blockIdx

    let blockMorphisms ← extractMorphisms snap.infoTree

    let mut docStrings : Array String := #[]
    let mut typeStrings : Array String := #[]
    for n in newDecls do
      let doc ← match ← Lean.findDocString? snap.env n with
                | some d => pure d
                | none => pure ""
      docStrings := docStrings.push doc
      let tstr ← match snap.env.find? n with
                 | some ci => pure (toString ci.type)
                 | none => pure ""
      typeStrings := typeStrings.push tstr

    blocks := blocks.push
      { idx := blockIdx
        startUtf8 := start
        stopUtf8 := stop
        startPos := startPos
        stopPos := stopPos
        text := if withText then txtFull else ""
        scopes := scopeStack.reverse.toArray
        produces := newDecls
        affects := #[]
        morphisms := blockMorphisms
        docStrings := docStrings
        typeStrings := typeStrings }

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
      let skelPairs := DAG.extractTheorySkeleton hydratedG 1
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

/-- Server RPC: Discover all sliceable targets in the document. -/
@[server_rpc_method]
def getTargets (_pos : Lsp.Position) : RequestM (RequestTask (Array TargetInfo)) := do
  let doc ← readDoc
  let t := IO.AsyncList.waitAll doc.cmdSnaps
  RequestM.mapTaskCostly t fun (snapsList, _) => do
    let (ex, _) ← exportFromSnaps doc snapsList.toArray false
    let mut out := #[]
    for i in [:ex.decls.size] do
      let name := ex.decls[i]!
      let bIdx := ex.producer[i]!
      let some block := ex.blocks[bIdx]? | continue
      let range : Lsp.Range := {
        start := { line := block.startPos.line - 1, character := block.startPos.column },
        «end» := { line := block.stopPos.line - 1, character := block.stopPos.column }
      }
      out := out.push { name := name, range := range }
    return out

/-- Server RPC: compute a slice (block indices) for `params.target` in the currently open document. -/
@[server_rpc_method]
def sliceFor (params : SliceParams) : RequestM (RequestTask Json) := do
  let doc ← readDoc
  let target := params.target

  -- Stop as soon as the target constant exists in the environment.
  let pred : Snapshot → Bool := fun s => (s.env.find? target).isSome
  let t := IO.AsyncList.waitUntil pred doc.cmdSnaps
  RequestM.mapTaskCostly t fun (snapsList, term?) => do
    match term? with
    | some err => throw (RequestError.ofIoError err)
    | none =>
      let snaps := snapsList.toArray
      if snaps.isEmpty then
        throw (RequestError.invalidParams "no command snapshots available for this document")

      let (ex, isCtx) ← exportFromSnaps doc snaps params.withText

      let base : Array Nat := minimalBlocksFor ex target
      let mut chosen : Std.HashSet Nat := {}
      for b in base do
        chosen := chosen.insert b

      -- ensure header/imports (block 0 starts at pos 0 in your exporter)
      if params.withContext && ex.blocks.size > 0 then
        chosen := chosen.insert 0

      if params.withContext && base.size > 0 then
        let hi := base.foldl (fun m x => Nat.max m x) 0
        for i in [:ex.blocks.size] do
          if i ≤ hi && isCtx[i]! then
            chosen := chosen.insert i

      let blocks := chosen.toArray.qsort (· < ·)

      -- Return: blocks + (optionally) texts
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
