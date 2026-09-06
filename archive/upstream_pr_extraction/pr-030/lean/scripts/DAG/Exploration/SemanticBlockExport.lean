import Lean
import Lean.Data.Json
import Lean.Server.FileWorker

import DAG.Basic
import DAG.Util
import DAG.Hydrate
import DAG.Analysis

open Lean
open Lean.Server
open Lean.Server.FileWorker
open DAG

private def defaultInput : String :=
  "lean/InfoGeometry/Canonical/GrandSynthesis.lean"

private def defaultOutput : String :=
  "reports/dag/GrandSynthesis.semantic-block.json"

private def argD (args : Array String) (idx : Nat) (fallback : String) : String :=
  args.getD idx fallback

private def moduleNameGuessFromFile (file : System.FilePath) : Option Name :=
  let parts := file.toString.splitOn "/"
  let relParts :=
    match parts.dropWhile (· != "lean") with
    | [] => parts
    | _ :: rest => rest
  match relParts.reverse with
  | [] => none
  | leafWithExt :: revRest =>
      if !leafWithExt.endsWith ".lean" then
        none
      else
        let leaf := (leafWithExt.dropEnd 5).toString
        let modParts := revRest.reverse ++ [leaf]
        some <| modParts.foldl (init := Name.anonymous) fun acc part =>
          if part.isEmpty then acc else Name.str acc part

private def openNullStream : IO IO.FS.Stream := do
  let h ← IO.FS.Handle.mk "/dev/null" IO.FS.Mode.write
  pure <| IO.FS.Stream.ofHandle h

private def mkDocumentMeta (file : System.FilePath) : IO DocumentMeta := do
  let realFile ← IO.FS.realPath file
  let text := (← IO.FS.readFile realFile).crlfToLf.toFileMap
  pure {
    uri := System.Uri.pathToUri realFile
    mod := moduleNameGuessFromFile realFile |>.getD `Main
    version := 0
    text := text
    dependencyBuildMode := .never
  }

private def mkStableBlockId (startUtf8 stopUtf8 : String.Pos.Raw) : String :=
  s!"block:{startUtf8.byteIdx}-{stopUtf8.byteIdx}"

private def classifyProducedDecls (decls : Array Name) : Array Name × Array Name := Id.run do
  let mut primaryDecls : Array Name := #[]
  let mut auxDecls : Array Name := #[]
  for n in decls do
    if isGeneratedOrUnstableName n then
      auxDecls := auxDecls.push n
    else
      primaryDecls := primaryDecls.push n
  (primaryDecls, auxDecls)

structure RawBlock where
  idx : Nat
  stableId : String
  startPos : Position
  stopPos : Position
  primaryProduces : Array Name
  auxProduces : Array Name
  deriving ToJson, Inhabited

structure RawExport where
  file : String
  blocks : Array RawBlock
  decls : Array Name
  producer : Array Nat
  graph : Graph Name
  blockGraph : Graph Nat

private def buildGraphFromEnvOn (env : Environment) (decls : Array Name) : Graph Name :=
  Id.run do
    let decls := decls.qsort Name.lt
    let mut nodeToIdx : Std.HashMap Name Nat := {}
    for i in [:decls.size] do
      nodeToIdx := nodeToIdx.insert decls[i]! i
    let mut forward : Array (Array (Nat × EdgeKind)) :=
      Array.replicate decls.size #[]
    for i in [:decls.size] do
      let n := decls[i]!
      match env.find? n with
      | none => pure ()
      | some ci =>
          let edges := edgesFromConstantInfo ci
          for (dep, k) in edges do
            match nodeToIdx.get? dep with
            | none => pure ()
            | some j => forward := forward.modify i (·.push (j, k))
    { nodes := decls, nodeToIdx := nodeToIdx, forward := forward }

private def producerMap (decls : Array Name) (producer : Array Nat) : Std.HashMap Name Nat :=
  Id.run do
    let mut m : Std.HashMap Name Nat := {}
    let n := Nat.min decls.size producer.size
    for i in [:n] do
      m := m.insert decls[i]! producer[i]!
    m

private def buildBlockGraph (constG : Graph Name) (prod : Std.HashMap Name Nat) (numBlocks : Nat) :
    Graph Nat :=
  Id.run do
    let nodes := Array.range numBlocks
    let mut nodeToIdx : Std.HashMap Nat Nat := {}
    for i in [:nodes.size] do
      nodeToIdx := nodeToIdx.insert nodes[i]! i

    let mut forward : Array (Array (Nat × EdgeKind)) := Array.replicate numBlocks #[]
    let mut seen : Std.HashSet (Nat × Nat × EdgeKind) := {}

    for ui in [:constG.nodes.size] do
      let u := constG.nodes[ui]!
      let some bu := prod.get? u | continue
      for (vj, k) in constG.forward[ui]! do
        let v := constG.nodes[vj]!
        let some bv := prod.get? v | continue
        if bu != bv && !seen.contains (bu, bv, k) then
          seen := seen.insert (bu, bv, k)
          forward := forward.modify bu (·.push (bv, k))

    { nodes := nodes, nodeToIdx := nodeToIdx, forward := forward }

private def primaryDeclSet (blocks : Array RawBlock) : Std.HashSet Name :=
  Id.run do
    let mut out : Std.HashSet Name := {}
    for blk in blocks do
      for n in blk.primaryProduces do
        out := out.insert n
    out

private def exportDocument (doc : EditableDocument) : IO RawExport := do
  let (snapsList, err?) := doc.cmdSnaps.waitAll.get
  match err? with
  | some err => throw err
  | none =>
      let snaps := snapsList.toArray
      let inputCtx := doc.meta.mkInputContext
      let mut blocks : Array RawBlock := #[]
      let mut decls : Array Name := #[]
      let mut producer : Array Nat := #[]
      let baseSeen : NameSet :=
        match doc.initSnap.processedResult.get with
        | some headerState =>
            headerState.cmdState.env.constants.fold (init := ({} : NameSet)) fun s n _ => s.insert n
        | none => {}
      let mut seen : NameSet := baseSeen
      let mut prevEnd : String.Pos.Raw := ⟨0⟩

      for i in [:snaps.size] do
        let some snap := snaps[i]? | continue
        let stop := snap.endPos
        let start := prevEnd
        prevEnd := stop
        if start >= stop then
          continue

        let txtFull := toString (inputCtx.substring start stop)
        if txtFull.trimAscii.isEmpty then
          continue

        let startPos := inputCtx.fileMap.toPosition start
        let stopPos := inputCtx.fileMap.toPosition stop
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
        let newDecls := newDecls0.qsort Name.lt

        let blockIdx := blocks.size
        if newDecls.size > 0 then
          decls := decls ++ newDecls
          producer := producer ++ Array.replicate newDecls.size blockIdx

        let (primaryDecls, auxDecls) := classifyProducedDecls newDecls
        blocks := blocks.push {
          idx := blockIdx
          stableId := mkStableBlockId start stop
          startPos := startPos
          stopPos := stopPos
          primaryProduces := primaryDecls
          auxProduces := auxDecls
        }

      let finalEnv := snaps.back?.map (·.env) |>.getD (← importModules #[] {})
      let graph := buildGraphFromEnvOn finalEnv decls
      let prodMap := producerMap decls producer
      let blockGraph := buildBlockGraph graph prodMap blocks.size
      pure {
        file := doc.meta.uri
        blocks := blocks
        decls := decls
        producer := producer
        graph := graph
        blockGraph := blockGraph
      }

private def semanticBlockIndices (blocks : Array RawBlock) : Array Nat :=
  Id.run do
    let mut out := #[]
    for blk in blocks do
      if !blk.primaryProduces.isEmpty then
        out := out.push blk.idx
    out

private def buildSemanticBlockGraph (e : RawExport) : Graph Nat :=
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

private def semanticBlockSkeleton (_blocks : Array RawBlock) (h : HydratedGraph Nat)
    (minVulnerability : Nat := 1) : Array (Nat × Nat × Nat) :=
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

private def skeletonEntryJson (blocks : Array RawBlock) (entry : Nat × Nat × Nat) : Json :=
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
    ]

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let argv := args.toArray
  let inputFile := argD argv 0 defaultInput
  let outputFile := argD argv 1 defaultOutput

  IO.println s!"[SemanticBlockExport] Elaborating {inputFile}..."

  let doc ← mkDocumentMeta (System.FilePath.mk inputFile)
  let outStream ← openNullStream
  let errStream ← openNullStream
  let initParams : Lsp.InitializeParams := { capabilities := {} }
  let opts := Elab.async.setIfNotSet ({} : Options) false
  let (_, state) ← initializeWorker doc outStream errStream initParams opts
  let initSnap := state.doc.initSnap
  IO.println s!"[SemanticBlockExport] headerParsedOk={initSnap.result?.isSome}"

  let ex ← exportDocument state.doc
  let rawPrimaryBlockCount := ex.blocks.foldl (init := 0) fun acc blk =>
    acc + if blk.primaryProduces.isEmpty then 0 else 1
  let semanticG := buildSemanticBlockGraph ex
  let hydrated := hydrate semanticG
  let skeleton := semanticBlockSkeleton ex.blocks hydrated 1
  let edgeCount := semanticG.forward.foldl (init := 0) fun acc row => acc + row.size
  let semanticBlocks := semanticG.nodes.map fun origIdx => toJson (ex.blocks[origIdx]!)

  let payload := Json.mkObj
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

  let outPath := System.FilePath.mk outputFile
  if let some p := outPath.parent then
    IO.FS.createDirAll p
  IO.FS.writeFile outPath payload.pretty
  IO.println s!"[SemanticBlockExport] raw blocks={ex.blocks.size}, raw decls={ex.decls.size}, raw primary blocks={rawPrimaryBlockCount}"
  IO.println s!"[SemanticBlockExport] wrote {outputFile} (nodes={semanticG.nodes.size}, edges={edgeCount}, skeleton={skeleton.size})"
  pure 0
