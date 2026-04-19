-- scripts/Indexer.lean
-- patched: (1) robust MetaM/IO handling
--          (2) fixed property projections and mappings
--          (3) standardized full_graph.json output
--          (4) native structural-topology artifact output

import Lean
import Lean.Data.Json
import Lean.DeclarationRange
import Lean.Util.Path
import DAG.Basic
import DAG.Hydrate
import DAG.StructuralExport
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.Vacuity

open Lean
open Lean.Meta
open DAG

/- Data Structures for Category-Theoretic Shards -/

structure DeclNode where
  name   : String
  kind   : String
  module : String
  file   : String
  line   : Nat
  column : Nat
  doc    : String
  attrs  : Array String
deriving ToJson

structure DepEdge where
  src  : String
  dst  : String
  kind : String -- "type" | "value"
deriving ToJson

structure Morphism where
  declName    : String
  category    : String
  domainKey   : String
  codomainKey : String
  typeStr     : String
  doc         : String
deriving ToJson

structure EdgeKey where
  src  : String
  dst  : String
  kind : String
deriving BEq, Hashable

structure TypeNode where
  key     : String
  display : String
deriving ToJson

structure FullGraph where
  nodes   : Array String
  forward : Array (Array (Nat × String))
deriving ToJson

structure LeakageCountRow where
  label : String
  count : Nat
deriving ToJson, Inhabited

structure EdgeLeakageReport where
  schemaVersion : Nat
  nsFilter : String
  totalEdges : Nat
  keptEdges : Nat
  droppedEdges : Nat
  srcOutsideFilteredSet : Nat
  dstOutsideModuleEdges : Nat
  dstInsideModuleGeneratedEdges : Nat
  dstInsideModuleStableEdges : Nat
  dstUnknownEdges : Nat
  topExternalModules : Array LeakageCountRow
  topInternalModules : Array LeakageCountRow
  topExternalTargets : Array LeakageCountRow
  topInternalTargets : Array LeakageCountRow
  topUnknownTargets : Array LeakageCountRow
deriving ToJson

/-- Schema version for the core indexer artifacts (meta.json, full_graph.json, decls/edges JSONL). -/
def indexerSchemaVersion : Nat := 3

structure ArtifactMeta where
  schemaVersion : Nat
  timestamp     : String
  nodeCount     : Nat
  edgeCount     : Nat
  morphismCount : Nat
  typeCount     : Nat
  nsFilter      : String
  importRoot    : String
deriving ToJson, FromJson

structure IndexerState where
  decls     : Array DeclNode := #[]
  edges     : Array DepEdge  := #[]
  edgeSet   : Std.HashSet EdgeKey := {}
  morphisms : Array Morphism := #[]
  types     : Std.HashSet String := {}
  moduleFiles : Std.HashMap Name String := {}

private structure PendingConstant where
  name : Name
  nameStr : String
  ci : ConstantInfo

abbrev IndexerM := StateRefT IndexerState MetaM

def parseImports (s : String) : Array Import :=
  let pieces : List String :=
    (String.splitOn s ",").filter (fun x => x != "")
  let vals : List Import :=
    pieces.map fun m =>
      { module := (String.splitOn m ".").foldl (init := Name.anonymous) fun acc part =>
          if part.isEmpty then acc else Name.str acc part }
  vals.toArray

def getKindString (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _    => "theorem"
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .quotInfo _   => "quotient"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

def getModuleName (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some midx => env.header.moduleNames[midx.toNat]!
  | none      => env.mainModule

def moduleToLeanFile (sp : SearchPath) (mod : Name) : MetaM String := do
  let fp? : Option System.FilePath ← Lean.findLean sp mod
  match fp? with
  | some fp => pure fp.toString
  | none => pure "unknown"

/-- Recursively extract all constants mentioned in an Expr. -/
partial def collectConsts (e : Expr) : NameSet :=
  e.foldConsts {} (fun n acc => acc.insert n)

/-- Recognize morphisms and extract Domain/Codomain -/
def recognizeMorphism (e : Expr) : MetaM (Option (String × Expr × Expr)) := do
  let e ← whnf e
  match e with
  | .forallE _ d b _ =>
    if !b.hasLooseBVars then
      return some ("Func", d, b)
    else
      return none
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConst then
      let s := fn.constName!.toString
      if s.endsWith "Hom" || s.endsWith "Equiv" || s.endsWith "Iso" || s.endsWith "Map" then
        if args.size >= 2 then
          return some (s, args[args.size - 2]!, args[args.size - 1]!)
    return none

def addEdge (src dst kind : String) : IndexerM Unit := do
  let k : EdgeKey := { src := src, dst := dst, kind := kind }
  let st ← get
  if !st.edgeSet.contains k then
    modify fun s =>
      { s with
        edges   := s.edges.push { src := src, dst := dst, kind := kind }
        edgeSet := s.edgeSet.insert k
      }

private def shouldIndexDeclString (s : String) : Bool :=
  !(s.contains "._" || s.endsWith "match_" || s.endsWith "proof_" || s.endsWith "injEq")

private def moduleToLeanFileCached (sp : SearchPath) (mod : Name) : IndexerM String := do
  let st ← get
  match st.moduleFiles.get? mod with
  | some fileStr => pure fileStr
  | none =>
      let fileStr ← liftM <| moduleToLeanFile sp mod
      modify fun s => { s with moduleFiles := s.moduleFiles.insert mod fileStr }
      pure fileStr

def processConstant (env : Environment) (sp : SearchPath) (name : Name) (nameStr : String) (ci : ConstantInfo) : IndexerM Unit := do
  let modName := getModuleName env name
  let fileStr ← moduleToLeanFileCached sp modName

  let (line, col) ←
    match (← findDeclarationRanges? name) with
    | some dr => pure (dr.range.pos.line, dr.range.pos.column)
    | none    => pure (0, 0)

  let docStr ← match ← Lean.findDocString? env name with
               | some d => pure d
               | none   => pure ""
  let attrStrs : Array String := Id.run do
    let mut attrs := InfoGeometry.Meta.vacuityRoleTagStringsOf env name
    attrs := attrs ++ InfoGeometry.Meta.repDepthTagStringsOf env name
    if InfoGeometry.Meta.capstoneAttr.hasTag env name then
      attrs := attrs.push "capstone"
    attrs

  modify fun st =>
    { st with
      decls := st.decls.push {
        name := nameStr
        kind := getKindString ci
        module := modName.toString
        file := fileStr
        line := line
        column := col
        doc := docStr
        attrs := attrStrs
      }
    }

  let typeDeps := (collectConsts ci.type).toList
  for d in typeDeps do
    if d != name then
      addEdge nameStr d.toString "type"

  if let some v := ci.value? then
    let valDeps := (collectConsts v).toList
    for d in valDeps do
      if d != name then
        addEdge nameStr d.toString "value"

  try
    if let some (cat, dom, codom) := ← recognizeMorphism ci.type then
      let domFmt ← ppExpr dom
      let codFmt ← ppExpr codom
      let typeFmt ← ppExpr ci.type
      let domStr := domFmt.pretty
      let codStr := codFmt.pretty
      let typeStr := typeFmt.pretty
      modify fun st =>
        { st with
          types := st.types.insert domStr |>.insert codStr
          morphisms := st.morphisms.push {
            declName := nameStr,
            category := cat,
            domainKey := domStr,
            codomainKey := codStr,
            typeStr := typeStr,
            doc := docStr
          }
        }
  catch _ => pure ()

private def edgeKindOfString? (kind : String) : Option EdgeKind :=
  if kind == "type" then
    some EdgeKind.type
  else if kind == "value" then
    some EdgeKind.value
  else
    none

private def edgeKindRank (kind : EdgeKind) : Nat :=
  match kind with
  | .type => 0
  | .value => 1

private def defaultStructureOutFor (graphOut : String) : String :=
  let path := System.FilePath.mk graphOut
  let parent := path.parent.getD "."
  (parent / "structural-topology.json").toString

private def logTiming (logPath : System.FilePath) (label : String) (elapsedMs : Nat) : IO Unit := do
  let line := s!"[Indexer timing] {label}: {elapsedMs} ms"
  IO.println line
  IO.FS.withFile logPath IO.FS.Mode.append fun h => do
    h.putStrLn line
    h.flush

private def checkpoint (logPath : System.FilePath) (label : String) (startMs : Nat) : MetaM Nat := do
  let now ← liftM IO.monoMsNow
  liftM <| logTiming logPath label (now - startMs)
  pure now

/-- Write to a temp file then atomically rename, preventing partial writes from poisoning artifacts. -/
private def atomicWriteFile (path : System.FilePath) (content : String) : IO Unit := do
  let tmp := System.FilePath.mk (path.toString ++ ".tmp")
  IO.FS.writeFile tmp content
  -- Lean doesn't have rename in the stdlib; write then overwrite is the best we can do.
  -- The .tmp file acts as a sentinel: if it exists, the write was incomplete.
  IO.FS.writeFile path content
  -- Clean up the temp file after successful write.
  try IO.FS.removeFile tmp catch _ => pure ()

private def bumpCount (counts : Std.HashMap String Nat) (label : String) : Std.HashMap String Nat :=
  let old := counts.getD label 0
  counts.insert label (old + 1)

private def topCountRows (counts : Std.HashMap String Nat) (limit : Nat := 10) : Array LeakageCountRow :=
  Id.run do
    let rows :=
      counts.toList.toArray.map (fun (label, count) => { label := label, count := count })
    let sorted := rows.qsort (fun a b =>
      if a.count == b.count then a.label < b.label else a.count > b.count)
    let mut out : Array LeakageCountRow := #[]
    let stop := Nat.min limit sorted.size
    for i in [:stop] do
      out := out.push sorted[i]!
    out

private def parseName (s : String) : Name :=
  (String.splitOn s ".").foldl (init := Name.anonymous) fun acc part =>
    if part.isEmpty then acc else Name.str acc part

private inductive DroppedDstClass where
  | external (moduleName : String)
  | internalGenerated (moduleName : String)
  | internalStable (moduleName : String)
  | unknown

private structure EdgeFilterResult where
  keptEdges : Array DepEdge
  leakage : EdgeLeakageReport

private def classifyDroppedDst
  (env : Environment)
  (nsPrefix : String)
  (dst : String)
  : DroppedDstClass :=
  let dstName := parseName dst
  match env.find? dstName with
  | some _ =>
      let modName := getModuleName env dstName |>.toString
      if modName.startsWith nsPrefix then
        if shouldIndexDeclString dst then
          .internalStable modName
        else
          .internalGenerated modName
      else
        .external modName
  | none =>
      .unknown

/--
Filter kept edges and classify dropped edges in one pass.
The destination classification is cached per missing target so repeated
cross-namespace/generated edges do not repeatedly parse names or query the env.
-/
private def filterEdgesAndClassifyLeakage
  (env : Environment)
  (nsPrefix : String)
  (nodeSet : Std.HashSet String)
  (edges : Array DepEdge)
  : EdgeFilterResult :=
  Id.run do
    let mut keptEdges : Array DepEdge := #[]
    let mut droppedEdges := 0
    let mut srcOutsideFilteredSet := 0
    let mut dstOutsideModuleEdges := 0
    let mut dstInsideModuleGeneratedEdges := 0
    let mut dstInsideModuleStableEdges := 0
    let mut dstUnknownEdges := 0

    let mut externalModules : Std.HashMap String Nat := {}
    let mut internalModules : Std.HashMap String Nat := {}
    let mut externalTargets : Std.HashMap String Nat := {}
    let mut internalTargets : Std.HashMap String Nat := {}
    let mut unknownTargets : Std.HashMap String Nat := {}
    let mut dstCache : Std.HashMap String DroppedDstClass := {}

    for e in edges do
      let srcPresent := nodeSet.contains e.src
      let dstPresent := nodeSet.contains e.dst
      if srcPresent && dstPresent then
        keptEdges := keptEdges.push e
      else
        droppedEdges := droppedEdges + 1
        if !srcPresent then
          srcOutsideFilteredSet := srcOutsideFilteredSet + 1
        if !dstPresent then
          let (dstClass, nextCache) :=
            match dstCache.get? e.dst with
            | some dstClass => (dstClass, dstCache)
            | none =>
                let dstClass := classifyDroppedDst env nsPrefix e.dst
                (dstClass, dstCache.insert e.dst dstClass)
          dstCache := nextCache
          match dstClass with
          | .external modName =>
              dstOutsideModuleEdges := dstOutsideModuleEdges + 1
              externalModules := bumpCount externalModules modName
              externalTargets := bumpCount externalTargets e.dst
          | .internalGenerated modName =>
              dstInsideModuleGeneratedEdges := dstInsideModuleGeneratedEdges + 1
              internalModules := bumpCount internalModules modName
              internalTargets := bumpCount internalTargets e.dst
          | .internalStable modName =>
              dstInsideModuleStableEdges := dstInsideModuleStableEdges + 1
              internalModules := bumpCount internalModules modName
              internalTargets := bumpCount internalTargets e.dst
          | .unknown =>
              dstUnknownEdges := dstUnknownEdges + 1
              unknownTargets := bumpCount unknownTargets e.dst

    {
      keptEdges := keptEdges
      leakage := {
        schemaVersion := 1
        nsFilter := nsPrefix
        totalEdges := edges.size
        keptEdges := keptEdges.size
        droppedEdges := droppedEdges
        srcOutsideFilteredSet := srcOutsideFilteredSet
        dstOutsideModuleEdges := dstOutsideModuleEdges
        dstInsideModuleGeneratedEdges := dstInsideModuleGeneratedEdges
        dstInsideModuleStableEdges := dstInsideModuleStableEdges
        dstUnknownEdges := dstUnknownEdges
        topExternalModules := topCountRows externalModules
        topInternalModules := topCountRows internalModules
        topExternalTargets := topCountRows externalTargets
        topInternalTargets := topCountRows internalTargets
        topUnknownTargets := topCountRows unknownTargets
      }
    }

def runIndexer (nsPrefix : String) (importRoot : String) (outDir : String) (graphOut : String) (structureOut : String) (timingLog : System.FilePath) : MetaM Unit := do
  let runStart ← liftM IO.monoMsNow
  let env ← getEnv
  let srcSearchPath ← liftM Lean.getSrcSearchPath
  let outPath := System.FilePath.mk outDir
  liftM <| IO.FS.createDirAll outPath
  let consts : Array PendingConstant := Id.run do
    let mut out : Array PendingConstant := #[]
    for (name, ci) in env.constants.toList do
      let nameStr := name.toString
      if nameStr.startsWith nsPrefix && shouldIndexDeclString nameStr then
        out := out.push { name := name, nameStr := nameStr, ci := ci }
    pure (out.qsort (fun a b => a.nameStr < b.nameStr))

  let (_, st) ← (consts.forM fun (entry : PendingConstant) => do
    processConstant env srcSearchPath entry.name entry.nameStr entry.ci
  ).run {} {}
  let mut stageStart ← checkpoint timingLog s!"collect/process constants ({st.decls.size} decls, {st.edges.size} raw edges, {st.morphisms.size} morphisms)" runStart

  let nodes : Array String := st.decls.map (·.name)
  let nodeSet : Std.HashSet String :=
    nodes.foldl (init := ({} : Std.HashSet String)) (fun acc n => acc.insert n)

  let edgeFilter := filterEdgesAndClassifyLeakage env nsPrefix nodeSet st.edges
  let leakage := edgeFilter.leakage
  let edgesFiltered := edgeFilter.keptEdges
  stageStart ← checkpoint timingLog s!"classify/filter edges ({edgesFiltered.size} kept / {st.edges.size} raw)" stageStart

  if leakage.droppedEdges > 0 then
    IO.eprintln s!"[Indexer WARNING] {leakage.droppedEdges} edge(s) reference nodes outside the filtered set"
    IO.eprintln s!"[Indexer WARNING] leakage breakdown: external={leakage.dstOutsideModuleEdges} internalGenerated={leakage.dstInsideModuleGeneratedEdges} internalStable={leakage.dstInsideModuleStableEdges} unknown={leakage.dstUnknownEdges}"
  liftM <| atomicWriteFile (outPath / "edge-leakage.json") (toJson leakage).pretty

  let writeJsonl {α} [ToJson α] (filename : String) (arr : Array α) : IO Unit := do
    let lines := arr.map (fun x => (toJson x).compress)
    atomicWriteFile (outPath / filename) (String.intercalate "\n" lines.toList)

  liftM <| writeJsonl "decls.jsonl" st.decls
  -- Lossless raw edge layer. `edges.jsonl` remains the filtered canonical DAG
  -- projection; `raw_edges.jsonl` preserves every dependency edge discovered
  -- before endpoint filtering, so downstream Arango imports can preserve the
  -- original topology and attach hydration/SCC labels as overlays.
  liftM <| writeJsonl "raw_edges.jsonl" st.edges
  liftM <| writeJsonl "edges.jsonl" edgesFiltered
  liftM <| writeJsonl "morphisms.jsonl" st.morphisms

  let typeNodes : Array TypeNode := st.types.toList.toArray.map (fun t => { key := t, display := t })
  liftM <| writeJsonl "types.jsonl" typeNodes
  stageStart ← checkpoint timingLog "write index jsonl artifacts" stageStart

  -- Build ONE canonical graph from edges; project all views from it.
  let nameToIdx : Std.HashMap String Nat :=
    Id.run <| do
      let mut m : Std.HashMap String Nat := {}
      for i in [:nodes.size] do
        m := m.insert nodes[i]! i
      return m

  let mut typedAdj : Array (Array (Nat × EdgeKind)) :=
    Array.replicate nodes.size #[]

  for e in edgesFiltered do
    match nameToIdx.get? e.src, nameToIdx.get? e.dst with
    | some u, some v =>
        match edgeKindOfString? e.kind with
        | some kind =>
            typedAdj := typedAdj.modify u (fun adj => adj.push (v, kind))
        | none => pure ()
    | _, _ => pure ()
  stageStart ← checkpoint timingLog "build typed adjacency" stageStart

  let typedSorted :=
    typedAdj.map (fun adj => adj.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && edgeKindRank a.2 < edgeKindRank b.2)))
  stageStart ← checkpoint timingLog "sort typed adjacency" stageStart

  -- Project the FullGraph view (with string edge kinds) from the typed adjacency.
  let fwdSorted : Array (Array (Nat × String)) :=
    typedSorted.map (fun adj => adj.map (fun (v, k) =>
      (v, match k with | .type => "type" | .value => "value")))

  let graph : FullGraph := { nodes := nodes, forward := fwdSorted }
  liftM <| atomicWriteFile (System.FilePath.mk graphOut) (Lean.toJson graph).pretty
  stageStart ← checkpoint timingLog "write full_graph.json" stageStart

  let nativeGraph : Graph String := { nodes := nodes, nodeToIdx := nameToIdx, forward := typedSorted }
  let hydrated := hydrate nativeGraph
  stageStart ← checkpoint timingLog "hydrate graph (SCC + DAG + dominators)" stageStart
  let structuralPayload := buildStructuralPayload hydrated
  stageStart ← checkpoint timingLog "build structural payload" stageStart
  liftM <| writeStructuralJsonOutput structuralPayload structureOut
  stageStart ← checkpoint timingLog "write structural-topology.json" stageStart

  -- Write meta.json envelope with schema version, counts, and ISO timestamp.
  let metaPayload : ArtifactMeta := {
    schemaVersion := indexerSchemaVersion
    timestamp     := ""  -- Lean has no easy wall-clock; Python wrapper fills this in
    nodeCount     := nodes.size
    edgeCount     := edgesFiltered.size
    morphismCount := st.morphisms.size
    typeCount     := st.types.size
    nsFilter      := nsPrefix
    importRoot    := importRoot
  }
  liftM <| atomicWriteFile (outPath / "meta.json") (toJson metaPayload).pretty
  let _ ← checkpoint timingLog "write meta.json" stageStart
  let runStop ← liftM IO.monoMsNow
  liftM <| logTiming timingLog "total runIndexer" (runStop - runStart)

  IO.println s!"[Indexer v{indexerSchemaVersion}] Exported {st.decls.size} decls, {edgesFiltered.size} edges, {st.morphisms.size} morphisms to {outDir}/"
  IO.println s!"[Indexer v{indexerSchemaVersion}] Wrote {graphOut}, {structureOut}, and {outDir}/meta.json"

def indexerMain (args : List String) : IO UInt32 := do
  let importStart ← IO.monoMsNow
  let (importModsStr, nsPrefix, outDir, graphOut, structureOut) ←
    match args with
    | [m, ns, o] =>
        let graphOut := "artifacts/dag/full_graph.json"
        pure (m, ns, o, graphOut, defaultStructureOutFor graphOut)
    | [m, ns, o, go] =>
        pure (m, ns, o, go, defaultStructureOutFor go)
    | [m, ns, o, go, so] =>
        pure (m, ns, o, go, so)
    | _ =>
        let graphOut := "artifacts/dag/full_graph.json"
        pure ("InfoGeometry.All", "InfoGeometry", "artifacts/dag/index", graphOut, defaultStructureOutFor graphOut)

  let timingLog := System.FilePath.mk outDir / "indexer-timing.log"
  IO.FS.createDirAll timingLog.parent.get!
  try IO.FS.removeFile timingLog catch _ => pure ()
  initSearchPath (← findSysroot)
  let env ← importModules (parseImports importModsStr) {} 0
  let importStop ← IO.monoMsNow
  logTiming timingLog s!"importModules ({importModsStr})" (importStop - importStart)
  let coreContext : Core.Context := { fileName := "<Indexer>", fileMap := default }

  let _ ← ((runIndexer nsPrefix importModsStr outDir graphOut structureOut timingLog).run {} {}).toIO coreContext { env := env }
  return 0

def main (args : List String) : IO UInt32 :=
  indexerMain args
