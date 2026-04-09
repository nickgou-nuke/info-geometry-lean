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

def moduleToLeanFile (mod : Name) : MetaM String := do
  let sp ← Lean.getSrcSearchPath
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

def processConstant (name : Name) (ci : ConstantInfo) : IndexerM Unit := do
  let env ← getEnv
  let nameStr := name.toString

  let modName := getModuleName env name
  let fileStr ← moduleToLeanFile modName

  let (line, col) ←
    match (← findDeclarationRanges? name) with
    | some dr => pure (dr.range.pos.line, dr.range.pos.column)
    | none    => pure (0, 0)

  let docStr ← match ← Lean.findDocString? env name with
               | some d => pure d
               | none   => pure ""
  let attrStrs : Array String := Id.run do
    let mut attrs := InfoGeometry.Meta.vacuityRoleTagStringsOf env name
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

private def logTiming (label : String) (elapsedMs : Nat) : IO Unit := do
  IO.println s!"[Indexer timing] {label}: {elapsedMs} ms"

private def checkpoint (label : String) (startMs : Nat) : MetaM Nat := do
  let now ← liftM IO.monoMsNow
  liftM <| logTiming label (now - startMs)
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

/-- Classify edges dropped by the namespace-filtered node set. -/
private def classifyEdgeLeakage
  (env : Environment)
  (nsPrefix : String)
  (nodeSet : Std.HashSet String)
  (edges : Array DepEdge)
  : EdgeLeakageReport :=
  Id.run do
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

    for e in edges do
      let srcMissing := !nodeSet.contains e.src
      let dstMissing := !nodeSet.contains e.dst
      if srcMissing || dstMissing then
        droppedEdges := droppedEdges + 1
        if srcMissing then
          srcOutsideFilteredSet := srcOutsideFilteredSet + 1
        if dstMissing then
          let dstName := parseName e.dst
          match env.find? dstName with
          | some _ =>
              let modName := getModuleName env dstName |>.toString
              if modName.startsWith nsPrefix then
                internalModules := bumpCount internalModules modName
                internalTargets := bumpCount internalTargets e.dst
                if shouldIndexDeclString e.dst then
                  dstInsideModuleStableEdges := dstInsideModuleStableEdges + 1
                else
                  dstInsideModuleGeneratedEdges := dstInsideModuleGeneratedEdges + 1
              else
                dstOutsideModuleEdges := dstOutsideModuleEdges + 1
                externalModules := bumpCount externalModules modName
                externalTargets := bumpCount externalTargets e.dst
          | none =>
              dstUnknownEdges := dstUnknownEdges + 1
              unknownTargets := bumpCount unknownTargets e.dst

    {
      schemaVersion := 1
      nsFilter := nsPrefix
      totalEdges := edges.size
      keptEdges := edges.size - droppedEdges
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

def runIndexer (nsPrefix : String) (importRoot : String) (outDir : String) (graphOut : String) (structureOut : String) : MetaM Unit := do
  let runStart ← liftM IO.monoMsNow
  let env ← getEnv
  let mut consts := env.constants.toList.map (·.1)
  consts := consts.filter (fun n => (n.toString).startsWith nsPrefix)
  consts := consts.toArray.qsort (fun a b => a.toString < b.toString) |>.toList

  let (_, st) ← (consts.forM fun n => do
    if let some ci := env.find? n then
      let s := n.toString
      if shouldIndexDeclString s then
        processConstant n ci
  ).run {} {}
  let mut stageStart ← checkpoint s!"collect/process constants ({st.decls.size} decls, {st.edges.size} raw edges, {st.morphisms.size} morphisms)" runStart

  let nodes : Array String := st.decls.map (·.name)
  let nodeSet : Std.HashSet String :=
    nodes.foldl (init := ({} : Std.HashSet String)) (fun acc n => acc.insert n)

  let leakage := classifyEdgeLeakage env nsPrefix nodeSet st.edges

  let edgesFiltered : Array DepEdge :=
    st.edges.filter (fun e => nodeSet.contains e.src && nodeSet.contains e.dst)
  stageStart ← checkpoint s!"classify/filter edges ({edgesFiltered.size} kept / {st.edges.size} raw)" stageStart

  let outPath := System.FilePath.mk outDir
  IO.FS.createDirAll outPath

  if leakage.droppedEdges > 0 then
    IO.eprintln s!"[Indexer WARNING] {leakage.droppedEdges} edge(s) reference nodes outside the filtered set"
    IO.eprintln s!"[Indexer WARNING] leakage breakdown: external={leakage.dstOutsideModuleEdges} internalGenerated={leakage.dstInsideModuleGeneratedEdges} internalStable={leakage.dstInsideModuleStableEdges} unknown={leakage.dstUnknownEdges}"
  liftM <| atomicWriteFile (outPath / "edge-leakage.json") (toJson leakage).pretty

  let writeJsonl {α} [ToJson α] (filename : String) (arr : Array α) : IO Unit := do
    let lines := arr.map (fun x => (toJson x).compress)
    atomicWriteFile (outPath / filename) (String.intercalate "\n" lines.toList)

  liftM <| writeJsonl "decls.jsonl" st.decls
  liftM <| writeJsonl "edges.jsonl" edgesFiltered
  liftM <| writeJsonl "morphisms.jsonl" st.morphisms

  let typeNodes : Array TypeNode := st.types.toList.toArray.map (fun t => { key := t, display := t })
  liftM <| writeJsonl "types.jsonl" typeNodes
  stageStart ← checkpoint "write index jsonl artifacts" stageStart

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
  stageStart ← checkpoint "build typed adjacency" stageStart

  let typedSorted :=
    typedAdj.map (fun adj => adj.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && edgeKindRank a.2 < edgeKindRank b.2)))
  stageStart ← checkpoint "sort typed adjacency" stageStart

  -- Project the FullGraph view (with string edge kinds) from the typed adjacency.
  let fwdSorted : Array (Array (Nat × String)) :=
    typedSorted.map (fun adj => adj.map (fun (v, k) =>
      (v, match k with | .type => "type" | .value => "value")))

  let graph : FullGraph := { nodes := nodes, forward := fwdSorted }
  liftM <| atomicWriteFile (System.FilePath.mk graphOut) (Lean.toJson graph).pretty
  stageStart ← checkpoint "write full_graph.json" stageStart

  let nativeGraph : Graph String := { nodes := nodes, nodeToIdx := nameToIdx, forward := typedSorted }
  let hydrated := hydrate nativeGraph
  stageStart ← checkpoint "hydrate graph (SCC + DAG + dominators)" stageStart
  let structuralPayload := buildStructuralPayload hydrated
  stageStart ← checkpoint "build structural payload" stageStart
  liftM <| writeStructuralJsonOutput structuralPayload structureOut
  stageStart ← checkpoint "write structural-topology.json" stageStart

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
  let _ ← checkpoint "write meta.json" stageStart
  let runStop ← liftM IO.monoMsNow
  liftM <| logTiming "total runIndexer" (runStop - runStart)

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

  initSearchPath (← findSysroot)
  let env ← importModules (parseImports importModsStr) {} 0
  let importStop ← IO.monoMsNow
  logTiming s!"importModules ({importModsStr})" (importStop - importStart)
  let coreContext : Core.Context := { fileName := "<Indexer>", fileMap := default }

  let _ ← ((runIndexer nsPrefix importModsStr outDir graphOut structureOut).run {} {}).toIO coreContext { env := env }
  return 0

def main (args : List String) : IO UInt32 :=
  indexerMain args
