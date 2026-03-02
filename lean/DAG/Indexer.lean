-- scripts/Indexer.lean
-- patched: (1) robust MetaM/IO handling
--          (2) fixed property projections and mappings
--          (3) standardized full_graph.json output

import Lean
import Lean.Data.Json
import Lean.DeclarationRange
import Lean.Util.Path
import DAG.Basic

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

structure IndexerState where
  decls     : Array DeclNode := #[]
  edges     : Array DepEdge  := #[]
  edgeSet   : Std.HashSet EdgeKey := {}
  morphisms : Array Morphism := #[]
  types     : Std.HashSet String := {}

abbrev IndexerM := StateRefT IndexerState MetaM

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

def runIndexer (nsPrefix : String) (outDir : String) (graphOut : String) : MetaM Unit := do
  let env ← getEnv
  let mut consts := env.constants.toList.map (·.1)
  consts := consts.filter (fun n => (n.toString).startsWith nsPrefix)
  consts := consts.toArray.qsort (fun a b => a.toString < b.toString) |>.toList

  let (_, st) ← (consts.forM fun n => do
    if let some ci := env.find? n then
      let s := n.toString
      if !(s.contains "._" || s.endsWith "match_" || s.endsWith "proof_" || s.endsWith "injEq") then
        processConstant n ci
  ).run {}

  let nodes : Array String := st.decls.map (·.name)
  let nodeSet : Std.HashSet String :=
    nodes.foldl (init := ({} : Std.HashSet String)) (fun acc n => acc.insert n)

  let edgesFiltered : Array DepEdge :=
    st.edges.filter (fun e => nodeSet.contains e.src && nodeSet.contains e.dst)

  let outPath := System.FilePath.mk outDir
  IO.FS.createDirAll outPath

  let writeJsonl {α} [ToJson α] (filename : String) (arr : Array α) : IO Unit := do
    let lines := arr.map (fun x => (toJson x).compress)
    IO.FS.writeFile (outPath / filename) (String.intercalate "\n" lines.toList)

  liftM <| writeJsonl "decls.jsonl" st.decls
  liftM <| writeJsonl "edges.jsonl" edgesFiltered
  liftM <| writeJsonl "morphisms.jsonl" st.morphisms

  let typeNodes : Array TypeNode := st.types.toList.toArray.map (fun t => { key := t, display := t })
  liftM <| writeJsonl "types.jsonl" typeNodes

  let nameToIdx : Std.HashMap String Nat :=
    Id.run <| do
      let mut m : Std.HashMap String Nat := {}
      for i in [:nodes.size] do
        m := m.insert nodes[i]! i
      return m

  let mut fwd_adj : Array (Array (Nat × String)) :=
    Id.run <| do
      let mut a := #[]
      for _ in [:nodes.size] do
        a := a.push #[]
      return a

  for e in edgesFiltered do
    match nameToIdx.get? e.src, nameToIdx.get? e.dst with
    | some u, some v => fwd_adj := fwd_adj.modify u (fun adj => adj.push (v, e.kind))
    | _, _ => pure ()

  let fwd_sorted := fwd_adj.map (fun adj => adj.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)))
  let graph : FullGraph := { nodes := nodes, forward := fwd_sorted }
  IO.FS.writeFile (System.FilePath.mk graphOut) (Lean.toJson graph).pretty

  IO.println s!"[Indexer patched] Exported {st.decls.size} atoms to {outDir}/ and wrote {graphOut}"

def main (args : List String) : IO UInt32 := do
  let (importMod, nsPrefix, outDir, graphOut) ←
    match args with
    | [m, ns, o]      => pure (m, ns, o, "full_graph.json")
    | [m, ns, o, go]  => pure (m, ns, o, go)
    | _               => pure ("InfoGeometry.Library", "InfoGeometry", "index", "full_graph.json")

  let env ← importModules #[{ module := importMod.toName }] {} 0
  let coreContext : Core.Context := { fileName := "<Indexer>", fileMap := default }

  let _ ← ((runIndexer nsPrefix outDir graphOut).run {} {}).toIO coreContext { env := env }
  return 0
