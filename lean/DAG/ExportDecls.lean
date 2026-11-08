import Lean
import Lean.Data.Json
import DAG.Basic
import DAG.Util

open DAG

open Lean

/-!
`ExportDecls.lean`

Compatibility declaration-inventory exporter.

This file still exports a filtered JSON inventory of "real" declarations (theorems/defs/axioms/opaque/inductives)
from a loaded Lean environment, with optional dependency filtering by namespace.

Usage:
  lake env lean --run lean/DAG/ExportDecls.lean
    <import-module> <namespace-prefix> <output.json> [deps-prefix]

Examples:
  -- Export declarations in namespace `InfoGeometry`, keep all deps
  lake env lean --run lean/DAG/ExportDecls.lean
    InfoGeometry InfoGeometry docs-map/declarations.json

  -- Export declarations in namespace `InfoGeometry`, keep only `InfoGeometry.*` deps
  lake env lean --run lean/DAG/ExportDecls.lean
    InfoGeometry InfoGeometry docs-map/declarations.json InfoGeometry

  -- Inspection mode (no namespace filter): use "*" (or "")
  lake env lean --run lean/DAG/ExportDecls.lean
    InfoGeometry "*" docs-map/declarations.debug.json
-/

structure DeclRow where
  name : String
  kind : String
  mod  : String
  deps : List String
  doc  : String
  type : String
deriving Repr

instance : ToJson DeclRow where
  toJson r :=
    Json.mkObj
      [ ("name",   toJson r.name)
      , ("kind",   toJson r.kind)
      , ("module", toJson r.mod)
      , ("deps",   toJson r.deps)
      , ("doc",    toJson r.doc)
      , ("type",   toJson r.type)
      ]

def dottedName (s : String) : Name :=
  (s.splitOn ".").foldl (init := Name.anonymous) fun acc part =>
    if part.isEmpty then acc else Name.str acc part

def parseNamespaceFilters (s : String) : Option (List String) :=
  let parts :=
    (s.splitOn ",").map (fun part => part.trimAscii.toString) |>.filter (fun x => x != "" && x != "*")
  if parts.isEmpty then none else some parts

def normalizePrefix? (s : String) : Option String :=
  if s = "" || s = "*" then none else some s

def inNamespaceFilters (nsFilters : Option (List String)) (n : Name) : Bool :=
  match nsFilters with
  | none =>
      true
  | some filters =>
      let s := toString n
      filters.any (fun p => s = p || s.startsWith (p ++ "."))

def kindString? : ConstantInfo → Option String
  | .thmInfo _    => some "theorem"
  | .axiomInfo _  => some "axiom"
  | .defnInfo _   => some "def"
  | .opaqueInfo _ => some "opaque"
  | .inductInfo _ => some "inductive"
  | .quotInfo _   => none      -- skip generated quotient declarations
  | .ctorInfo _   => none      -- skip constructors
  | .recInfo _    => none      -- skip recursors

def moduleNameFor (env : Environment) (declName : Name) : String :=
  match env.getModuleIdxFor? declName with
  | some midx =>
      let mods : List Name := env.header.moduleNames.toList
      let idx : Nat := midx.toNat
      if h : idx < mods.length then
        let m := mods.get ⟨idx, h⟩
        toString m
      else
        "<unknown>"
  | none =>
      toString env.mainModule



def dedupNames (xs : List Name) : List Name :=
  (xs.foldl (fun acc n => if acc.contains n then acc else n :: acc) []).reverse

def sortStrings (xs : List String) : List String :=
  (xs.toArray.qsort (fun a b => a < b)).toList

def keepDep (depsPrefix? : Option String) (selfName : Name) (dep : Name) : Bool :=
  dep != selfName &&
  !isGeneratedOrUnstableName dep &&
  match depsPrefix? with
  | some p =>
      let s := toString dep
      s = p || s.startsWith (p ++ ".")
  | none   =>
      true

def getDeps (ci : ConstantInfo) (depsPrefix? : Option String := none) : List String :=
  let fromType := collectDeps ci.type
  let fromValue :=
    match ci.value? with
    | some v => collectDeps v
    | none   => []
  let raw := dedupNames (fromType ++ fromValue)
  let filtered := raw.filter (fun n => keepDep depsPrefix? ci.name n)
  let cleaned := filtered.map toString
  sortStrings cleaned

def shouldInclude (nsFilters : Option (List String)) (declName : Name) (ci : ConstantInfo) : Bool :=
  inNamespaceFilters nsFilters declName &&
  !isGeneratedOrUnstableName declName &&
  (kindString? ci).isSome

def getDocString (env : Environment) (n : Name) : IO String := do
  match ← Lean.findDocString? env n with
  | some doc => return doc
  | none => return ""

def collectDecls
    (env : Environment)
    (nsPrefix : String)
    (depsPrefix? : Option String := none) : IO (Array DeclRow) := do
  let nsFilters := parseNamespaceFilters nsPrefix
  let mut rows : Array DeclRow := #[]
  for (declName, ci) in env.constants.toList do
    if shouldInclude nsFilters declName ci then
      match kindString? ci with
      | some k =>
          let doc ← getDocString env declName
          -- Note: simple `toString` for now; can be enhanced with `MetaM` later.
          let typeStr := toString ci.type
          let deps := getDeps ci depsPrefix?
          rows := rows.push
            { name := toString declName
            , kind := k
            , mod  := moduleNameFor env declName
            , deps := deps
            , doc  := doc
            , type := typeStr
            }
      | none =>
          pure ()
  return rows.qsort (fun a b => a.name < b.name)

def writeOutput
    (rows : Array DeclRow)
    (outPath importMod nsPrefix : String)
    (depsPrefix? : Option String := none) : IO Unit := do
  let path := System.FilePath.mk outPath
  match path.parent with
  | some p => IO.FS.createDirAll p
  | none   => pure ()

  let depsPrefixStr :=
    match depsPrefix? with
    | some s => s
    | none   => ""

  let payload :=
    Json.mkObj
      [ ("importModule", toJson importMod)
      , ("namespace",    toJson nsPrefix)
      , ("depsPrefix",   toJson depsPrefixStr)
      , ("count",        toJson rows.size)
      , ("declarations", toJson rows)
      ]

  IO.FS.writeFile path payload.pretty

def firstSegment (s : String) : String :=
  match s.splitOn "." with
  | x :: _ => x
  | [] => s

def sampleNames (env : Environment) (probePrefix : String) (limit : Nat := 40) : List String :=
  let allNames : List String := env.constants.toList.map (fun (n, _) => toString n)
  let filtered :=
    if probePrefix = "" then
      allNames
    else
      allNames.filter (fun s => s.startsWith probePrefix)
  filtered.take limit

def runExport
    (importModsStr nsPrefix outPath : String)
    (depsPrefix? : Option String) : IO UInt32 := do
  -- allow comma-separated list of modules
  let importMods := importModsStr.splitOn "," |>.map (fun s => dottedName s)
  -- build an Array Import
  let imports : Array Import := importMods.foldl (init := #[]) fun acc m =>
        acc.push { module := m }
  let env ← importModules imports {} 0

  let totalConsts := env.constants.toList.length
  IO.println s!"[ExportDecls] env.constants={totalConsts}"

  let rows ← collectDecls env nsPrefix depsPrefix?
  writeOutput rows outPath importModsStr nsPrefix depsPrefix?

  let depsMsg :=
    match depsPrefix? with
    | some p => p
    | none   => "ALL"

  IO.println <|
    s!"[ExportDecls] modules={importModsStr} namespace={nsPrefix} deps={depsMsg} " ++
      s!"count={rows.size}"
  IO.println s!"[ExportDecls] wrote {outPath}"

  if rows.size = 0 then
    let probe := firstSegment importModsStr
    let samples := sampleNames env probe 40
    IO.println s!"[ExportDecls] WARNING: exported 0 declarations."
    IO.println s!"[ExportDecls] Sample names in env (prefix '{probe}'): {samples}"
    IO.println s!"[ExportDecls] Hint: module name and declaration namespace may differ."
    IO.println <|
      s!"[ExportDecls] Try namespace='*' (inspection mode) or the actual namespace " ++
        s!"from the sample."
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [importModsStr, nsPrefix, outPath] =>
      runExport importModsStr nsPrefix outPath none

  | [importModsStr, nsPrefix, outPath, depsPrefix] =>
      runExport importModsStr nsPrefix outPath (normalizePrefix? depsPrefix)

  | _ =>
      IO.eprintln <|
        "usage: ExportDecls <import-module[,module2,...]> <namespace-prefix[,namespace-prefix2,...]> <output.json> " ++
          "[deps-prefix]"
      IO.eprintln "examples:"
      IO.eprintln <|
        "  lake env lean --run lean/DAG/ExportDecls.lean " ++
          "InfoGeometry.Core,InfoGeometry.Convex InfoGeometry docs-map/declarations.json"
      IO.eprintln <|
        "  lake env lean --run lean/DAG/ExportDecls.lean " ++
          "Mathlib,InfoGeometry.All Mathlib,InfoGeometry docs-map/declarations.json Mathlib"
      IO.eprintln <|
        "  lake env lean --run lean/DAG/ExportDecls.lean " ++
          "InfoGeometry.Core \"*\" docs-map/declarations.debug.json"
      return 1
