import Lean
import Lean.Data.Json
import DAG.Basic
import DAG.Hydrate
import DAG.Analysis

open Lean
open DAG

structure SkeletonRow where
  name       : String
  vulSrcs    : Nat
  vulPaths   : Nat
deriving Repr, ToJson

def writeOutput (rows : Array SkeletonRow) (outPath : String) : IO Unit := do
  let path := System.FilePath.mk outPath
  if let some p := path.parent then
    IO.FS.createDirAll p

  let payload :=
    Json.mkObj
      [ ("count", toJson rows.size)
      , ("skeleton", toJson rows)
      ]
  IO.FS.writeFile path payload.pretty

def main (args : List String) : IO UInt32 := do
  match args with
  | [importModStr, nsPrefix, outPath] =>
      initSearchPath (← findSysroot)
      let env ← importModules #[{ module := importModStr.toName }] {}

      IO.println s!"[SkeletonExport] Building graph for {importModStr} (prefix: {nsPrefix})..."
      let g := buildGraphFromEnv env (some nsPrefix)
      let h := hydrate g

      IO.println s!"[SkeletonExport] Extracting True Skeleton..."
      let skelRaw := extractTheorySkeleton h 1

      let rows : Array SkeletonRow := skelRaw.map fun (n, vp, vs) =>
        { name := n.toString, vulPaths := vp, vulSrcs := vs }

      writeOutput rows outPath
      IO.println s!"[SkeletonExport] Wrote {rows.size} skeleton nodes to {outPath}"
      return 0
  | _ =>
      IO.eprintln "usage: skeleton_export <import-module> <namespace-prefix> <output.json>"
      IO.eprintln "example: lake env lean --run lean/DAG/SkeletonExport.lean InfoGeometry InfoGeometry skeleton.json"
      return 1
