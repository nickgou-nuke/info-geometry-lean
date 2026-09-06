import Lean
import Lean.Data.Json
import InfoGeometry.Analysis

open Lean
open InfoGeometry.Analysis

/-- JSON representation matching DAG.Graph. -/
structure ForwardGraphJson where
  nodes   : Array String
  forward : Array (Array (Nat × String))

instance : ToJson ForwardGraphJson where
  toJson g :=
    Json.mkObj
      [ ("nodes", toJson g.nodes)
      , ("forward", toJson g.forward)
      ]

def indexedToForwardJson (g : IndexedGraph) : ForwardGraphJson :=
  let nodes := g.nodes.map toString
  let forward := g.forward.map (fun row =>
    row.map (fun (j, k) =>
      let kind := match k with
        | .type  => "type"
        | .value => "value"
      (j, kind)
    )
  )
  { nodes := nodes, forward := forward }

def parseImports (s : String) : Array Import :=
  let pieces : List String :=
    (String.splitOn s ",").filter (fun x => x != "")
  let vals : List Import :=
    pieces.map fun m =>
      { module := (String.splitOn m ".").foldl (init := Name.anonymous) fun acc part =>
          if part.isEmpty then acc else Name.str acc part }
  vals.toArray

def main (args : List String) : IO UInt32 := do
  match args with
  | [importModsStr, outPath, nsPrefix] =>
      let imports := parseImports importModsStr
      let env ← importModules imports {} 0
      let ig : IndexedGraph := envToIndexedGraph env (some nsPrefix)
      let fg := indexedToForwardJson ig
      let json := ToJson.toJson fg
      let path := System.FilePath.mk outPath
      match path.parent with
      | some p => IO.FS.createDirAll p
      | none   => pure ()
      IO.FS.writeFile path json.pretty
      IO.println s!"[ExportForwardGraph] wrote {outPath} (nodes={ig.nodes.size})"
      return 0
  | _ =>
      IO.eprintln "usage: ExportForwardGraph <import-module[,module2,…]> <output.json> <ns-prefix>"
      return 1
