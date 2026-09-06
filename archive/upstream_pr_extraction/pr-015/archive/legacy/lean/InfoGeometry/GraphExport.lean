import Lean
import Lean.Data.Json
import DAG.Basic
import DAG.JsonInstances

open Lean
open DAG

namespace InfoGeometry

/-!
`ExportGraph.lean`

Legacy compatibility exporter for older Python/JSON graph consumers.

Dump the dependency graph produced by `DAG.buildGraphFromEnv` as
JSON.  The graph format is intentionally minimal, suitable for post‑processing
in Python or other tools.

For the current public declaration DAG lane, use `tools/refresh_decl_graph.py`
which wraps `lean/DAG/Indexer.lean` and writes to `artifacts/dag/`.

Usage:

```sh
lake env lean --run archive/legacy/lean/InfoGeometry/GraphExport.lean <import-modules> <output.json> [ns-prefix]
```

`<import-modules>` is a comma-separated list of modules to load before
inspecting the environment.  If the list is empty (`""`) the current package
is used implicitly.

Example:

```sh
lake env lean --run archive/legacy/lean/InfoGeometry/GraphExport.lean InfoGeometry InfoGeometry/graph.json
```
-/

/-- JSON representation of the graph used by the Python tooling.
    The `edges` list now includes an optional kind string ("type" or "value").
    Existing consumers that only expect pairs may still function if they ignore
    the third field.
-/
structure GraphJson where
  nodes : List String
  edges : List (String × String × String) -- from, to, kind

instance : ToJson GraphJson where
  toJson g :=
    Json.mkObj
      [ ("nodes", toJson g.nodes)
      , ("edges", toJson g.edges)
      ]

/-- Convert an indexed graph (with kinds) to JSON. -/
def indexedGraphToJson (g : Graph Name) : GraphJson :=
  -- copy the arrays we need so that later loops don't refer to `g` directly
  let nodesArr := g.nodes
  let forwardArr := g.forward
  let nodesList : List String :=
    (nodesArr.toList).map toString
  let edges : List (String × String × String) :=
    Id.run do
      let mut out : List (String × String × String) := []
      let n := forwardArr.size
      for i in [:n] do
        let row := forwardArr[i]!
        let srcName := (nodesArr[i]!).toString
        for (j, k) in row do
          let dstName := (nodesArr[j]!).toString
          let kind :=
            match k with
            | .type  => "type"
            | .value => "value"
          out := (srcName, dstName, kind) :: out
      out.reverse
  { nodes := nodesList, edges := edges }

/-- Parse comma-separated module list. -/
def parseImports (s : String) : Array Import :=
  let pieces : List String :=
    (String.splitOn s ",").filter (fun x => x != "")
  let vals : List Import :=
    pieces.map fun m =>
      { module := (String.splitOn m ".").foldl (init := Name.anonymous) fun acc part =>
          if part.isEmpty then acc else Name.str acc part }
  vals.toArray

end InfoGeometry

open InfoGeometry

-- Execute as a script; this `main` must live at the toplevel so that
-- `lake env lean --run` can find it.
def main (args : List String) : IO UInt32 := do
  match args with
  | [importModsStr, outPath] =>
      let imports := parseImports importModsStr
      let env ← importModules imports {} 0
      let ig : Graph Name := buildGraphFromEnv env none
      let graphJson := indexedGraphToJson ig
      let json := ToJson.toJson graphJson
      let path := System.FilePath.mk outPath
      match path.parent with
      | some p => IO.FS.createDirAll p
      | none   => pure ()
      IO.FS.writeFile path json.pretty
      let nodeCount := ig.nodes.size
      let edgeCount := ig.forward.foldl (init := 0) fun acc arr => acc + arr.size
      IO.println s!"[ExportGraph] wrote {outPath} (nodes={nodeCount}, edges={edgeCount})"
      return 0
  | [importModsStr, outPath, nsPrefix] =>
      let imports := parseImports importModsStr
      let env ← importModules imports {} 0
      let ig : Graph Name := buildGraphFromEnv env (some nsPrefix)
      let graphJson := indexedGraphToJson ig
      let json := ToJson.toJson graphJson
      let path := System.FilePath.mk outPath
      match path.parent with
      | some p => IO.FS.createDirAll p
      | none   => pure ()
      IO.FS.writeFile path json.pretty
      let nodeCount := ig.nodes.size
      let edgeCount := ig.forward.foldl (init := 0) fun acc arr => acc + arr.size
      IO.println s!"[ExportGraph] wrote {outPath} (nodes={nodeCount}, edges={edgeCount})"
      return 0
  | _ =>
      IO.eprintln "usage: ExportGraph <import-module[,module2,…]> <output.json> [ns-prefix]"
      return 1
