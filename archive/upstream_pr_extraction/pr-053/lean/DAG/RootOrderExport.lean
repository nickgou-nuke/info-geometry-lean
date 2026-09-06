import Lean
import Lean.Data.Json
import DAG.Basic
import DAG.Hydrate
import DAG.Analysis
import DAG.Util

open Lean
open DAG

structure RootContributionRow where
  name  : String
  paths : Nat
deriving Repr, ToJson

structure LayerRow where
  depth : Nat
  size  : Nat
  nodes : Array String
deriving Repr, ToJson

structure ChainRow where
  depth : Nat
  nodes : Array String
deriving Repr, ToJson

structure CapstoneRow where
  name        : String
  depthMin    : Nat
  depthMax    : Nat
  depthSpread : Nat
  rootCount   : Nat
  roots       : Array RootContributionRow
deriving Repr, ToJson

structure RootOrderPayload where
  orientation   : String
  rootCount     : Nat
  capstoneCount : Nat
  layerCount    : Nat
  maxDepth      : Nat
  roots         : Array String
  layers        : Array LayerRow
  deepestChains : Array ChainRow
  capstones     : Array CapstoneRow
deriving Repr, ToJson

private def representativeName (h : HydratedGraph Lean.Name) (si : Nat) : Lean.Name :=
  Id.run do
    let comp := h.sccs[si]!
    for vi in [:comp.size] do
      let v := comp[vi]!
      let n := h.toGraph.nodes[v]!
      if !isGeneratedOrUnstableName n then
        return n
    if comp.isEmpty then
      return Name.anonymous
    return h.toGraph.nodes[comp[0]!]!

private def representativeString (h : HydratedGraph Lean.Name) (si : Nat) : String :=
  (representativeName h si).toString

private def renderRootContribs (rows : Array RootContributionRow) : String :=
  if rows.isEmpty then
    "-"
  else
    String.intercalate ", " <| rows.toList.map (fun r => s!"{r.name} ({r.paths})")

private def buildPayload (h : HydratedGraph Lean.Name) : RootOrderPayload :=
  Id.run do
    let roots := rootSet h
    let caps := capstoneSet h
    let dMin := depthMinFromRoots h
    let dMax := depthMaxFromRoots h
    let dSpread := depthSpreadFromRoots h
    let layersRaw := topologicalLayersFromRoots h
    let deepestRaw := deepestRootChains h

    let rootsOut := roots.map (representativeString h ·)

    let layers : Array LayerRow :=
      layersRaw.mapIdx fun depth comps =>
        { depth := depth
        , size := comps.size
        , nodes := comps.map (representativeString h ·)
        }

    let mut maxDepth := 0
    for i in [:dMax.size] do
      match dMax[i]! with
      | none => pure ()
      | some d =>
          if d > maxDepth then
            maxDepth := d

    let deepestChains : Array ChainRow :=
      deepestRaw.map fun comps =>
        { depth := if comps.size == 0 then 0 else comps.size - 1
        , nodes := comps.map (representativeString h ·)
        }

    let capstones : Array CapstoneRow :=
      caps.map fun si =>
        let contributions := rootContributionCounts h si
        let rootsForCap : Array RootContributionRow :=
          contributions.map fun (ri, paths) =>
            { name := representativeString h ri, paths := paths }
        let minD := match dMin[si]! with | some d => d | none => 0
        let maxD := match dMax[si]! with | some d => d | none => 0
        let spread := match dSpread[si]! with | some d => d | none => 0
        { name := representativeString h si
        , depthMin := minD
        , depthMax := maxD
        , depthSpread := spread
        , rootCount := rootsForCap.size
        , roots := rootsForCap
        }

    { orientation := "Edges are declaration -> dependency on the condensed SCC DAG. True roots are SCCs with empty dependency out-neighborhoods (`dag = #[]`)."
      , rootCount := roots.size
      , capstoneCount := caps.size
      , layerCount := layers.size
      , maxDepth := maxDepth
      , roots := rootsOut
      , layers := layers
      , deepestChains := deepestChains
      , capstones := capstones.qsort (fun a b =>
          if a.depthMax == b.depthMax then a.name < b.name else a.depthMax > b.depthMax)
      }

private def writeJsonOutput (payload : RootOrderPayload) (outPath : String) : IO Unit := do
  let path := System.FilePath.mk outPath
  if let some p := path.parent then
    IO.FS.createDirAll p
  IO.FS.writeFile path (toJson payload).pretty

private def writeMarkdownOutput (payload : RootOrderPayload) (outPath : String) : IO Unit := do
  let path := System.FilePath.mk outPath
  if let some p := path.parent then
    IO.FS.createDirAll p

  let mut lines : Array String := #[]
  lines := lines.push "# True Root Order"
  lines := lines.push ""
  lines := lines.push payload.orientation
  lines := lines.push ""
  lines := lines.push "## Summary"
  lines := lines.push ""
  lines := lines.push s!"- roots: `{payload.rootCount}`"
  lines := lines.push s!"- capstones: `{payload.capstoneCount}`"
  lines := lines.push s!"- layers: `{payload.layerCount}`"
  lines := lines.push s!"- max depth from roots: `{payload.maxDepth}`"
  lines := lines.push ""
  lines := lines.push "## Root Set"
  lines := lines.push ""
  for r in payload.roots do
    lines := lines.push s!"- `{r}`"
  lines := lines.push ""
  lines := lines.push "## Topological Layers"
  lines := lines.push ""
  lines := lines.push "| Depth | Size | Representative nodes |"
  lines := lines.push "| --- | --- | --- |"
  for layer in payload.layers do
    let names := String.intercalate ", " <| layer.nodes.toList.map (fun n => s!"`{n}`")
    lines := lines.push s!"| `{layer.depth}` | `{layer.size}` | {names} |"
  lines := lines.push ""
  lines := lines.push "## Deepest Root Chains"
  lines := lines.push ""
  for chain in payload.deepestChains do
    let chainStr := String.intercalate " -> " <| chain.nodes.toList.map (fun n => s!"`{n}`")
    lines := lines.push s!"- depth `{chain.depth}`: {chainStr}"
  lines := lines.push ""
  lines := lines.push "## Per-Capstone Root Ancestry"
  lines := lines.push ""
  lines := lines.push "| Capstone | depth_min | depth_max | spread | roots | ancestry |"
  lines := lines.push "| --- | --- | --- | --- | --- | --- |"
  for row in payload.capstones do
    lines := lines.push s!"| `{row.name}` | `{row.depthMin}` | `{row.depthMax}` | `{row.depthSpread}` | `{row.rootCount}` | {renderRootContribs row.roots} |"

  IO.FS.writeFile path (String.intercalate "\n" lines.toList)

def main (args : List String) : IO UInt32 := do
  match args with
  | [importModStr, nsPrefix, mdOut] =>
      initSearchPath (← findSysroot)
      let env ← importModules #[{ module := importModStr.toName }] {}
      IO.println s!"[RootOrderExport] Building graph for {importModStr} (prefix: {nsPrefix})..."
      let g := buildGraphFromEnv env (some nsPrefix)
      let h := hydrate g
      IO.println "[RootOrderExport] Computing rooted partial-order geometry..."
      let payload := buildPayload h
      writeMarkdownOutput payload mdOut
      IO.println s!"[RootOrderExport] Wrote root-order report to {mdOut}"
      return 0
  | [importModStr, nsPrefix, mdOut, jsonOut] =>
      initSearchPath (← findSysroot)
      let env ← importModules #[{ module := importModStr.toName }] {}
      IO.println s!"[RootOrderExport] Building graph for {importModStr} (prefix: {nsPrefix})..."
      let g := buildGraphFromEnv env (some nsPrefix)
      let h := hydrate g
      IO.println "[RootOrderExport] Computing rooted partial-order geometry..."
      let payload := buildPayload h
      writeMarkdownOutput payload mdOut
      writeJsonOutput payload jsonOut
      IO.println s!"[RootOrderExport] Wrote root-order report to {mdOut} and {jsonOut}"
      return 0
  | _ =>
      IO.eprintln "usage: root_order_export <import-module> <namespace-prefix> <output.md> [output.json]"
      IO.eprintln "example: lake env lean --run lean/DAG/RootOrderExport.lean InfoGeometry InfoGeometry reports/dag/true-root-order.md reports/dag/true-root-order.json"
      return 1
