import Lean
import Lean.Data.Json
import DAG.Basic
import DAG.Hydrate
import DAG.Analysis
import DAG.Util

open Lean
open DAG

------------------------------------------------------------------------
-- Disconnected Capstone Audit
--
-- Pure Lean program. No Python. No ArangoDB.
--
-- Loads the full InfoGeometry environment, builds the declaration graph,
-- computes SCCs via Tarjan, then identifies capstone SCCs that have no
-- path from any root SCC in the condensed DAG.
--
-- For each disconnected capstone, classifies the reason:
--   1. axiom_contaminated : representative is axiom/opaque, or declares
--      non-mathlib axioms
--   2. disconnected_island: the SCC and its dependencies form a closed
--      island with no Mathlib-rooted imports
--   3. sorry_incomplete   : proof uses sorry (debt, not fake root)
--
-- Outputs JSON + Markdown reports.
------------------------------------------------------------------------

structure DisconnectedCapstone where
  repName        : String
  sccIdx         : Nat
  sccSize        : Nat
  declCount      : Nat
  category       : String  -- "axiom_contaminated" | "disconnected_island" | "sorry_incomplete" | "unknown"
  axioms         : Array String
  isSorry        : Bool
  isAxiom        : Bool
  isOpaque       : Bool
  importsMathlib : Bool
  moduleImports  : Array String
  depthFromRoot  : Option Nat
deriving Repr

structure AuditSummary where
  totalSccs          : Nat
  rootCount          : Nat
  capstoneCount      : Nat
  connectedCount     : Nat
  disconnectedCount  : Nat
  axiomContaminated  : Nat
  disconnectedIsland : Nat
  sorryIncomplete    : Nat
  unknown            : Nat
  maxDepth           : Nat
deriving Repr

structure AuditPayload where
  summary      : AuditSummary
  disconnected : Array DisconnectedCapstone
  roots        : Array String
deriving Repr

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

/-- Check if a name belongs to Mathlib/Init/Std/Batteries. -/
def isMathlibName (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some midx =>
      let mods := env.header.moduleNames
      let m := mods[midx.toNat]!
      let ms := toString m
      ms.startsWith "Mathlib" || ms.startsWith "Init" ||
      ms.startsWith "Std" || ms.startsWith "Batteries"
  | none => false

/-- Check if a name belongs to the current library (InfoGeometry). -/
def isLocalName (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some midx =>
      let mods := env.header.moduleNames
      let m := mods[midx.toNat]!
      (toString m).startsWith "InfoGeometry"
  | none => false

/-- Check if a declaration is an axiom or opaque. -/
def isAxiomOrOpaque (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.axiomInfo _)  => true
  | some (.opaqueInfo _) => true
  | _                    => false

/-- Check if a declaration's proof uses sorry. -/
def usesSorry (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some ci =>
      let refs := collectDeps ci.type
      let valRefs := match ci.value? with
        | some v => collectDeps v
        | none => []
      let all := refs ++ valRefs
      all.any (fun r => r.toString == "sorryAx" || r.toString == "sorry")
  | none => false

/-- Collect axiom/sorry names from a declaration. -/
def collectAxiomNames (env : Environment) (n : Name) : Array String := Id.run do
  match env.find? n with
  | some ci =>
      let mut axioms := #[]
      match ci with
      | .axiomInfo _   => axioms := axioms.push s!"axiom:{n.toString}"
      | .opaqueInfo _  => axioms := axioms.push s!"opaque:{n.toString}"
      | _              => pure ()
      let allRefs := collectDeps ci.type ++ (match ci.value? with | some v => collectDeps v | none => [])
      for r in allRefs do
        if r.toString == "sorryAx" then
          axioms := axioms.push s!"sorry:{n.toString}"
      axioms
  | none => #[]

/-- Check if an SCC imports any Mathlib-rooted declaration. -/
def sccImportsMathlib (env : Environment) (h : HydratedGraph Name) (si : Nat) : Bool := Id.run do
  let comp := h.sccs[si]!
  for vi in [:comp.size] do
    let v := comp[vi]!
    let n := h.toGraph.nodes[v]!
    match env.find? n with
    | some ci =>
        let edges := edgesFromConstantInfo ci
        for (dep, _) in edges do
          if isMathlibName env dep then
            return true
    | none => pure ()
  false

/-- Get the InfoGeometry module imports for an SCC. -/
def sccModuleImports (env : Environment) (h : HydratedGraph Name) (si : Nat) : Array String := Id.run do
  let comp := h.sccs[si]!
  let mut mods : Std.HashSet String := {}
  for vi in [:comp.size] do
    let v := comp[vi]!
    let n := h.toGraph.nodes[v]!
    match env.find? n with
    | some ci =>
        let edges := edgesFromConstantInfo ci
        for (dep, _) in edges do
          if isLocalName env dep then
            let s := toString dep
            match s.splitOn "." with
            | [] => pure ()
            | m :: _ => mods := mods.insert m
    | none => pure ()
  mods.toList.toArray.qsort (· < ·)

------------------------------------------------------------------------
-- Main audit logic (IO because it prints progress)
------------------------------------------------------------------------

def runAudit (env : Environment) (nsPrefix : String) : IO AuditPayload := do
  IO.println s!"[DisconnectedAudit] Building graph for {nsPrefix}..."
  let g := buildGraphFromEnv env (some nsPrefix)
  IO.println s!"[DisconnectedAudit] Graph: {g.nodes.size} nodes, {g.forward.foldl (fun acc row => acc + row.size) 0} edges"

  IO.println "[DisconnectedAudit] Computing SCCs..."
  let h := hydrate g
  IO.println s!"[DisconnectedAudit] SCCs: {h.sccs.size}"

  let roots := rootSet h
  let caps := capstoneSet h
  IO.println s!"[DisconnectedAudit] Roots: {roots.size}, Capstones: {caps.size}"

  -- Compute depth from roots for all SCCs
  let depthMin := depthMinFromRoots h
  let depthMax := depthMaxFromRoots h

  let maxDepth := Id.run do
    let mut d := 0
    for i in [:depthMax.size] do
      match depthMax[i]! with
      | some v => if v > d then d := v
      | none => pure ()
    d

  -- Identify disconnected capstones (depthMin = none)
  let mut disconnected : Array DisconnectedCapstone := #[]
  let mut connectedCount := 0
  let mut axiomCount := 0
  let mut islandCount := 0
  let mut sorryCount := 0
  let mut unknownCount := 0

  IO.println "[DisconnectedAudit] Analyzing capstones..."
  for si in [:h.sccs.size] do
    -- Only process capstones (no reverse dependents)
    if h.preds[si]!.isEmpty then
      match depthMin[si]! with
      | some _ =>
          connectedCount := connectedCount + 1
      | none =>
          -- This capstone is disconnected from all roots
          let comp := h.sccs[si]!
          let repName := match componentRepresentative? h si with
            | some n => n.toString
            | none => s!"<empty_scc_{si}>"

          let repIsAx := match componentRepresentative? h si with
            | some n => isAxiomOrOpaque env n
            | none => false

          let repIsSor := match componentRepresentative? h si with
            | some n => usesSorry env n
            | none => false

          let axioms := match componentRepresentative? h si with
            | some n => collectAxiomNames env n
            | none => #[]

          let im := sccImportsMathlib env h si
          let mods := sccModuleImports env h si

          let repIsOpaque := match componentRepresentative? h si with
            | some n => match env.find? n with | some (.opaqueInfo _) => true | _ => false
            | none => false

          let category : String :=
            if repIsAx || axioms.any (fun a => a.startsWith "axiom:") then
              "axiom_contaminated"
            else if repIsSor then
              "sorry_incomplete"
            else if !im then
              "disconnected_island"
            else
              "unknown"

          if category == "axiom_contaminated" then axiomCount := axiomCount + 1
          else if category == "sorry_incomplete" then sorryCount := sorryCount + 1
          else if category == "disconnected_island" then islandCount := islandCount + 1
          else unknownCount := unknownCount + 1

          let declCount := comp.foldl (fun acc v =>
            let n := h.toGraph.nodes[v]!
            if !isGeneratedOrUnstableName n then acc + 1 else acc
          ) 0

          disconnected := disconnected.push {
            repName := repName
            sccIdx := si
            sccSize := comp.size
            declCount := declCount
            category := category
            axioms := axioms
            isSorry := repIsSor
            isAxiom := repIsAx
            isOpaque := repIsOpaque
            importsMathlib := im
            moduleImports := mods
            depthFromRoot := none
          }

  IO.println s!"[DisconnectedAudit] Disconnected: {disconnected.size} capstones"
  IO.println s!"[DisconnectedAudit]   axiom_contaminated: {axiomCount}"
  IO.println s!"[DisconnectedAudit]   disconnected_island: {islandCount}"
  IO.println s!"[DisconnectedAudit]   sorry_incomplete:   {sorryCount}"
  IO.println s!"[DisconnectedAudit]   unknown:            {unknownCount}"

  let rootNames := roots.map (fun si =>
    match componentRepresentative? h si with
    | some n => n.toString
    | none => s!"<scc_{si}>"
  )

  return {
    summary := {
      totalSccs := h.sccs.size
      rootCount := roots.size
      capstoneCount := caps.size
      connectedCount := connectedCount
      disconnectedCount := disconnected.size
      axiomContaminated := axiomCount
      disconnectedIsland := islandCount
      sorryIncomplete := sorryCount
      unknown := unknownCount
      maxDepth := maxDepth
    }
    disconnected := disconnected
    roots := rootNames
  }

------------------------------------------------------------------------
-- JSON output
------------------------------------------------------------------------

instance : ToJson DisconnectedCapstone where
  toJson d := Json.mkObj [
    ("repName", toJson d.repName),
    ("sccIdx", toJson d.sccIdx),
    ("sccSize", toJson d.sccSize),
    ("declCount", toJson d.declCount),
    ("category", toJson d.category),
    ("axioms", toJson d.axioms),
    ("isSorry", toJson d.isSorry),
    ("isAxiom", toJson d.isAxiom),
    ("isOpaque", toJson d.isOpaque),
    ("importsMathlib", toJson d.importsMathlib),
    ("moduleImports", toJson d.moduleImports),
    ("depthFromRoot", toJson d.depthFromRoot)
  ]

instance : ToJson AuditSummary where
  toJson s := Json.mkObj [
    ("totalSccs", toJson s.totalSccs),
    ("rootCount", toJson s.rootCount),
    ("capstoneCount", toJson s.capstoneCount),
    ("connectedCount", toJson s.connectedCount),
    ("disconnectedCount", toJson s.disconnectedCount),
    ("axiomContaminated", toJson s.axiomContaminated),
    ("disconnectedIsland", toJson s.disconnectedIsland),
    ("sorryIncomplete", toJson s.sorryIncomplete),
    ("unknown", toJson s.unknown),
    ("maxDepth", toJson s.maxDepth)
  ]

instance : ToJson AuditPayload where
  toJson p := Json.mkObj [
    ("summary", toJson p.summary),
    ("disconnectedCount", toJson p.disconnected.size),
    ("disconnected", toJson p.disconnected),
    ("rootCount", toJson p.roots.size),
    ("roots", toJson p.roots)
  ]

------------------------------------------------------------------------
-- Markdown output
------------------------------------------------------------------------

def writeMarkdown (payload : AuditPayload) (path : String) : IO Unit := do
  let fp := System.FilePath.mk path
  if let some p := fp.parent then
    IO.FS.createDirAll p

  let mut lines : Array String := #[]

  lines := lines.push "# Disconnected Capstone Audit (Pure Lean)"
  lines := lines.push ""
  lines := lines.push "> Authority: Lean environment graph + axiom analysis + import analysis."
  lines := lines.push "> No Python. No ArangoDB. No heuristics."
  lines := lines.push ""
  lines := lines.push "## Summary"
  lines := lines.push ""
  let s := payload.summary
  lines := lines.push "| Metric | Value |"
  lines := lines.push "| --- | --- |"
  lines := lines.push s!"| Total SCCs | {s.totalSccs} |"
  lines := lines.push s!"| Root SCCs | {s.rootCount} |"
  lines := lines.push s!"| Capstone SCCs | {s.capstoneCount} |"
  lines := lines.push s!"| Connected capstones | {s.connectedCount} |"
  lines := lines.push s!"| **Disconnected capstones** | **{s.disconnectedCount}** |"
  lines := lines.push s!"|   axiom_contaminated | {s.axiomContaminated} |"
  lines := lines.push s!"|   disconnected_island | {s.disconnectedIsland} |"
  lines := lines.push s!"|   sorry_incomplete | {s.sorryIncomplete} |"
  lines := lines.push s!"|   unknown | {s.unknown} |"
  lines := lines.push s!"| Max depth from roots | {s.maxDepth} |"
  lines := lines.push ""

  -- Axiom-contaminated section
  let axiomContam := payload.disconnected.filter (fun d => d.category == "axiom_contaminated")
  if axiomContam.size > 0 then
    lines := lines.push "## Axiom-Contaminated Capstones (FAKE ROOTS)"
    lines := lines.push ""
    lines := lines.push "These capstones contain declarations that are axioms or opaques, or that reference sorryAx."
    lines := lines.push "They create the illusion of being rooted but actually assert unproven claims."
    lines := lines.push ""
    lines := lines.push "| Capstone | SCC Size | Decls | Axiom/Opaque | Sorry | Imports Mathlib | Module Imports |"
    lines := lines.push "| --- | --- | --- | --- | --- | --- | --- |"
    for d in axiomContam do
      let axStr := if d.isAxiom then "AXIOM" else if d.isOpaque then "OPAQUE" else "axiom_ref"
      let sorryStr := if d.isSorry then "YES" else "no"
      let mlStr := if d.importsMathlib then "yes" else "**NO**"
      let mods := String.intercalate ", " d.moduleImports.toList
      lines := lines.push s!"| `{d.repName}` | {d.sccSize} | {d.declCount} | {axStr} | {sorryStr} | {mlStr} | {mods} |"
    lines := lines.push ""

    lines := lines.push "### Axiom Details"
    lines := lines.push ""
    for d in axiomContam do
      if d.axioms.size > 0 then
        lines := lines.push s!"#### `{d.repName}`"
        for ax in d.axioms do
          lines := lines.push s!"- `{ax}`"
        lines := lines.push ""

  -- Disconnected islands section
  let islands := payload.disconnected.filter (fun d => d.category == "disconnected_island")
  if islands.size > 0 then
    lines := lines.push "## Disconnected Islands (No Mathlib Imports)"
    lines := lines.push ""
    lines := lines.push "These capstones form closed groups that never import Mathlib."
    lines := lines.push "They are purely local definitions with no grounding in proven mathematics."
    lines := lines.push ""
    lines := lines.push "| Capstone | SCC Size | Decls | Sorry | Module Imports |"
    lines := lines.push "| --- | --- | --- | --- | --- |"
    for d in islands do
      let sorryStr := if d.isSorry then "YES" else "no"
      let mods := String.intercalate ", " d.moduleImports.toList
      lines := lines.push s!"| `{d.repName}` | {d.sccSize} | {d.declCount} | {sorryStr} | {mods} |"
    lines := lines.push ""

  -- Sorry-incomplete section
  let sorryOnes := payload.disconnected.filter (fun d => d.category == "sorry_incomplete")
  if sorryOnes.size > 0 then
    lines := lines.push "## Sorry-Incomplete Capstones (Proof Debt)"
    lines := lines.push ""
    lines := lines.push "These capstones use `sorry` in their proofs. The statements might be true"
    lines := lines.push "but the proofs are incomplete. This is debt, not a fake root."
    lines := lines.push ""
    lines := lines.push "| Capstone | SCC Size | Decls | Imports Mathlib |"
    lines := lines.push "| --- | --- | --- | --- |"
    for d in sorryOnes do
      let mlStr := if d.importsMathlib then "yes" else "no"
      lines := lines.push s!"| `{d.repName}` | {d.sccSize} | {d.declCount} | {mlStr} |"
    lines := lines.push ""

  -- Unknown section
  let unknowns := payload.disconnected.filter (fun d => d.category == "unknown")
  if unknowns.size > 0 then
    lines := lines.push "## Unknown Disconnected Capstones"
    lines := lines.push ""
    lines := lines.push "These capstones are disconnected but don't fit the above categories."
    lines := lines.push "They may have complex dependency patterns requiring manual inspection."
    lines := lines.push ""
    lines := lines.push "| Capstone | SCC Size | Decls | Imports Mathlib | Module Imports |"
    lines := lines.push "| --- | --- | --- | --- | --- |"
    for d in unknowns do
      let mlStr := if d.importsMathlib then "yes" else "**NO**"
      let mods := String.intercalate ", " d.moduleImports.toList
      lines := lines.push s!"| `{d.repName}` | {d.sccSize} | {d.declCount} | {mlStr} | {mods} |"
    lines := lines.push ""

  IO.FS.writeFile fp (String.intercalate "\n" lines.toList)

------------------------------------------------------------------------
-- Main
------------------------------------------------------------------------

def main (args : List String) : IO UInt32 := do
  match args with
  | [importModStr, nsPrefix, mdOut] =>
      initSearchPath (← findSysroot)
      let env ← importModules #[{ module := importModStr.toName }] {}
      IO.println s!"[DisconnectedAudit] Loading {importModStr}..."
      let payload ← runAudit env nsPrefix
      writeMarkdown payload mdOut
      IO.println s!"[DisconnectedAudit] Wrote markdown to {mdOut}"
      return 0
  | [importModStr, nsPrefix, mdOut, jsonOut] =>
      initSearchPath (← findSysroot)
      let env ← importModules #[{ module := importModStr.toName }] {}
      IO.println s!"[DisconnectedAudit] Loading {importModStr}..."
      let payload ← runAudit env nsPrefix
      writeMarkdown payload mdOut
      let jsonFp := System.FilePath.mk jsonOut
      if let some p := jsonFp.parent then
        IO.FS.createDirAll p
      IO.FS.writeFile jsonFp (toJson payload).pretty
      IO.println s!"[DisconnectedAudit] Wrote markdown to {mdOut} and JSON to {jsonOut}"
      return 0
  | _ =>
      IO.eprintln "usage: disconnectedAudit <import-module> <namespace-prefix> <output.md> [output.json]"
      IO.eprintln "example: .lake/build/bin/disconnectedAudit InfoGeometry InfoGeometry reports/dag/disconnected-audit.md reports/dag/disconnected-audit.json"
      return 1
