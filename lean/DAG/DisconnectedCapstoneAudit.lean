import Lean
import Lean.Data.Json
import DAG.Basic
import DAG.Hydrate
import DAG.Analysis
import DAG.Util

open Lean
open DAG

/--
# Disconnected Capstone Audit

Pure-Lean audit that identifies capstone SCCs (no reverse dependents)
that have no path from any true dependency root, and classifies them
by the nature of their disconnection.

A theorem is "mathless" when:
1. It lives in an SCC unreachable from any root SCC (depthMin = none), AND
2. The SCC contains declarations that are axioms/opaque, OR
3. The SCC's module imports form a disconnected island with no Mathlib grounding

Usage:
  lake env lean --run lean/DAG/DisconnectedCapstoneAudit.lean \
    InfoGeometry InfoGeometry reports/dag/disconnected-capstones.json
-/

structure DeclAudit where
  name       : String
  kind       : String          -- "axiom" | "opaque" | "theorem" | "definition" | "other"
  isFakeRoot : Bool            -- true if axiom/opaque
  module     : String          -- source module
  deriving Repr, ToJson

structure DisconnectedSCC where
  repName    : String          -- representative declaration name
  repKind    : String          -- kind of representative
  isFakeRoot : Bool            -- true if rep is axiom/opaque
  size       : Nat             -- number of declarations in SCC
  decls      : Array DeclAudit -- all non-generated declarations in SCC
  module     : String          -- source module of representative
  deriving Repr, ToJson

structure AuditPayload where
  totalSCCs          : Nat
  rootSCCs           : Nat
  capstoneSCCs       : Nat
  disconnectedCaps   : Nat
  fakeRootCaps       : Nat      -- disconnected caps that are axiom/opaque
  disconnectedIslands : Array DisconnectedSCC
  mathlibRootDecls   : Array String  -- root SCC representatives that are Mathlib
  fakeRootDecls      : Array String  -- root SCC reps that are axiom/opaque (should be empty)
  deriving Repr, ToJson

def getDeclKind : ConstantInfo → String
  | .axiomInfo _    => "axiom"
  | .opaqueInfo _   => "opaque"
  | .thmInfo _      => "theorem"
  | .defnInfo _     => "definition"
  | .ctorInfo _     => "constructor"
  | .recInfo _      => "recursor"
  | .quotInfo _     => "quot"
  | .inductInfo _   => "inductive"

def isFakeRootDecl (ci : ConstantInfo) : Bool :=
  match ci with
  | .axiomInfo _  => true
  | .opaqueInfo _ => true
  | _             => false

def getModuleName (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some modIdx => toString env.header.moduleNames[modIdx.toNat]!
  | none        => "unknown"

def auditDecl (name : Name) (env : Environment) : Option DeclAudit := do
  let ci ← env.find? name
  let kind := getDeclKind ci
  let isFake := isFakeRootDecl ci
  let mod := getModuleName env name
  { name := toString name
  , kind := kind
  , isFakeRoot := isFake
  , module := mod
  : DeclAudit }

def auditDisconnectedSCC
    (h : HydratedGraph Lean.Name)
    (env : Environment)
    (si : Nat)
    : DisconnectedSCC :=
  let comp := h.sccs[si]!
  let repName := Id.run do
    for vi in [:comp.size] do
      let v := comp[vi]!
      let n := h.toGraph.nodes[v]!
      if !isGeneratedOrUnstableName n then
        return n
    if h.sccs[si]!.isEmpty then
      return Name.anonymous
    return h.toGraph.nodes[h.sccs[si]![0]!]!

  let repCi := env.find? repName
  let repKind := repCi.map getDeclKind |>.getD "unknown"
  let isFake := repCi.map isFakeRootDecl |>.getD false
  let mod := getModuleName env repName

  let decls := Id.run do
    let mut out : Array DeclAudit := #[]
    for vi in [:comp.size] do
      let v := comp[vi]!
      let n := h.toGraph.nodes[v]!
      if !isGeneratedOrUnstableName n then
        if let some audit := auditDecl n env then
          out := out.push audit
    out

  { repName := toString repName
  , repKind := repKind
  , isFakeRoot := isFake
  , size := comp.size
  , decls := decls
  , module := mod
  }

def isMathlibRoot (h : HydratedGraph Lean.Name) (env : Environment) (si : Nat) : Bool :=
  let comp := h.sccs[si]!
  Id.run do
    for vi in [:comp.size] do
      let v := comp[vi]!
      let n := h.toGraph.nodes[v]!
      if !isGeneratedOrUnstableName n then
        if let some _ci := env.find? n then
          if let some modIdx ← env.getModuleIdxFor? n then
            let modName := toString env.header.moduleNames[modIdx.toNat]!
            if modName.startsWith "Mathlib" || modName.startsWith "Lean" || modName.startsWith "Std" then
              return true
    false

def runAudit (env : Environment) (nsPrefix : String) : IO AuditPayload := do
  IO.println "[DisconnectedCapstoneAudit] Building graph..."
  let g := buildGraphFromEnv env (some nsPrefix)
  IO.println s!"[DisconnectedCapstoneAudit] Graph: {g.nodes.size} nodes, {g.forward.foldl (fun acc a => acc + a.size) 0} edges"

  IO.println "[DisconnectedCapstoneAudit] Computing SCCs..."
  let h := hydrate g
  IO.println s!"[DisconnectedCapstoneAudit] SCCs: {h.sccs.size}"

  let roots := rootSet h
  let caps := capstoneSet h
  let dMin := depthMinFromRoots h

  IO.println s!"[DisconnectedCapstoneAudit] Roots: {roots.size}, Capstones: {caps.size}"

  -- Find disconnected capstones (no path from any root)
  let disconnectedCaps := Id.run do
    let mut out : Array Nat := #[]
    for si in caps do
      if dMin[si]!.isNone then
        out := out.push si
    out

  IO.println s!"[DisconnectedCapstoneAudit] Disconnected capstones: {disconnectedCaps.size}"

  -- Classify disconnected capstones
  let fakeRootCaps := Id.run do
    let mut out : Array DisconnectedSCC := #[]
    for si in disconnectedCaps do
      let scc := auditDisconnectedSCC h env si
      out := out.push scc
    out

  let fakeRootCount := fakeRootCaps.foldl (fun acc s => if s.isFakeRoot then acc + 1 else acc) 0

  -- Find Mathlib-rooted SCCs
  let mathlibRoots := Id.run do
    let mut out : Array String := #[]
    for si in roots do
      if isMathlibRoot h env si then
        let rep := Id.run do
          let comp := h.sccs[si]!
          for vi in [:comp.size] do
            let v := comp[vi]!
            let n := h.toGraph.nodes[v]!
            if !isGeneratedOrUnstableName n then
              return toString n
          if h.sccs[si]!.isEmpty then return "anonymous"
          return toString h.toGraph.nodes[h.sccs[si]![0]!]!
        out := out.push rep
    out

  -- Find fake roots (axiom/opaque in root SCCs -- these should not exist)
  let fakeRoots := Id.run do
    let mut out : Array String := #[]
    for si in roots do
      let comp := h.sccs[si]!
      for vi in [:comp.size] do
        let v := comp[vi]!
        let n := h.toGraph.nodes[v]!
        if !isGeneratedOrUnstableName n then
          if let some ci := env.find? n then
            if isFakeRootDecl ci then
              out := out.push s!"{toString n} ({getDeclKind ci})"
    out

  let payload : AuditPayload := {
    totalSCCs := h.sccs.size,
    rootSCCs := roots.size,
    capstoneSCCs := caps.size,
    disconnectedCaps := disconnectedCaps.size,
    fakeRootCaps := fakeRootCount,
    disconnectedIslands := fakeRootCaps,
    mathlibRootDecls := mathlibRoots,
    fakeRootDecls := fakeRoots
  }
  return payload

def writeJson (payload : AuditPayload) (path : String) : IO Unit := do
  let p := System.FilePath.mk path
  if let some parent := p.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path (toJson payload).pretty
  IO.println s!"[DisconnectedCapstoneAudit] Wrote report to {path}"

def writeMarkdown (payload : AuditPayload) (path : String) : IO Unit := do
  let p := System.FilePath.mk path
  if let some parent := p.parent then
    IO.FS.createDirAll parent
  let mut lines : Array String := #[]
  lines := lines.push "# Disconnected Capstone Audit"
  lines := lines.push ""
  lines := lines.push s!"- Total SCCs: `{payload.totalSCCs}`"
  lines := lines.push s!"- Root SCCs (no outgoing edges): `{payload.rootSCCs}`"
  lines := lines.push s!"- Capstone SCCs (no incoming edges): `{payload.capstoneSCCs}`"
  lines := lines.push s!"- Disconnected capstones (no path from roots): `{payload.disconnectedCaps}`"
  lines := lines.push s!"- Fake root capstones (axiom/opaque): `{payload.fakeRootCaps}`"
  lines := lines.push ""

  if payload.fakeRootDecls.size > 0 then
    lines := lines.push "## FAKE ROOTS IN ROOT SCCs (CRITICAL)"
    lines := lines.push ""
    lines := lines.push "These declarations are axioms/opaque in root SCCs."
    lines := lines.push "They assert mathematical content without proof."
    lines := lines.push ""
    for r in payload.fakeRootDecls do
      lines := lines.push s!"- `{r}`"
    lines := lines.push ""

  lines := lines.push "## Mathlib-Rooted SCCs"
  lines := lines.push ""
  lines := lines.push s!"{payload.mathlibRootDecls.size} root SCCs are grounded in Mathlib/Lean/Std."
  lines := lines.push ""
  for r in payload.mathlibRootDecls do
    lines := lines.push s!"- `{r}`"
  lines := lines.push ""

  lines := lines.push "## Disconnected Capstone Islands"
  lines := lines.push ""
  lines := lines.push s!"{payload.disconnectedIslands.size} capstone SCCs have no path from any root."
  lines := lines.push ""
  lines := lines.push "| Representative | Kind | Fake Root | Size | Module |"
  lines := lines.push "| --- | --- | --- | --- | --- |"
  for scc in payload.disconnectedIslands do
    let fake := if scc.isFakeRoot then "YES" else "no"
    lines := lines.push s!"| `{scc.repName}` | {scc.repKind} | {fake} | {scc.size} | {scc.module} |"

  lines := lines.push ""
  lines := lines.push "## Declarations in Disconnected Islands"
  lines := lines.push ""
  for scc in payload.disconnectedIslands do
    lines := lines.push s!"### {scc.repName}"
    lines := lines.push ""
    lines := lines.push "| Name | Kind | Fake Root | Module |"
    lines := lines.push "| --- | --- | --- | --- |"
    for d in scc.decls do
      let fake := if d.isFakeRoot then "YES" else "no"
      lines := lines.push s!"| `{d.name}` | {d.kind} | {fake} | {d.module} |"
    lines := lines.push ""

  IO.FS.writeFile path (String.intercalate "\n" lines.toList)
  IO.println s!"[DisconnectedCapstoneAudit] Wrote report to {path}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [importModStr, nsPrefix, jsonOut] =>
      initSearchPath (← findSysroot)
      let env ← importModules #[{ module := importModStr.toName }] {}
      IO.println s!"[DisconnectedCapstoneAudit] Loading {importModStr}..."
      let payload ← runAudit env nsPrefix
      writeJson payload jsonOut
      let mdOut := (jsonOut.dropEnd 5).toString ++ ".md"
      writeMarkdown payload mdOut
      return 0
  | [importModStr, nsPrefix, jsonOut, mdOut] =>
      initSearchPath (← findSysroot)
      let env ← importModules #[{ module := importModStr.toName }] {}
      IO.println s!"[DisconnectedCapstoneAudit] Loading {importModStr}..."
      let payload ← runAudit env nsPrefix
      writeJson payload jsonOut
      writeMarkdown payload mdOut
      return 0
  | _ =>
      IO.eprintln "usage: disconnected_capstone_audit <import-module> <namespace-prefix> <output.json> [output.md]"
      IO.eprintln "example: lake env lean --run lean/DAG/DisconnectedCapstoneAudit.lean InfoGeometry InfoGeometry reports/dag/disconnected-capstones.json"
      return 1
