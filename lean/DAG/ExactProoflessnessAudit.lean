import Lean
import Lean.Data.Json
import DAG.Basic
import DAG.Util

open Lean
open DAG

structure Blocker where
  kind : String
  blocker : String
  via : String
  deriving Repr, ToJson

structure DeclAudit where
  name : String
  declarationKind : String
  declarationModule : String
  status : String
  blockerKind : String
  blocker : String
  via : String
  hasDirectAxiom : Bool
  hasDirectOpaque : Bool
  hasDirectSorry : Bool
  deriving Repr, ToJson

structure ExactAuditPayload where
  namespacePrefix : String
  totalChecked : Nat
  inspectedDecls : Nat
  blockedDecls : Nat
  cleanDecls : Nat
  explicitAxiom : Nat
  explicitOpaque : Nat
  directSorry : Nat
  transitive : Nat
  trustedModules : Array String
  findings : Array DeclAudit
  deriving Repr, ToJson

/-- Return the declaration kind label used by the report. -/
def declKind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"

/-- Module name (or "unknown"). -/
def declarationModuleName (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some midx =>
      let moduleNames := env.header.moduleNames
      match moduleNames[midx.toNat]? with
      | some n => toString n
      | none => "unknown"
  | none => "unknown"

/-- Is declaration/module inside the scope prefix (e.g. "InfoGeometry"). -/
def inNamespacePrefix (env : Environment) (name : Name) (nsPrefix : String) : Bool :=
  declarationModuleName env name |>.startsWith nsPrefix

/-- Trusted non-audit modules that we intentionally do not recurse into. -/
def isTrustedModule (moduleName : String) (trusted : Array String) : Bool :=
  trusted.any (fun p => moduleName == p || moduleName.startsWith (p ++ "."))

/-- Conservative direct contamination on a declaration. -/
def directBlocker
    (env : Environment)
    (name : Name)
    (ci : ConstantInfo)
    (trusted : Array String)
    : Option Blocker :=
  let moduleName := declarationModuleName env name
  let trustedModule := isTrustedModule moduleName trusted
  let hasDirectSorry : Bool :=
    ci.type.hasSorry || (match ci.value? (allowOpaque := true) with
      | none => false
      | some v => v.hasSorry)
  if !trustedModule then
    match ci with
    | .axiomInfo _ =>
        some { kind := "blocked.explicitAxiom", blocker := toString name, via := toString name }
    | .opaqueInfo _ =>
        some { kind := "blocked.explicitOpaque", blocker := toString name, via := toString name }
    | _ =>
        if hasDirectSorry then
          some { kind := "blocked.localSorry", blocker := toString name, via := toString name }
        else
          none
  else
    if hasDirectSorry then
      some { kind := "blocked.localSorry", blocker := toString name, via := toString name }
    else
      none

/-- Direct dependencies from a declaration, excluding generated/internal names. -/
def collectDirectDeps
    (env : Environment)
    (name : Name)
    (cache : IO.Ref (Std.HashMap Name (Array Name)))
    : IO (Array Name) := do
  let cacheMap := (← cache.get)
  match cacheMap.get? name with
  | some memoized => return memoized
  | none =>
      match env.find? name with
      | none =>
          cache.modify (fun m => m.insert name #[])
          return #[]
      | some ci =>
          let mut deps : Array Name := #[]
          let mut seen : Std.HashSet Name := {}
          for (dep, _) in DAG.edgesFromConstantInfo ci do
            if (dep == name) || isGeneratedOrUnstableName dep then
              continue
            if !seen.contains dep then
              deps := deps.push dep
              seen := seen.insert dep
          cache.modify (fun m => m.insert name deps)
          return deps

/-- Compute the first exact blocker for a declaration with memoized DFS. -/
partial def findExactBlocker
    (env : Environment)
    (name : Name)
    (trusted : Array String)
    (nsPrefix : String)
    (depCache : IO.Ref (Std.HashMap Name (Array Name)))
    (memo : IO.Ref (Std.HashMap Name (Option Blocker)))
    (visiting : Std.HashSet Name)
    : IO (Option Blocker) := do
  let memoMap := ← memo.get
  match memoMap.get? name with
  | some cached => return cached
  | none =>
      if visiting.contains name then
        return none
      let visiting := visiting.insert name
      match env.find? name with
      | none =>
          memo.modify (fun m => m.insert name none)
          return none
      | some ci =>
          match directBlocker env name ci trusted with
          | some b =>
              memo.modify (fun m => m.insert name (some b))
              return some b
          | none =>
              let deps := ← collectDirectDeps env name depCache
              let mut result : Option Blocker := none
              for dep in deps do
                if result.isSome then
                  break
                let depModule := declarationModuleName env dep
                if inNamespacePrefix env dep nsPrefix && ! (isTrustedModule depModule trusted) then
                  let child := ← findExactBlocker env dep trusted nsPrefix depCache memo visiting
                  match child with
                  | none => pure ()
                  | some c =>
                      result := some { kind := s!"{c.kind}-via-{depModule}", blocker := c.blocker, via := toString dep }
                else
                  pure ()
              memo.modify (fun m => m.insert name result)
              return result

def isGeneratedOrIgnored (name : Name) : Bool :=
  isGeneratedOrUnstableName name
    || name.isInternal
    || name.hasMacroScopes

/-- Main audit pass over all declarations in the selected namespace. -/
def runAudit (env : Environment) (nsPrefix : String) (trusted : Array String) : IO ExactAuditPayload := do
  let g := buildGraphFromEnv env (some nsPrefix)
  let totalChecked := g.nodes.size
  let depCache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let memo ← IO.mkRef ({} : Std.HashMap Name (Option Blocker))

  let mut inspected : Nat := 0
  let mut blocked : Nat := 0
  let mut clean : Nat := 0
  let mut axiomCount : Nat := 0
  let mut opaqueCount : Nat := 0
  let mut sorryCount : Nat := 0
  let mut transitCount : Nat := 0
  let mut findings : Array DeclAudit := #[]

  let mut idx : Nat := 0
  while idx < g.nodes.size do
    let n := g.nodes[idx]!
    let hasCi := env.find? n
    if let some ci := hasCi then
      if !isGeneratedOrIgnored n then
        inspected := inspected + 1
        let moduleName := declarationModuleName env n
        let direct := directBlocker env n ci trusted
        let blocker : Option Blocker ←
          match direct with
          | some _ => pure direct
          | none =>
              findExactBlocker env n trusted nsPrefix depCache memo {}

        let reason := blocker.map (fun b => b.kind) |>.getD "clean"
        match reason with
        | "clean" =>
            clean := clean + 1
        | _ =>
            blocked := blocked + 1
            match reason with
            | "blocked.explicitAxiom" => axiomCount := axiomCount + 1
            | "blocked.explicitOpaque" => opaqueCount := opaqueCount + 1
            | "blocked.localSorry" => sorryCount := sorryCount + 1
            | _ => transitCount := transitCount + 1
            let b := blocker.getD { kind := "", blocker := "", via := "" }
            findings := findings.push {
              name := toString n
              declarationKind := declKind ci
              declarationModule := moduleName
              status := reason
              blockerKind := b.kind
              blocker := b.blocker
              via := b.via
              hasDirectAxiom := direct.isSome && reason = "blocked.explicitAxiom"
              hasDirectOpaque := direct.isSome && reason = "blocked.explicitOpaque"
              hasDirectSorry := direct.isSome && reason = "blocked.localSorry"
            }
    idx := idx + 1

  let payload : ExactAuditPayload := {
    namespacePrefix := nsPrefix
    totalChecked := totalChecked
    inspectedDecls := inspected
    blockedDecls := blocked
    cleanDecls := clean
    explicitAxiom := axiomCount
    explicitOpaque := opaqueCount
    directSorry := sorryCount
    transitive := transitCount
    trustedModules := trusted
    findings := findings
  }

  return payload


def parseTrusted (arg : String) : Array String :=
  Id.run do
    let parts := arg.splitOn ","
    let mut out : Array String := #[]
    for p in parts do
      let s := p.trimAscii
      if !s.isEmpty then
        out := out.push (s.toString)
    return out

def defaultTrustedModules : Array String :=
  #[
    "Init",
    "Lean",
    "Std",
    "Mathlib"
  ]

def strictTrustedModules : Array String :=
  #[
    "Init",
    "Lean",
    "Std",
    "Mathlib",
    "DAG",
    "InfoGeometry.Meta",
    "InfoGeometry.Lint",
    "InfoGeometry.Canonical.SpineAttributes"
  ]

def mathcoreTrustedModules : Array String :=
  #[
    "Init",
    "Lean",
    "Std",
    "Mathlib"
  ]

def trustedFromArg (arg : String) : Array String :=
  let s := arg.trimAscii
  if s == "strict" then
    strictTrustedModules
  else if s == "mathcore" then
    mathcoreTrustedModules
  else
    let parsed := parseTrusted arg
    if parsed.isEmpty then
      defaultTrustedModules
      else
      parsed


def writeMarkdown (payload : ExactAuditPayload) (path : String) : IO Unit := do
  let p := System.FilePath.mk path
  if let some dir := p.parent then
    IO.FS.createDirAll dir
  let mut lines : Array String := #[]
  lines := lines.push "# Exact Prooflessness Audit"
  lines := lines.push ""
  lines := lines.push s!"- Namespace prefix: `{payload.namespacePrefix}`"
  lines := lines.push s!"- Total candidates: {payload.totalChecked}"
  lines := lines.push s!"- Inspected declarations: {payload.inspectedDecls}"
  lines := lines.push s!"- Blocked declarations: {payload.blockedDecls}"
  lines := lines.push s!"- Clean declarations: {payload.cleanDecls}"
  lines := lines.push ""
  lines := lines.push "## Exact blocker classes"
  lines := lines.push s!"- explicitAxiom: {payload.explicitAxiom}"
  lines := lines.push s!"- explicitOpaque: {payload.explicitOpaque}"
  lines := lines.push s!"- directSorry: {payload.directSorry}"
  lines := lines.push s!"- transitive: {payload.transitive}"
  lines := lines.push ""
  lines := lines.push "## Blocked declarations"
  lines := lines.push ""
  lines := lines.push "| Declaration | Kind | Module | Status | Blocker | Via | Direct? |"
  lines := lines.push "| --- | --- | --- | --- | --- | --- | --- |"

  for b in payload.findings do
    let directMark := if b.hasDirectAxiom || b.hasDirectOpaque || b.hasDirectSorry then "yes" else "no"
    lines := lines.push s!"| `{b.name}` | {b.declarationKind} | {b.declarationModule} | `{b.status}` | `{b.blocker}` | `{b.via}` | {directMark} |"

  lines := lines.push ""
  lines := lines.push "## Notes"
  lines := lines.push "- This report is derived from kernel-visible declaration metadata and direct dependency traversal."
  lines := lines.push "- Transitive classes record the witness path module where the first block is introduced."
  IO.FS.writeFile p (String.intercalate "\n" lines.toList)


def usage : IO Unit := do
  IO.eprintln "usage: exactProoflessnessAudit <import-module> <namespace-prefix> <output.md> [output.json] [trusted-prefixes|strict|mathcore]"
  IO.eprintln "- trusted-prefixes is comma-separated module prefixes to skip as blockers (defaults to core/runtime modules)."
  IO.eprintln "- use `strict` to also skip known InfoGeometry infrastructure modules (Meta, Lint, Canonical.SpineAttributes, DAG)."
  IO.eprintln "- use `mathcore` for base Lean/Mathlib-only trust."
  IO.eprintln "example: .lake/build/bin/exactProoflessnessAudit InfoGeometry.All InfoGeometry reports/dag/exact-prooflessness-audit.md reports/dag/exact-prooflessness-audit.json"
  IO.eprintln "example: .lake/build/bin/exactProoflessnessAudit InfoGeometry.All InfoGeometry reports/dag/exact-prooflessness-audit.md reports/dag/exact-prooflessness-audit.json strict"
  IO.eprintln "example: .lake/build/bin/exactProoflessnessAudit InfoGeometry.All InfoGeometry reports/dag/exact-prooflessness-audit.md reports/dag/exact-prooflessness-audit.json mathcore"

/-- entrypoint -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [_importModStr, _nsPrefix, _mdOut] =>
      usage
      return 1
  | [importModStr, nsPrefix, mdOut, jsonOut] =>
      initSearchPath (← findSysroot)
      let env ← importModules #[{ module := importModStr.toName }] {}
      let payload ← runAudit env nsPrefix defaultTrustedModules
      writeMarkdown payload mdOut
      let jPath := System.FilePath.mk jsonOut
      if let some dir := jPath.parent then
        IO.FS.createDirAll dir
      IO.FS.writeFile jPath (toJson payload).pretty
      IO.println s!"[exactProoflessnessAudit] wrote {mdOut} and {jsonOut}"
      return 0
  | [importModStr, nsPrefix, mdOut, jsonOut, trustedArg] =>
      initSearchPath (← findSysroot)
      let env ← importModules #[{ module := importModStr.toName }] {}
      let trusted := trustedFromArg trustedArg
      let payload ← runAudit env nsPrefix trusted
      writeMarkdown payload mdOut
      let jPath := System.FilePath.mk jsonOut
      if let some dir := jPath.parent then
        IO.FS.createDirAll dir
      IO.FS.writeFile jPath (toJson payload).pretty
      IO.println s!"[exactProoflessnessAudit] wrote {mdOut} and {jsonOut}"
      return 0
  | _ =>
      usage
      return 1
