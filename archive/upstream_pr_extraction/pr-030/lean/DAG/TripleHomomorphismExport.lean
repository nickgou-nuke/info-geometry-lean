import Lean
import Lean.Data.Json
import DAG.TripleSystem

open Lean

namespace DAG.TripleHomomorphismExport

/-- Concrete JSONL triple row used by RDF/Arango-style finite exports. -/
structure TripleRow where
  subject : String
  predicate : String
  object : String
deriving Repr, BEq, Hashable, ToJson

/-- Concrete JSONL mapping row for finite homomorphism checks. -/
structure MapRow where
  kind : String
  source : String
  target : String
deriving Repr, ToJson

structure MissingTripleRow where
  subject : String
  predicate : String
  object : String
  mappedSubject : String
  mappedPredicate : String
  mappedObject : String
deriving Repr, ToJson

structure HomomorphismAuditRow where
  sourceTriples : Nat
  targetTriples : Nat
  objectMappings : Nat
  relationMappings : Nat
  checkedTriples : Nat
  preservedTriples : Nat
  missingTriples : Nat
  leanVerified : Bool
  verificationTier : String
  proofAuthority : String
  checker : String
deriving Repr, ToJson

private def trimLine (s : String) : String :=
  s.trimAscii.toString

private def parseTripleRow (json : Json) : Except String TripleRow := do
  let subject ← json.getObjValAs? String "subject"
  let predicate ← json.getObjValAs? String "predicate"
  let object ← json.getObjValAs? String "object"
  pure { subject, predicate, object }

private def parseMapRow (json : Json) : Except String MapRow := do
  let kind ← json.getObjValAs? String "kind"
  let source ← json.getObjValAs? String "source"
  let target ← json.getObjValAs? String "target"
  pure { kind, source, target }

private def readJsonlRows (path : System.FilePath) (parse : Json → Except String α) :
    IO (Array α) := do
  let content ← IO.FS.readFile path
  let mut rows : Array α := #[]
  for raw in content.splitOn "\n" do
    let line := trimLine raw
    if line.isEmpty then
      continue
    let json ←
      match Json.parse line with
      | Except.ok json => pure json
      | Except.error err => throw <| IO.userError s!"{path}: invalid JSONL row: {err}"
    let row ←
      match parse json with
      | Except.ok row => pure row
      | Except.error err => throw <| IO.userError s!"{path}: invalid JSONL row: {err}"
    rows := rows.push row
  pure rows

private def readTriples (path : System.FilePath) : IO (Array TripleRow) :=
  readJsonlRows path parseTripleRow

private def readMappings (path : System.FilePath) : IO (Array MapRow) :=
  readJsonlRows path parseMapRow

private def writeJsonl {α} [ToJson α] (path : System.FilePath) (rows : Array α) : IO Unit := do
  match path.parent with
  | some parent => IO.FS.createDirAll parent
  | none => pure ()
  let lines := String.intercalate "\n" <| rows.toList.map fun row => (toJson row).compress
  IO.FS.writeFile path (lines ++ if rows.isEmpty then "" else "\n")

private def writeJson (path : System.FilePath) (json : Json) : IO Unit := do
  match path.parent with
  | some parent => IO.FS.createDirAll parent
  | none => pure ()
  IO.FS.writeFile path (json.pretty ++ "\n")

private def tripleKey (t : TripleRow) : String :=
  s!"{t.subject}|||{t.predicate}|||{t.object}"

private def mapLookup (rows : Array MapRow) (kind value : String) : String :=
  match rows.find? (fun row => row.kind == kind && row.source == value) with
  | some row => row.target
  | none => value

private def mappedTriple (maps : Array MapRow) (t : TripleRow) : TripleRow :=
  { subject := mapLookup maps "object" t.subject
    predicate := mapLookup maps "relation" t.predicate
    object := mapLookup maps "object" t.object
  }

private def objectMapCount (maps : Array MapRow) : Nat :=
  maps.foldl (init := 0) fun n row => if row.kind == "object" then n + 1 else n

private def relationMapCount (maps : Array MapRow) : Nat :=
  maps.foldl (init := 0) fun n row => if row.kind == "relation" then n + 1 else n

/--
Finite string-level triple homomorphism checker.

This is not a theorem about arbitrary Lean objects.  It is the Lean-native
checker for exported RDF/Arango-style rows: every source triple must map to an
existing target triple under the supplied object/relation maps.  Python and
vector layers can generate candidate maps; this checker is the native
preservation gate for finite triple rows.
-/
def auditHomomorphism
    (sourceTriples targetTriples : Array TripleRow)
    (maps : Array MapRow) :
    HomomorphismAuditRow × Array MissingTripleRow := Id.run do
  let targetKeys := targetTriples.foldl (init := ({} : Std.HashSet String)) fun acc t =>
    acc.insert (tripleKey t)
  let mut preserved := 0
  let mut missing : Array MissingTripleRow := #[]
  for sourceTriple in sourceTriples do
    let mapped := mappedTriple maps sourceTriple
    if targetKeys.contains (tripleKey mapped) then
      preserved := preserved + 1
    else
      missing := missing.push {
        subject := sourceTriple.subject
        predicate := sourceTriple.predicate
        object := sourceTriple.object
        mappedSubject := mapped.subject
        mappedPredicate := mapped.predicate
        mappedObject := mapped.object
      }
  let leanVerified := missing.isEmpty
  let audit : HomomorphismAuditRow := {
    sourceTriples := sourceTriples.size
    targetTriples := targetTriples.size
    objectMappings := objectMapCount maps
    relationMappings := relationMapCount maps
    checkedTriples := sourceTriples.size
    preservedTriples := preserved
    missingTriples := missing.size
    leanVerified := leanVerified
    verificationTier := "lean_native_finite_triple_homomorphism"
    proofAuthority := "Lean finite triple preservation checker"
    checker := "DAG.TripleHomomorphismExport.auditHomomorphism"
  }
  (audit, missing)

private def runAudit
    (sourcePathStr targetPathStr mapPathStr auditPathStr missingPathStr : String) :
    IO UInt32 := do
  let sourceTriples ← readTriples (System.FilePath.mk sourcePathStr)
  let targetTriples ← readTriples (System.FilePath.mk targetPathStr)
  let maps ← readMappings (System.FilePath.mk mapPathStr)
  let (audit, missing) := auditHomomorphism sourceTriples targetTriples maps
  writeJson (System.FilePath.mk auditPathStr) (toJson audit)
  writeJsonl (System.FilePath.mk missingPathStr) missing
  IO.println s!"[TripleHomomorphismExport] checked triples={audit.checkedTriples}"
  IO.println s!"[TripleHomomorphismExport] preserved={audit.preservedTriples}"
  IO.println s!"[TripleHomomorphismExport] missing={audit.missingTriples}"
  pure (if audit.leanVerified then 0 else 2)

def main (args : List String) : IO UInt32 := do
  match args with
  | [sourcePath, targetPath, mapPath, auditPath, missingPath] =>
      runAudit sourcePath targetPath mapPath auditPath missingPath
  | _ =>
      IO.eprintln "usage: TripleHomomorphismExport <source-triples.jsonl> <target-triples.jsonl> <maps.jsonl> <audit.json> <missing.jsonl>"
      IO.eprintln "triple rows require: {\"subject\":\"...\",\"predicate\":\"...\",\"object\":\"...\"}"
      IO.eprintln "map rows require: {\"kind\":\"object|relation\",\"source\":\"...\",\"target\":\"...\"}"
      pure 1

end DAG.TripleHomomorphismExport

def main (args : List String) : IO UInt32 :=
  DAG.TripleHomomorphismExport.main args
