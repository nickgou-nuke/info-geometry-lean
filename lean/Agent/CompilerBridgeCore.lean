import Lean
import Lean.PrettyPrinter
import Lean.Server.FileWorker.RequestHandling
import Lean.Server.FileWorker.Utils
import Lean.Server.Requests
import Lean.Server.Rpc.RequestHandling
import Lean.Server.Utils
import Lean.Util.Sorry
import Lean.Widget.InteractiveDiagnostic

import Agent.Protocol

open Lean
open Lean.Server
open Lean.Server.RequestM

namespace IG.Compiler

structure ProofStateView where
  responseMeta : ResponseMeta
  diagnostics : Array CompilerError := #[]
  goals : Array GoalView := #[]
deriving Inhabited

private structure DagIndexMeta where
  schemaVersion : Nat
  importRoot : String
  nsFilter : String
  oleanHash : String
deriving Inhabited, FromJson

def sessionIdOfDoc (doc : FileWorker.EditableDocument) : SessionId :=
  { value := toString doc.meta.uri }

private def docPathOfDoc? (doc : FileWorker.EditableDocument) : Option System.FilePath :=
  System.Uri.fileUriToPath? doc.meta.uri

private def isRepoRootCandidate (path : System.FilePath) : IO Bool := do
  let hasToolchain ← (path / "lean-toolchain").pathExists
  let hasLakefile ← (path / "lakefile.lean").pathExists
  let hasGit ← (path / ".git").pathExists
  return hasToolchain || hasLakefile || hasGit

private partial def findRepoRootFrom? (start : System.FilePath) : IO (Option System.FilePath) := do
  let current ←
    if ← start.isDir then
      pure start
    else
      pure (start.parent.getD start)
  let rec go (path : System.FilePath) : IO (Option System.FilePath) := do
    if ← isRepoRootCandidate path then
      return some path
    match path.parent with
    | some parent => go parent
    | none => return none
  go current

private def fallbackRepoRoot? : IO (Option System.FilePath) := do
  let cwd ← IO.currentDir
  if ← isRepoRootCandidate cwd then
    return some cwd
  else
    return none

private def repoRootOfDoc? (doc : FileWorker.EditableDocument) : IO (Option System.FilePath) := do
  match docPathOfDoc? doc with
  | some path =>
      match ← findRepoRootFrom? path with
      | some root => return some root
      | none => fallbackRepoRoot?
  | none => fallbackRepoRoot?

private def readTrimmedFile? (path : System.FilePath) : IO (Option String) := do
  if !(← path.pathExists) then
    return none
  let content ← IO.FS.readFile path
  let trimmed := content.trimAscii.toString
  if trimmed.isEmpty then
    return none
  return some trimmed

private def readRepoTrimmedFile? (root? : Option System.FilePath) (relPath : String) : IO (Option String) := do
  match root? with
  | some root => readTrimmedFile? (root / relPath)
  | none => return none

private def readJsonFile? [FromJson α] (path : System.FilePath) : IO (Option α) := do
  match (← readTrimmedFile? path) with
  | none => return none
  | some content =>
      match Json.parse content with
      | .error err =>
          dbg_trace s!"[IG.Compiler] failed to parse JSON at {path}: {err}"
          return none
      | .ok json =>
          match fromJson? json with
          | .error err =>
              dbg_trace s!"[IG.Compiler] failed to decode JSON at {path}: {err}"
              return none
          | .ok value => return some value

private def readRepoJsonFile? [FromJson α] (root? : Option System.FilePath) (relPath : String) :
    IO (Option α) := do
  match root? with
  | some root => readJsonFile? (root / relPath)
  | none => return none

def envFingerprintOfDoc (doc : FileWorker.EditableDocument) : IO EnvFingerprint := do
  let repoRoot? ← repoRootOfDoc? doc
  let leanToolchain? ← readRepoTrimmedFile? repoRoot? "lean-toolchain"
  let meta? : Option DagIndexMeta ← readRepoJsonFile? repoRoot? "artifacts/dag/index/meta.json"
  return {
    leanToolchain := leanToolchain?.getD Lean.versionString
    importRoot := meta?.map (·.importRoot) |>.getD "unknown"
    namespaceHint := meta?.map (·.nsFilter) |>.getD (toString doc.meta.mod)
    oleanHash := meta?.map (·.oleanHash) |>.getD ""
    artifactSchema := meta?.map (·.schemaVersion) |>.getD 0
  }

def responseMetaOfDoc (doc : FileWorker.EditableDocument) : IO ResponseMeta := do
  return {
    version := bridgeVersion
    sessionId := sessionIdOfDoc doc
    revision := doc.meta.version
    env := (← envFingerprintOfDoc doc)
  }

def mkCompilerError
    (code : CompilerErrorCode)
    (phase : ErrorPhase)
    (severity : Severity)
    (message : String)
    (file : Option String := none)
    (line : Option Nat := none)
    (column : Option Nat := none) : CompilerError :=
  {
    code := code
    phase := phase
    severity := severity
    message := message
    file := file
    line := line
    column := column
  }

def unsupportedProtocolVersionError (requested : BridgeVersion) (responseMeta : ResponseMeta) :
    CompilerError :=
  mkCompilerError
    .unsupportedProtocolVersion
    .protocol
    .error
    s!"Unsupported bridge version {requested.protocol}/{requested.schema}; expected {responseMeta.version.protocol}/{responseMeta.version.schema}"

def validateVersion (requested : BridgeVersion) (responseMeta : ResponseMeta) :
    Option CompilerError :=
  if requested.isSupported then none
  else some (unsupportedProtocolVersionError requested responseMeta)

def severityOfDiagnostic (severity? : Option Lsp.DiagnosticSeverity) : Severity :=
  match severity? with
  | some .error => .error
  | some .warning => .warning
  | some .information => .info
  | some .hint => .info
  | none => .error

private def readInteractiveDiagnostics (doc : FileWorker.EditableDocument) :
    IO (Array Widget.InteractiveDiagnostic) :=
  doc.diagnosticsRef.get

private def toPlainDiagnostic (diag : Widget.InteractiveDiagnostic) : Lsp.Diagnostic :=
  Widget.InteractiveDiagnostic.toDiagnostic diag

private def classifyDiagnostic (diag : Lsp.Diagnostic) : ErrorPhase × CompilerErrorCode :=
  let msg := diag.message.toLower
  let leanTags := diag.leanTags?.getD #[]
  if leanTags.contains .unsolvedGoals || msg.contains "unsolved goals" then
    (.proofState, .unsolvedGoals)
  else if msg.contains "failed to synthesize" || msg.contains "typeclass instance problem is stuck" then
    (.elaboration, .typeclassSearchFailed)
  else if msg.contains "unknown constant" || msg.contains "unknown identifier" then
    (.elaboration, .unknownConstant)
  else if msg.contains "unexpected token" || msg.contains "expected token" || msg.contains "invalid syntax" then
    (.parse, .parseError)
  else if msg.contains "timeout" then
    (.elaboration, .timeout)
  else
    (.elaboration, .elaborationError)

def compilerErrorOfDiagnostic (uri : Lsp.DocumentUri) (diag : Widget.InteractiveDiagnostic) :
    CompilerError :=
  let plain := toPlainDiagnostic diag
  let (phase, code) := classifyDiagnostic plain
  let range := plain.fullRange?.getD plain.range
  {
    code := code
    phase := phase
    severity := severityOfDiagnostic plain.severity?
    message := plain.message
    file := some (toString uri)
    line := some range.start.line
    column := some range.start.character
  }

def docDiagnostics (doc : FileWorker.EditableDocument) : IO (Array CompilerError) := do
  let diagnostics ← readInteractiveDiagnostics doc
  return diagnostics.map (compilerErrorOfDiagnostic doc.meta.uri)

def diagnosticsOk (diagnostics : Array CompilerError) : Bool :=
  !diagnostics.any (fun diag => diag.severity == .error)

def mkDocError
    (doc : FileWorker.EditableDocument)
    (code : CompilerErrorCode)
    (phase : ErrorPhase)
    (severity : Severity)
    (message : String) : CompilerError :=
  mkCompilerError
    code
    phase
    severity
    message
    (file := some (toString doc.meta.uri))

private def binderKindOfBundle (bundle : Widget.InteractiveHypothesisBundle) : String :=
  if bundle.val?.isSome then
    "let"
  else if bundle.isInstance?.getD false then
    "instance"
  else
    "default"

private def expandHypBundle (bundle : Widget.InteractiveHypothesisBundle) :
    Array LocalDeclView :=
  Id.run do
    let mut locals := #[]
    let count := min bundle.names.size bundle.fvarIds.size
    for i in [:count] do
      locals := locals.push {
        fvarId := toString bundle.fvarIds[i]!.name
        userName := bundle.names[i]!
        binderKind := binderKindOfBundle bundle
        type := bundle.type.stripTags
        value := bundle.val?.map (·.stripTags)
        isLet := bundle.val?.isSome
        isInstance := bundle.isInstance?.getD false
        isImplementationDetail := false
      }
    return locals

private def goalViewOf (responseMeta : ResponseMeta) (goal : Widget.InteractiveGoal) : GoalView :=
  {
    goalId := {
      sessionId := responseMeta.sessionId
      revision := responseMeta.revision
      value := toString goal.mvarId.name
    }
    pretty := toString goal.pretty
    locals := goal.hyps.foldl (fun acc hyp => acc ++ expandHypBundle hyp) #[]
    target := goal.type.stripTags
    targetHead := none
  }

def proofStateTaskAt (doc : FileWorker.EditableDocument) (posLine posCharacter : Nat) :
    RequestM (RequestTask ProofStateView) := do
  let goalParams : Lsp.PlainGoalParams := {
    textDocument := { uri := doc.meta.uri }
    position := { line := posLine, character := posCharacter }
  }
  let goalTask ← FileWorker.getInteractiveGoals goalParams
  RequestM.mapRequestTaskCheap goalTask fun goals? => do
    let responseMeta ← responseMetaOfDoc doc
    let diagnostics ← docDiagnostics doc
    let goals := goals?.map (fun gs => gs.goals.map (goalViewOf responseMeta)) |>.getD #[]
    return {
      responseMeta := responseMeta
      diagnostics := diagnostics
      goals := goals
    }

def finalSnapshotTask (doc : FileWorker.EditableDocument) :
    RequestM (RequestTask Snapshots.Snapshot) := do
  let waitTask := IO.AsyncList.waitAll doc.cmdSnaps
  RequestM.mapTaskCostly waitTask fun (snapsList, term?) => do
    match term? with
    | some err => throw (RequestError.ofIoError err)
    | none =>
        let snaps := snapsList.toArray
        match snaps[snaps.size - 1]? with
        | some snap => pure snap
        | none => throw <| RequestError.ofIoError <| IO.userError "No command snapshots available"

def ppExprAtSnapshot (snap : Snapshots.Snapshot) (e : Expr) : RequestM String := do
  RequestM.runTermElabM snap do
    pure <| toString (← PrettyPrinter.ppExpr e)

def findDeclInfo? (env : Environment) (declName : String) : Option ConstantInfo := do
  let name := declName.toName
  guard (!name.isAnonymous)
  env.find? name

private def isSorryLikeConst (n : Name) : Bool :=
  let s := toString n.eraseMacroScopes
  s.endsWith "sorryAx" || s.endsWith "admitAx"

private def exprHasSorryLikeConst (e : Expr) : Bool :=
  e.hasSorry || e.foldConsts false (fun n acc => acc || isSorryLikeConst n)

def constantHasSorry (ci : ConstantInfo) : Bool :=
  exprHasSorryLikeConst ci.type ||
    match ci.value? (allowOpaque := true) with
    | some val => exprHasSorryLikeConst val
    | none => false

def declarationNotFoundError (declName : String) : CompilerError :=
  mkCompilerError
    .declarationNotFound
    .validation
    .error
    s!"Declaration '{declName}' was not found in the current snapshot."

def containsSorryError (declName : String) : CompilerError :=
  mkCompilerError
    .containsSorry
    .validation
    .error
    s!"Declaration '{declName}' contains `sorry`."

end IG.Compiler
