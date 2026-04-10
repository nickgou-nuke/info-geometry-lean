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
    (classificationProvenance : ErrorClassificationProvenance := .bridgeRule)
    (file : Option String := none)
    (line : Option Nat := none)
    (column : Option Nat := none) : CompilerError :=
  {
    code := code
    phase := phase
    severity := severity
    message := message
    classificationProvenance := classificationProvenance
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

private def isHeadNoise (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\t' || c == '(' || c == '{' || c == '['

private def isHeadBoundary (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\t' || c == ',' || c == ':' ||
  c == ')' || c == ']' || c == '}' || c == '=' || c == ';'

private def headTokenOfText? (text : String) : Option String :=
  let normalized := (text.replace "\n" " ").trimAscii.toString
  if normalized.isEmpty then
    none
  else
    let chars := normalized.toList.dropWhile isHeadNoise
    let headChars := chars.takeWhile (fun c => !isHeadBoundary c)
    let token := String.ofList headChars
    if token.isEmpty then none else some token

private def exprHeadMetaOfText (text : String) : Option String × ExprHeadSource :=
  match headTokenOfText? text with
  | some head => (some head, .textHeuristic)
  | none => (none, .unavailable)

private def exprKindOfTextHead (head : String) : String :=
  if head == "∀" then
    "forallE"
  else if head == "fun" then
    "lam"
  else if head == "let" then
    "letE"
  else if head == "Sort" || head == "Prop" then
    "sort"
  else
    "unknown"

private partial def exprKindOfExpr : Expr → String
  | .mdata _ b => exprKindOfExpr b
  | .forallE .. => "forallE"
  | .lam .. => "lam"
  | .letE .. => "letE"
  | .app .. => "app"
  | .const .. => "const"
  | .fvar .. => "fvar"
  | .mvar .. => "mvar"
  | .sort .. => "sort"
  | .lit .. => "lit"
  | .proj .. => "proj"
  | _ => "other"

private partial def binderDepthOfExpr : Expr → Nat
  | .mdata _ b => binderDepthOfExpr b
  | .forallE _ _ body _ => binderDepthOfExpr body + 1
  | .lam _ _ body _ => binderDepthOfExpr body + 1
  | .letE _ _ _ body _ => binderDepthOfExpr body + 1
  | _ => 0

private partial def unfoldAppCore (e : Expr) (args : List Expr) : Expr × List Expr :=
  match e with
  | .mdata _ b => unfoldAppCore b args
  | .app f a => unfoldAppCore f (a :: args)
  | _ => (e, args)

private def unfoldApp (e : Expr) : Expr × Array Expr :=
  let (fn, args) := unfoldAppCore e []
  (fn, args.toArray)

private def appArityOfExpr (e : Expr) : Nat :=
  (unfoldApp e).2.size

private structure HeadMeta where
  head : Option String := none
  source : ExprHeadSource := .unavailable
  fingerprint : Option String := none
  exprFingerprint : Option ExprFingerprintView := none
deriving Inhabited

private def mkHeadMetaOfText (text : String) : HeadMeta :=
  let (head, source) := exprHeadMetaOfText text
  let exprFingerprint :=
    match headTokenOfText? text with
    | none =>
        none
    | some textHead =>
        let exprKind := exprKindOfTextHead textHead
        let argHeadFingerprints : Array String := #[]
        let fp := s!"expr/v1/k={exprKind};h={textHead};b=0;a=0;args="
        some {
          exprKind := exprKind
          semanticHead := some textHead
          binderDepth := 0
          appArity := 0
          argHeadFingerprints := argHeadFingerprints
          fingerprintV1 := some fp
          fingerprintSource := .textHeuristic
        }
  {
    head := head
    source := source
    fingerprint := none
    exprFingerprint := exprFingerprint
  }

def headMetaOfText (text : String) : Option String × ExprHeadSource :=
  exprHeadMetaOfText text

private def headTokenOfExpr? : Expr → Option String
  | .sort .zero => some "Prop"
  | .sort _ => some "Sort"
  | .forallE .. => some "∀"
  | .lam .. => some "fun"
  | .letE .. => some "let"
  | .const n _ => some (toString n.eraseMacroScopes)
  | .fvar _ => some "fvar"
  | .mvar id => some (toString id.name)
  | .proj s _ _ => some (toString s.eraseMacroScopes)
  | .mdata _ b => headTokenOfExpr? b
  | .app f _ => headTokenOfExpr? f
  | _ => none

private def headFingerprintSeedOfExpr? : Expr → Option String
  | .sort .zero => some "head:sort:prop"
  | .sort _ => some "head:sort"
  | .forallE .. => some "head:forall"
  | .lam .. => some "head:lambda"
  | .letE .. => some "head:let"
  | .const n _ => some s!"head:const:{n.eraseMacroScopes}"
  | .fvar _ => some "head:fvar"
  | .mvar _ => some "head:mvar"
  | .proj s i _ => some s!"head:proj:{s.eraseMacroScopes}:{i}"
  | .mdata _ b => headFingerprintSeedOfExpr? b
  | .app f _ => headFingerprintSeedOfExpr? f
  | _ => none

private def headFingerprintOfExpr? (e : Expr) : Option String :=
  headFingerprintSeedOfExpr? e |>.map (fun fp => s!"shape/v1/{fp}")

private def argHeadFingerprintsOfExpr (e : Expr) : Array String :=
  let args := (unfoldApp e).2
  (args.toList.take 2).foldl
    (fun acc arg =>
      match headFingerprintOfExpr? arg with
      | some fp => acc.push fp
      | none => acc)
    #[]

private def mkFingerprintV1
    (exprKind : String)
    (semanticHead : Option String)
    (binderDepth : Nat)
    (appArity : Nat)
    (argHeadFingerprints : Array String) : String :=
  let headPart := semanticHead.getD "_"
  let argsPart := String.intercalate "," argHeadFingerprints.toList
  s!"expr/v1/k={exprKind};h={headPart};b={binderDepth};a={appArity};args={argsPart}"

private def mkExprFingerprintOfText (text : String) : Option ExprFingerprintView :=
  match headTokenOfText? text with
  | none =>
      none
  | some head =>
      let exprKind := exprKindOfTextHead head
      let argHeadFingerprints : Array String := #[]
      let fp := mkFingerprintV1 exprKind (some head) 0 0 argHeadFingerprints
      some {
        exprKind := exprKind
        semanticHead := some head
        binderDepth := 0
        appArity := 0
        argHeadFingerprints := argHeadFingerprints
        fingerprintV1 := some fp
        fingerprintSource := .textHeuristic
      }

private def mkExprFingerprintOfExpr (e : Expr) : ExprFingerprintView :=
  let exprKind := exprKindOfExpr e
  let semanticHead := headTokenOfExpr? e
  let binderDepth := binderDepthOfExpr e
  let appArity := appArityOfExpr e
  let argHeadFingerprints := argHeadFingerprintsOfExpr e
  let source :=
    if exprKind == "other" && semanticHead.isNone then
      ExprHeadSource.unavailable
    else
      ExprHeadSource.exprSemantic
  let fingerprintV1 :=
    if source == .unavailable then
      none
    else
      some (mkFingerprintV1 exprKind semanticHead binderDepth appArity argHeadFingerprints)
  {
    exprKind := exprKind
    semanticHead := semanticHead
    binderDepth := binderDepth
    appArity := appArity
    argHeadFingerprints := argHeadFingerprints
    fingerprintV1 := fingerprintV1
    fingerprintSource := source
  }

def exprFingerprintOfText (text : String) : Option ExprFingerprintView :=
  mkExprFingerprintOfText text

def headFingerprintOfExpr (e : Expr) : Option String :=
  headFingerprintOfExpr? e

def headMetaOfExpr (e : Expr) : Option String × ExprHeadSource :=
  match headTokenOfExpr? e with
  | some head => (some head, .exprSemantic)
  | none => (none, .unavailable)

def exprFingerprintOfExpr (e : Expr) : ExprFingerprintView :=
  mkExprFingerprintOfExpr e

private partial def headTokenOfExprInContext? : Expr → MetaM (Option String)
  | .sort .zero => pure (some "Prop")
  | .sort _ => pure (some "Sort")
  | .forallE .. => pure (some "∀")
  | .lam .. => pure (some "fun")
  | .letE .. => pure (some "let")
  | .const n _ => pure (some (toString n.eraseMacroScopes))
  | .fvar id =>
      return some (toString (← id.getDecl).userName)
  | .mvar id => pure (some (toString id.name))
  | .proj s _ _ => pure (some (toString s.eraseMacroScopes))
  | .mdata _ b => headTokenOfExprInContext? b
  | .app f _ => headTokenOfExprInContext? f
  | _ => pure none

private def exprKindOfExprInContext (e : Expr) : MetaM String := do
  let baseKind := exprKindOfExpr e
  if baseKind != "app" then
    return baseKind
  let fn := (unfoldApp e).1
  match fn with
  | .const fnName _ =>
      let env ← getEnv
      match env.getProjectionFnInfo? fnName with
      | some _ => return "proj"
      | none => return baseKind
  | _ =>
      return baseKind

private def mkExprFingerprintOfExprInContext (e : Expr) : MetaM ExprFingerprintView := do
  let exprKind ← exprKindOfExprInContext e
  let semanticHead ← headTokenOfExprInContext? e
  let binderDepth := binderDepthOfExpr e
  let appArity := appArityOfExpr e
  let argHeadFingerprints := argHeadFingerprintsOfExpr e
  let source :=
    if exprKind == "other" && semanticHead.isNone then
      ExprHeadSource.unavailable
    else
      ExprHeadSource.exprSemantic
  let fingerprintV1 :=
    if source == .unavailable then
      none
    else
      some (mkFingerprintV1 exprKind semanticHead binderDepth appArity argHeadFingerprints)
  return {
    exprKind := exprKind
    semanticHead := semanticHead
    binderDepth := binderDepth
    appArity := appArity
    argHeadFingerprints := argHeadFingerprints
    fingerprintV1 := fingerprintV1
    fingerprintSource := source
  }

private def mkHeadMetaOfExprInContext (e : Expr) : MetaM HeadMeta := do
  let exprFingerprint ← mkExprFingerprintOfExprInContext e
  let head? ← headTokenOfExprInContext? e
  match head? with
  | some head =>
      return {
        head := some head
        source := .exprSemantic
        fingerprint := headFingerprintOfExpr? e
        exprFingerprint := some exprFingerprint
      }
  | none =>
      return {
        head := none
        source := .unavailable
        fingerprint := none
        exprFingerprint := some exprFingerprint
      }

private def mkHeadMetaOfExpr (e : Expr) : HeadMeta :=
  let exprFingerprint := mkExprFingerprintOfExpr e
  let (head, source) := headMetaOfExpr e
  match head with
  | some _ =>
      {
        head := head
        source := source
        fingerprint := headFingerprintOfExpr? e
        exprFingerprint := some exprFingerprint
      }
  | none =>
      {
        head := none
        source := .unavailable
        fingerprint := none
        exprFingerprint := some exprFingerprint
      }

private def semanticTargetHeadMeta? (goal : Widget.InteractiveGoal) : IO (Option HeadMeta) := do
  try
    let headMeta ← goal.ctx.val.runMetaM (default : LocalContext) do
      goal.mvarId.withContext do
        let targetExpr ← Lean.instantiateMVars (← goal.mvarId.getType)
        mkHeadMetaOfExprInContext targetExpr
    return some headMeta
  catch _ =>
    return none

private def semanticLocalHeadMetaMap (goal : Widget.InteractiveGoal) : IO (Std.HashMap String HeadMeta) := do
  try
    goal.ctx.val.runMetaM (default : LocalContext) do
      goal.mvarId.withContext do
        let mut semantic : Std.HashMap String HeadMeta := {}
        for bundle in goal.hyps do
          let count := min bundle.names.size bundle.fvarIds.size
          for i in [:count] do
            let fvarId := bundle.fvarIds[i]!
            let typeExpr ← Lean.instantiateMVars (← fvarId.getType)
            let headMeta ← mkHeadMetaOfExprInContext typeExpr
            semantic := semantic.insert (toString fvarId.name) headMeta
        return semantic
  catch _ =>
    return {}

private def readInteractiveDiagnostics (doc : FileWorker.EditableDocument) :
    IO (Array Widget.InteractiveDiagnostic) :=
  doc.diagnosticsRef.get

private def toPlainDiagnostic (diag : Widget.InteractiveDiagnostic) : Lsp.Diagnostic :=
  Widget.InteractiveDiagnostic.toDiagnostic diag

private def classifyDiagnostic (diag : Lsp.Diagnostic) :
    ErrorPhase × CompilerErrorCode × ErrorClassificationProvenance :=
  let msg := diag.message.toLower
  let leanTags := diag.leanTags?.getD #[]
  if leanTags.contains .unsolvedGoals then
    (.proofState, .unsolvedGoals, .leanTag)
  else if msg.contains "unsolved goals" then
    (.proofState, .unsolvedGoals, .messagePattern)
  else if msg.contains "failed to synthesize" || msg.contains "typeclass instance problem is stuck" then
    (.elaboration, .typeclassSearchFailed, .messagePattern)
  else if msg.contains "unknown constant" || msg.contains "unknown identifier" then
    (.elaboration, .unknownConstant, .messagePattern)
  else if msg.contains "unexpected token" || msg.contains "expected token" || msg.contains "invalid syntax" then
    (.parse, .parseError, .messagePattern)
  else if msg.contains "timeout" then
    (.elaboration, .timeout, .messagePattern)
  else
    (.elaboration, .elaborationError, .fallback)

def compilerErrorOfDiagnostic (uri : Lsp.DocumentUri) (diag : Widget.InteractiveDiagnostic) :
    CompilerError :=
  let plain := toPlainDiagnostic diag
  let (phase, code, classificationProvenance) := classifyDiagnostic plain
  let range := plain.fullRange?.getD plain.range
  {
    code := code
    phase := phase
    severity := severityOfDiagnostic plain.severity?
    message := plain.message
    classificationProvenance := classificationProvenance
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

private def expandHypBundle (bundle : Widget.InteractiveHypothesisBundle)
    (semantic : Std.HashMap String HeadMeta) :
    Array LocalDeclView :=
  Id.run do
    let mut locals := #[]
    let count := min bundle.names.size bundle.fvarIds.size
    for i in [:count] do
      let localType := bundle.type.stripTags
      let fvarId := toString bundle.fvarIds[i]!.name
      let fallbackMeta := mkHeadMetaOfText localType
      let selectedMeta :=
        match semantic.get? fvarId with
        | some semanticMeta =>
            match semanticMeta.head with
            | some _ => semanticMeta
            | none => fallbackMeta
        | none => fallbackMeta
      locals := locals.push {
        fvarId := fvarId
        userName := bundle.names[i]!
        binderKind := binderKindOfBundle bundle
        type := localType
        typeHead := selectedMeta.head
        typeHeadSource := selectedMeta.source
        typeHeadFingerprint := selectedMeta.fingerprint
        typeExprFingerprint := selectedMeta.exprFingerprint
        value := bundle.val?.map (·.stripTags)
        isLet := bundle.val?.isSome
        isInstance := bundle.isInstance?.getD false
        isImplementationDetail := false
      }
    return locals

private def goalViewOf (responseMeta : ResponseMeta) (goal : Widget.InteractiveGoal) :
    RequestM GoalView := do
  let target := goal.type.stripTags
  let fallbackTargetMeta := mkHeadMetaOfText target
  let semanticTarget? ← semanticTargetHeadMeta? goal
  let targetMeta :=
    match semanticTarget? with
    | some semanticTarget =>
        match semanticTarget.head with
        | some _ => semanticTarget
        | none => fallbackTargetMeta
    | none => fallbackTargetMeta
  let semanticLocalMeta ← semanticLocalHeadMetaMap goal
  return {
    goalId := {
      sessionId := responseMeta.sessionId
      revision := responseMeta.revision
      value := toString goal.mvarId.name
    }
    pretty := toString goal.pretty
    locals := goal.hyps.foldl (fun acc hyp => acc ++ expandHypBundle hyp semanticLocalMeta) #[]
    target := target
    targetHead := targetMeta.head
    targetHeadSource := targetMeta.source
    targetHeadFingerprint := targetMeta.fingerprint
    targetExprFingerprint := targetMeta.exprFingerprint
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
    let goals ←
      match goals? with
      | some gs => gs.goals.mapM (goalViewOf responseMeta)
      | none => pure #[]
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

def snapshotTaskAt (doc : FileWorker.EditableDocument) (posLine posCharacter : Nat) :
    RequestM (RequestTask Snapshots.Snapshot) := do
  let pos : Lsp.Position := { line := posLine, character := posCharacter }
  let utf8Pos := doc.meta.text.lspPosToUtf8Pos pos
  withWaitFindSnap doc (fun snap => snap.endPos >= utf8Pos)
    (notFoundX := throw ⟨.invalidParams, s!"no snapshot found at {pos}"⟩)
    (x := fun snap => pure snap)

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
