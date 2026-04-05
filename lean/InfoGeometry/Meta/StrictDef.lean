import Lean
import Lean.Util.Sorry
import InfoGeometry.Meta.ProofShape
import InfoGeometry.Meta.RegionPolicy

open Lean Elab Command Meta Term

namespace InfoGeometry.Meta

structure StrictDeclData where
  levelParams : List Name
  typeExpr : Expr
  valueExpr : Expr

private def forbiddenTermKinds : List SyntaxNodeKind :=
  [ ``Lean.Parser.Term.byTactic
  , ``Lean.Parser.Term.«sorry»
  , ``Lean.Parser.Term.«unsafe»
  ]

private def containsForbiddenTerm (stx : Syntax) : Bool :=
  (stx.find? fun node => forbiddenTermKinds.contains node.getKind).isSome

def validateStrictDeclSyntax
    (declKind : String)
    (declName : Name)
    (typeStx valueStx : Syntax) : CommandElabM Unit := do
  if containsForbiddenTerm typeStx then
    throwErrorAt typeStx
      "strict {declKind} `{declName}` uses forbidden term syntax (`by`, `sorry`, or `unsafe`) in its type."
  if containsForbiddenTerm valueStx then
    throwErrorAt valueStx
      "strict {declKind} `{declName}` uses forbidden term syntax (`by`, `sorry`, or `unsafe`) in its value."

private def ppExprString (e : Expr) : TermElabM String := do
  return toString (← ppExpr e)

private def holeTelemetryJson (mvarId : MVarId) : TermElabM Json := mvarId.withContext do
  let expectedType ← instantiateMVars (← mvarId.getType)
  let expectedTypeStr ← ppExprString expectedType
  let lctx ← getLCtx
  let mut locals : Array Json := #[]
  for localDecl in lctx do
    if !localDecl.isImplementationDetail then
      let localType ← instantiateMVars localDecl.type
      let localTypeStr ← ppExprString localType
      locals := locals.push <| Json.mkObj
        [ ("name", Json.str (toString localDecl.userName))
        , ("type", Json.str localTypeStr)
        ]
  return Json.mkObj
    [ ("holeId", Json.str (toString mvarId.name))
    , ("expectedType", Json.str expectedTypeStr)
    , ("localContext", Json.arr locals)
    ]

private def collectPendingMVars (exprs : Array Expr) : TermElabM (Array MVarId) := do
  let mut seen : Std.HashSet Name := {}
  let mut pending : Array MVarId := #[]
  for expr in exprs do
    for mvarId in (← getMVars expr) do
      if !seen.contains mvarId.name then
        seen := seen.insert mvarId.name
        pending := pending.push mvarId
  pure pending

private def strictTelemetryJsonCore
    (declKind : String)
    (declName : Name)
    (failureKind : String)
    (typeStr valueStr : String)
    (holes : Array Json)
    (hasExprMVar hasLevelMVar hasSorry : Bool)
    (inferredTypeStr? : Option String := none)
    (extras : List (String × Json) := []) : Json :=
  let inferredTypeField :=
    match inferredTypeStr? with
    | some inferredTypeStr => [("inferredType", Json.str inferredTypeStr)]
    | none => []
  Json.mkObj <|
    [ ("declKind", Json.str declKind)
    , ("declName", Json.str (toString declName))
    , ("failureKind", Json.str failureKind)
    , ("expectedType", Json.str typeStr)
    , ("value", Json.str valueStr)
    , ("hasExprMVar", Json.bool hasExprMVar)
    , ("hasLevelMVar", Json.bool hasLevelMVar)
    , ("hasSorry", Json.bool hasSorry)
    , ("holes", Json.arr holes)
    ] ++ inferredTypeField ++ extras

private inductive RawBoundaryProbe where
  | compatible
  | mismatch (report : Json)

private def probeRawBoundary?
    (declKind : String)
    (declName : Name)
    (typeExpr : Expr)
    (valueStx : Syntax) : TermElabM (Option RawBoundaryProbe) :=
  withoutModifyingStateWithInfoAndMessages <| observing? do
    let valueExpr ← Term.withoutErrToSorry <| Term.elabTerm valueStx none false
    let valueExpr ← instantiateMVars valueExpr
    let inferredType ← instantiateMVars (← inferType valueExpr)
    let isCompatible? ← observing? <| isDefEq inferredType typeExpr
    let isCompatible := isCompatible?.getD false
    if isCompatible then
      return .compatible
    let typeStr ← ppExprString typeExpr
    let pending ← collectPendingMVars #[valueExpr, inferredType]
    let valueStr ← ppExprString valueExpr
    let inferredTypeStr ← ppExprString inferredType
    let holes ← pending.mapM holeTelemetryJson
    pure <| .mismatch <| strictTelemetryJsonCore declKind declName "typeMismatch" typeStr valueStr holes
      (typeExpr.hasExprMVar || valueExpr.hasExprMVar)
      (typeExpr.hasLevelMVar || valueExpr.hasLevelMVar)
      (typeExpr.hasSorry || valueExpr.hasSorry)
      (inferredTypeStr? := some inferredTypeStr)

private def strictTelemetryJson
    (declKind : String)
    (declName : Name)
    (failureKind : String)
    (typeExpr valueExpr : Expr)
    (pending : Array MVarId)
    (inferredType? : Option Expr := none) : TermElabM Json := do
  let typeStr ← ppExprString typeExpr
  let valueStr ← ppExprString valueExpr
  let holes ← pending.mapM holeTelemetryJson
  let inferredTypeField ←
    match inferredType? with
    | some inferredType =>
        pure (some (← ppExprString inferredType))
    | none =>
        pure none
  pure <| strictTelemetryJsonCore declKind declName failureKind typeStr valueStr holes
    (typeExpr.hasExprMVar || valueExpr.hasExprMVar)
    (typeExpr.hasLevelMVar || valueExpr.hasLevelMVar)
    (typeExpr.hasSorry || valueExpr.hasSorry)
    inferredTypeField

private def throwStrictTelemetry
    (declKind : String)
    (declName : Name)
    (failureKind : String)
    (typeExpr valueExpr : Expr)
    (pending : Array MVarId)
    (header : String)
    (inferredType? : Option Expr := none) : TermElabM α := do
  let report ← strictTelemetryJson declKind declName failureKind typeExpr valueExpr pending inferredType?
  throwError
    "{header}\n[strict-gap-json] {report.compress}"

private def throwStrictTelemetryReport
    (header : String)
    (report : Json) : TermElabM α :=
  throwError "{header}\n[strict-gap-json] {report.compress}"

private def thinSurfaceTelemetryJson
    (declKind : String)
    (declName : Name)
    (region : AdmissionRegion)
    (data : StrictDeclData)
    (shape : ProofShapeReport) : TermElabM Json := do
  let typeStr ← ppExprString data.typeExpr
  let valueStr ← ppExprString data.valueExpr
  let thinExtras :=
    match shape.thinSurface? with
    | some thinSurface => [("thinSurface", toJson thinSurface)]
    | none => []
  let targetExtras :=
    match shape.proofHead.forwardTarget? with
    | some target => [("forwardTarget", Json.str (toString target))]
    | none => []
  let extras :=
    [ ("region", Json.str region.asString)
    , ("proofShape", toJson shape.proofHead)
    , ("statementShape", toJson shape.statementShape)
    ] ++ thinExtras ++ targetExtras
  pure <| strictTelemetryJsonCore declKind declName "blockedProofShape"
    typeStr valueStr #[] false false false
    (extras := extras)

private def checkProtectedTheoremShape
    (declName : Name)
    (data : StrictDeclData) : CommandElabM Unit := do
  let region := regionOfDecl defaultPolicySnapshot declName
  unless region == .protectedRegion do
    return ()
  let shape := analyzeProofShape data.typeExpr data.valueExpr
  match shape.thinSurface? with
  | none => pure ()
  | some thinSurface =>
      let report ← liftTermElabM <| thinSurfaceTelemetryJson "theorem" declName region data shape
      let thinLabel := thinSurface.asString
      throwError
        "strict theorem `{declName}` is blocked in protected region: thin {thinLabel} surfaces are not admissible.\n[strict-gap-json] {report.compress}"

private def finalizeLevelParams (typeExpr valueExpr : Expr) : TermElabM StrictDeclData := do
  let typeExpr ← Term.levelMVarToParam typeExpr
  let valueExpr ← Term.levelMVarToParam valueExpr
  let typeExpr ← instantiateMVars typeExpr
  let valueExpr ← instantiateMVars valueExpr
  let levelParams := (collectLevelParams (collectLevelParams {} typeExpr) valueExpr).params.toList
  pure { levelParams, typeExpr, valueExpr }

def elabStrictDecl
    (declKind : String)
    (declName : Name)
    (typeStx valueStx : Syntax) : CommandElabM StrictDeclData :=
  liftTermElabM do
    Term.withDeclName declName do
      withoutModifyingEnv do
        let typeExpr ← Term.elabType typeStx
        let valueExpr ←
          try
            Term.withoutErrToSorry <| Term.elabTermEnsuringType valueStx typeExpr
          catch _ =>
            match ← probeRawBoundary? declKind declName typeExpr valueStx with
            | some (.mismatch report) =>
                throwStrictTelemetryReport
                  s!"strict {declKind} `{declName}` failed to elaborate against its declared type."
                  report
            | _ =>
                throwError
                  "strict {declKind} `{declName}` failed to elaborate against its declared type."
        try
          Term.synthesizeSyntheticMVarsNoPostponing
        catch _ =>
          let typeExpr ← instantiateMVars typeExpr
          let valueExpr ← instantiateMVars valueExpr
          let pending ← collectPendingMVars #[valueExpr]
          discard <| Term.logUnassignedUsingErrorInfos pending
          throwStrictTelemetry declKind declName "unresolvedSyntheticObligations" typeExpr valueExpr pending
            s!"strict {declKind} `{declName}` left unresolved synthetic obligations."
        let typeExpr ← instantiateMVars typeExpr
        let valueExpr ← instantiateMVars valueExpr
        let pending ← collectPendingMVars #[typeExpr, valueExpr]
        if !pending.isEmpty then
          discard <| Term.logUnassignedUsingErrorInfos pending
          throwStrictTelemetry declKind declName "unresolvedMetavariables" typeExpr valueExpr pending
            s!"strict {declKind} `{declName}` elaborated to an expression with unresolved metavariables."
        if typeExpr.hasSorry || valueExpr.hasSorry then
          throwStrictTelemetry declKind declName "containsSorryAx" typeExpr valueExpr #[]
            s!"strict {declKind} `{declName}` elaborated to an expression containing `sorryAx`."
        let finalized ← finalizeLevelParams typeExpr valueExpr
        if finalized.typeExpr.hasLevelMVar || finalized.valueExpr.hasLevelMVar then
          throwStrictTelemetry declKind declName "unresolvedUniverseLevels"
            finalized.typeExpr finalized.valueExpr #[]
            s!"strict {declKind} `{declName}` elaborated to an expression with unresolved universe levels."
        pure finalized

def commitStrictDef
    (declName : Name)
    (data : StrictDeclData) : CommandElabM Unit := do
  if (← getEnv).contains declName then
    throwError "declaration `{declName}` has already been declared"
  let decl : Declaration := .defnDecl
    { name := declName
      levelParams := data.levelParams
      type := data.typeExpr
      value := data.valueExpr
      hints := .regular 0
      safety := .safe
    }
  liftCoreM <| addAndCompile decl

def commitStrictTheorem
    (declName : Name)
    (data : StrictDeclData) : CommandElabM Unit := do
  if (← getEnv).contains declName then
    throwError "declaration `{declName}` has already been declared"
  unless ← liftTermElabM <| isProp data.typeExpr do
    throwError "strict theorem `{declName}` does not have a proposition type"
  liftCoreM <| addDecl <| .thmDecl
    { name := declName
      levelParams := data.levelParams
      type := data.typeExpr
      value := data.valueExpr
    }

/--
`#strict_def` is the minimal forward-flow declaration surface.
It accepts only ordinary `def` syntax and rejects tactic blocks, `sorry`, and
`unsafe` terms, validates the elaborated term, and commits that same checked
declaration directly.
-/
elab "#strict_def " declId:ident " : " typeStx:term " := " valueStx:term : command => do
  let declName := (← getCurrNamespace) ++ declId.getId
  validateStrictDeclSyntax "definition" declName typeStx.raw valueStx.raw
  let data ← elabStrictDecl "definition" declName typeStx.raw valueStx.raw
  commitStrictDef declName data

/--
`#strict_theorem` is the theorem analogue of `#strict_def`.
It enforces the same forward-flow syntax gate, validates the elaborated proof,
and commits that same checked theorem directly.
-/
elab "#strict_theorem " declId:ident " : " typeStx:term " := " valueStx:term : command => do
  let declName := (← getCurrNamespace) ++ declId.getId
  validateStrictDeclSyntax "theorem" declName typeStx.raw valueStx.raw
  let data ← elabStrictDecl "theorem" declName typeStx.raw valueStx.raw
  checkProtectedTheoremShape declName data
  commitStrictTheorem declName data

end InfoGeometry.Meta
