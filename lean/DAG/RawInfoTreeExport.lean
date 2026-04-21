import Lean
import Std.Data.HashSet
import Std.Data.TreeMap.Basic

open Lean
open Lean.Parser
open Lean.Elab
open Lean.Elab.Frontend

namespace DAG.RawInfoTreeExport

structure RootRow where
  schema : String
  rootKey : String
  module : String
  file : String
  commandIndex : Nat
  treeIndex : Nat
deriving ToJson

structure ContextRow where
  schema : String
  rootKey : String
  module : String
  file : String
  contextKey : String
  nodeKey : String
  contextKind : String
  lctx_size? : Option Nat
  mctx_size? : Option Nat
  mctx_depth? : Option Nat
  currNamespace? : Option String
  openDeclCount? : Option Nat
  openDeclsText? : Option String
  parentDecl? : Option String
  autoImplicitCount? : Option Nat
  autoImplicitText? : Option String
  fileSource? : Option String
  filePositionCount? : Option Nat
  filePositionsText? : Option String
  optionsCount? : Option Nat
  optionsText? : Option String
  optionsHasTrace? : Option Bool
  nameGeneratorPrefix? : Option String
  nameGeneratorIndex? : Option Nat
deriving ToJson

structure DeclLinkRow where
  schema : String
  rootKey : String
  module : String
  file : String
  linkKey : String
  nodeKey : String
  declName : String
deriving ToJson

structure EnvRefRow where
  schema : String
  rootKey : String
  module : String
  file : String
  envRefKey : String
  nodeKey : String
  role : String
  present : Bool
  mainModule? : Option String
  directImportCount? : Option Nat
  directImportsText? : Option String
  directImportsHash? : Option Nat
  allImportedModuleCount? : Option Nat
  allImportedModulesText? : Option String
  allImportedModulesHash? : Option Nat
deriving ToJson

structure MctxRefRow where
  schema : String
  rootKey : String
  module : String
  file : String
  mctxRefKey : String
  mctxKey : String
  nodeKey : String
  depth : Nat
  levelAssignDepth : Nat
  mvarCounter : Nat
  declCount : Nat
  levelDepthCount : Nat
  userNameCount : Nat
  levelAssignmentCount : Nat
  exprAssignmentCount : Nat
  delayedAssignmentCount : Nat
  declIdsText : String
  declIdsHash : Nat
  userNamesText : String
  userNamesHash : Nat
deriving ToJson

structure MctxDeclRow where
  schema : String
  rootKey : String
  module : String
  file : String
  declKey : String
  mctxRefKey : String
  mctxKey : String
  nodeKey : String
  mvarId : String
  userName : String
  kind : String
  depth : Nat
  index : Nat
  numScopeArgs : Nat
  lctxSize : Nat
  localInstanceCount : Nat
  typeText : String
  typeHash : Nat
  assigned : Bool
  assignmentText? : Option String
  assignmentHash? : Option Nat
  delayedAssigned : Bool
  delayedPendingMVar? : Option String
  delayedFVarCount? : Option Nat
deriving ToJson

structure LctxDeclRow where
  schema : String
  rootKey : String
  module : String
  file : String
  lctxDeclKey : String
  nodeKey : String
  sourceKind : String
  sourceKey : String
  fvarId : String
  userName : String
  localDeclKind : String
  index : Nat
  binderInfo? : Option String
  isLet : Bool
  nondep? : Option Bool
  auxFullName? : Option String
  typeText : String
  typeHash : Nat
  valueText? : Option String
  valueHash? : Option Nat
deriving ToJson

structure LctxRefRow where
  schema : String
  rootKey : String
  module : String
  file : String
  lctxRefKey : String
  nodeKey : String
  sourceKind : String
  sourceKey : String
  lctxKey : String
  lctxSize : Nat
deriving ToJson

structure NodeRow where
  schema : String
  nodeKey : String
  rootKey : String
  parentKey? : Option String
  preorder : Nat
  kind : String
  payloadKey? : Option String
  holeMVarId? : Option String
deriving ToJson

structure EdgeRow where
  schema : String
  edgeKey : String
  rootKey : String
  parentKey : String
  childKey : String
  siblingIndex : Nat
deriving ToJson

structure PayloadRow where
  schema : String
  rootKey : String
  module : String
  file : String
  payloadKey : String
  nodeKey : String
  kind : String
  text : String
deriving ToJson

structure PayloadFieldRow where
  schema : String
  rootKey : String
  module : String
  file : String
  fieldKey : String
  payloadKey : String
  nodeKey : String
  field : String
  value : String
deriving ToJson

structure LeakageRow where
  schema : String
  rootKey : String
  nodeKey? : Option String
  field : String
  reason : String
deriving ToJson

structure ExportState where
  nodes : Array NodeRow := #[]
  edges : Array EdgeRow := #[]
  payloads : Array PayloadRow := #[]
  payloadFields : Array PayloadFieldRow := #[]
  contexts : Array ContextRow := #[]
  declLinks : Array DeclLinkRow := #[]
  envRefs : Array EnvRefRow := #[]
  mctxRefs : Array MctxRefRow := #[]
  mctxDecls : Array MctxDeclRow := #[]
  lctxDecls : Array LctxDeclRow := #[]
  lctxRefs : Array LctxRefRow := #[]
  leakage : Array LeakageRow := #[]
  nextNode : Nat := 0
  nextLctxRef : Nat := 0
  emittedMctxKeys : Std.HashSet String := {}
  emittedLctxKeys : Std.HashSet String := {}

abbrev ExportM := StateRefT ExportState IO

def schema : String := "info_geometry.raw_infotree_export.v1"
def stage : String := "stage_2_tactic_lctx_bridge"

def mkKey (tag : String) (parts : Array String) : String :=
  tag ++ "_" ++ String.intercalate "_" parts.toList

def pushAll (xs : Array α) (ys : Array α) : Array α :=
  ys.foldl (fun acc row => acc.push row) xs

def sanitize (s : String) : String :=
  s.map fun c =>
    if c.isAlphanum then c else '_'

def writeJsonl {α : Type} [ToJson α] (path : System.FilePath) (rows : Array α) : IO Unit := do
  let parent? := path.parent
  match parent? with
  | some parent => IO.FS.createDirAll parent
  | none => pure ()
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  for row in rows do
    h.putStrLn (toJson row).compress

def syntaxText (stx : Syntax) : String :=
  "syntax_kind=" ++ stx.getKind.toString

def exprProjection (e : Expr) : String :=
  "expr_hash=" ++ toString (hash e)

def constNamesOfExpr (_e : Expr) : Array String :=
  #[] -- Full Expr traversal belongs to the dedicated Expr DAG exporter, not this scaffold.

def optionExprText (e? : Option Expr) : String :=
  match e? with
  | some e => exprProjection e
  | none => ""

def constNamesOfOptionExpr (e? : Option Expr) : Array String :=
  match e? with
  | some e => constNamesOfExpr e
  | none => #[]

def payloadText (fields : Array (String × String)) : String :=
  String.intercalate "\n" (fields.toList.map fun (key, value) => key ++ "=" ++ value)

def fileMapPositionsText (fileMap : FileMap) : String :=
  String.intercalate "\n" (fileMap.positions.toList.map toString)

def optionsRows (options : Options) : Array (String × String) := Id.run do
  let mut rows := #[]
  for (name, value) in options do
    rows := rows.push (name.toString, toString value)
  return rows

def optionsText (options : Options) : String :=
  payloadText (optionsRows options)

def importNamesText (imports : Array Import) : String :=
  String.intercalate "\n" (imports.toList.map fun imp => imp.module.toString)

def moduleNamesText (names : Array Name) : String :=
  String.intercalate "\n" (names.toList.map Name.toString)

def stableHash (text : String) : Nat :=
  let modulus := 18446744073709551616
  text.foldl (fun acc c => (acc * 16777619 + c.toNat) % modulus) 2166136261

def mvarIdText (id : MVarId) : String :=
  toString id.name

def fvarIdText (id : FVarId) : String :=
  toString id.name

def envRefRow
    (rootKey : String)
    (moduleName : String)
    (fileName : String)
    (nodeKey : String)
    (envRefKey : String)
    (role : String)
    (env? : Option Environment) : EnvRefRow :=
  match env? with
  | some env =>
      let directImports := env.imports
      let allImports := env.allImportedModuleNames
      { schema := schema
        rootKey := rootKey
        module := moduleName
        file := fileName
        envRefKey := envRefKey
        nodeKey := nodeKey
        role := role
        present := true
        mainModule? := some env.mainModule.toString
        directImportCount? := some directImports.size
        directImportsText? := none
        directImportsHash? := none
        allImportedModuleCount? := some allImports.size
        allImportedModulesText? := none
        allImportedModulesHash? := none }
  | none =>
      { schema := schema
        rootKey := rootKey
        module := moduleName
        file := fileName
        envRefKey := envRefKey
        nodeKey := nodeKey
        role := role
        present := false
        mainModule? := none
        directImportCount? := none
        directImportsText? := none
        directImportsHash? := none
        allImportedModuleCount? := none
        allImportedModulesText? := none
        allImportedModulesHash? := none }

def mctxRefRow
    (rootKey : String)
    (moduleName : String)
    (fileName : String)
    (nodeKey : String)
    (mctxRefKey : String)
    (mctxKey : String)
    (mctx : MetavarContext) : MctxRefRow :=
  let decls := mctx.decls.toList
  let userNames := mctx.userNames.toList
  let declIdsText := String.intercalate "\n" (decls.map fun (id, _decl) => toString id.name)
  let userNamesText := String.intercalate "\n" (userNames.map fun (name, id) => name.toString ++ "=" ++ toString id.name)
  { schema := schema
    rootKey := rootKey
    module := moduleName
    file := fileName
    mctxRefKey := mctxRefKey
    mctxKey := mctxKey
    nodeKey := nodeKey
    depth := mctx.depth
    levelAssignDepth := mctx.levelAssignDepth
    mvarCounter := mctx.mvarCounter
    declCount := decls.length
    levelDepthCount := mctx.lDepth.toList.length
    userNameCount := userNames.length
    levelAssignmentCount := mctx.lAssignment.toList.length
    exprAssignmentCount := mctx.eAssignment.toList.length
    delayedAssignmentCount := mctx.dAssignment.toList.length
    declIdsText := declIdsText
    declIdsHash := stableHash declIdsText
    userNamesText := userNamesText
    userNamesHash := stableHash userNamesText }

def mctxDeclRows
    (rootKey : String)
    (moduleName : String)
    (fileName : String)
    (nodeKey : String)
    (mctxKey : String)
    (mctx : MetavarContext) : Array MctxDeclRow := Id.run do
  let mut rows := #[]
  for (mvarId, decl) in mctx.decls.toList do
    let assignment? := mctx.eAssignment.find? mvarId
    let assignmentText? := assignment?.map exprProjection
    let delayed? := mctx.dAssignment.find? mvarId
    let delayedPending? := delayed?.map fun delayed => mvarIdText delayed.mvarIdPending
    let delayedFVarCount? := delayed?.map fun delayed => delayed.fvars.size
    let typeText := exprProjection decl.type
    rows := rows.push
      { schema := schema
        rootKey := rootKey
        module := moduleName
        file := fileName
        declKey := mkKey "itmd" #[mctxKey, sanitize (mvarIdText mvarId)]
        mctxRefKey := mctxKey
        mctxKey := mctxKey
        nodeKey := nodeKey
        mvarId := mvarIdText mvarId
        userName := decl.userName.toString
        kind := reprStr decl.kind
        depth := decl.depth
        index := decl.index
        numScopeArgs := decl.numScopeArgs
        lctxSize := decl.lctx.size
        localInstanceCount := decl.localInstances.size
        typeText := typeText
        typeHash := stableHash typeText
        assigned := assignment?.isSome
        assignmentText? := assignmentText?
        assignmentHash? := assignmentText?.map stableHash
        delayedAssigned := delayed?.isSome
        delayedPendingMVar? := delayedPending?
        delayedFVarCount? := delayedFVarCount? }
  return rows

def mctxSignature (mctx : MetavarContext) : String := Id.run do
  let declIds :=
    mctx.decls.toList.map fun (id, decl) =>
      String.intercalate "|"
        [ mvarIdText id
        , decl.userName.toString
        , reprStr decl.kind
        , toString decl.depth
        , toString decl.index
        , toString decl.numScopeArgs
        , toString decl.lctx.size
        , toString decl.localInstances.size ]
  let userNames :=
    mctx.userNames.toList.map fun (name, id) =>
      name.toString ++ "=" ++ mvarIdText id
  let assignments :=
    mctx.eAssignment.toList.map fun (id, expr) =>
      mvarIdText id ++ "=" ++ toString (hash expr)
  let delayed :=
    mctx.dAssignment.toList.map fun (id, delayed) =>
      String.intercalate "|"
        [ mvarIdText id
        , mvarIdText delayed.mvarIdPending
        , toString delayed.fvars.size ]
  String.intercalate "\n"
    ( [ "depth=" ++ toString mctx.depth
      , "levelAssignDepth=" ++ toString mctx.levelAssignDepth
      , "mvarCounter=" ++ toString mctx.mvarCounter
      , "lDepth=" ++ toString mctx.lDepth.toList.length
      , "lAssignment=" ++ toString mctx.lAssignment.toList.length
      , "decls=" ++ String.intercalate ";" declIds
      , "userNames=" ++ String.intercalate ";" userNames
      , "assignments=" ++ String.intercalate ";" assignments
      , "delayed=" ++ String.intercalate ";" delayed
      ] )

def emitMctxRefAndDecls
    (rootKey : String)
    (moduleName : String)
    (fileName : String)
    (nodeKey : String)
    (mctxRefKey : String)
    (mctx : MetavarContext) : ExportM String := do
  let mctxKey := mkKey "itmc" #[rootKey, toString (stableHash (mctxSignature mctx))]
  let refRow := mctxRefRow rootKey moduleName fileName nodeKey mctxRefKey mctxKey mctx
  modify fun s => { s with mctxRefs := s.mctxRefs.push refRow }
  let st ← get
  if st.emittedMctxKeys.contains mctxKey then
    pure mctxKey
  else
    let rows := mctxDeclRows rootKey moduleName fileName nodeKey mctxKey mctx
    modify fun s =>
      { s with
        mctxDecls := pushAll s.mctxDecls rows
        emittedMctxKeys := s.emittedMctxKeys.insert mctxKey }
    pure mctxKey

def lctxDeclRows
    (rootKey : String)
    (moduleName : String)
    (fileName : String)
    (nodeKey : String)
    (sourceKind : String)
    (sourceKey : String)
    (lctx : LocalContext) : Array LctxDeclRow := Id.run do
  let mut rows := #[]
  for decl in lctx do
    let typeText := exprProjection decl.type
    let value? : Option Expr :=
      match decl with
      | .cdecl .. => none
      | .ldecl (value := value) .. => some value
    let valueText? := value?.map exprProjection
    let nondep? : Option Bool :=
      match decl with
      | .cdecl .. => none
      | .ldecl (nondep := nondep) .. => some nondep
    let binderInfo? : Option String :=
      match decl with
      | .cdecl (bi := bi) .. => some (reprStr bi)
      | .ldecl .. => none
    let auxFullName? := lctx.auxDeclToFullName.get? decl.fvarId |>.map Name.toString
    rows := rows.push
      { schema := schema
        rootKey := rootKey
        module := moduleName
        file := fileName
        lctxDeclKey := mkKey "itld" #[sourceKey, toString decl.index, sanitize (fvarIdText decl.fvarId)]
        nodeKey := nodeKey
        sourceKind := sourceKind
        sourceKey := sourceKey
        fvarId := fvarIdText decl.fvarId
        userName := decl.userName.toString
        localDeclKind := reprStr decl.kind
        index := decl.index
        binderInfo? := binderInfo?
        isLet := decl.isLet (allowNondep := true)
        nondep? := nondep?
        auxFullName? := auxFullName?
        typeText := typeText
        typeHash := stableHash typeText
        valueText? := valueText?
        valueHash? := valueText?.map stableHash }
  return rows

def lctxSignature (lctx : LocalContext) : String := Id.run do
  let mut parts := #[]
  for decl in lctx do
    parts := parts.push <|
      String.intercalate "|"
        [ toString decl.index
        , fvarIdText decl.fvarId
        , decl.userName.toString
        , reprStr decl.kind
        , toString (decl.isLet (allowNondep := true)) ]
  return String.intercalate "\n" parts.toList

def emitLctxRef
    (rootKey : String)
    (moduleName : String)
    (fileName : String)
    (nodeKey : String)
    (sourceKind : String)
    (sourceKey : String)
    (lctx : LocalContext) : ExportM Unit := do
  let lctxKey := mkKey "itlc" #[rootKey, toString (stableHash (lctxSignature lctx))]
  let st0 ← get
  let lctxRefKey := mkKey "itlr" #[toString (stableHash rootKey), toString st0.nextLctxRef]
  let refRow : LctxRefRow :=
    { schema := schema
      rootKey := rootKey
      module := moduleName
      file := fileName
      lctxRefKey := lctxRefKey
      nodeKey := nodeKey
      sourceKind := sourceKind
      sourceKey := sourceKey
      lctxKey := lctxKey
      lctxSize := lctx.size }
  modify fun s => { s with lctxRefs := s.lctxRefs.push refRow, nextLctxRef := s.nextLctxRef + 1 }
  let st ← get
  if st.emittedLctxKeys.contains lctxKey then
    pure ()
  else
    let rows := lctxDeclRows rootKey moduleName fileName nodeKey "lctx_context" lctxKey lctx
    modify fun s =>
      { s with
        lctxDecls := pushAll s.lctxDecls rows
        emittedLctxKeys := s.emittedLctxKeys.insert lctxKey }

def emitMctxDeclLctxRefs
    (rootKey : String)
    (moduleName : String)
    (fileName : String)
    (nodeKey : String)
    (mctxKey : String)
    (mctx : MetavarContext) : ExportM Unit := do
  for (mvarId, decl) in mctx.decls.toList do
    let declKey := mkKey "itmd" #[mctxKey, sanitize (mvarIdText mvarId)]
    emitLctxRef rootKey moduleName fileName nodeKey "mctx_decl" declKey decl.lctx

def exprGraphLeakage (field : String) : String × String :=
  (field, "Expression is exported only as text/decl links; the full Lean Expr graph is not serialized in stage 1")

def lctxLeakage (field : String) : String × String :=
  (field, "LocalContext declaration rows are exported, but type/value expressions are text/hash projections and the full Lean LocalContext object graph is not serialized")

def syntaxLeakage (field : String) : String × String :=
  (field, "Syntax is exported only by reprinted text; SourceInfo and full syntax tree structure are not serialized in stage 1")

def termInfoLeakage (tag : String) : Array (String × String) :=
  #[ lctxLeakage (tag ++ "_lctx")
   , exprGraphLeakage (tag ++ "_expr_graph")
   , exprGraphLeakage (tag ++ "_expected_type_expr_graph")
   , syntaxLeakage (tag ++ "_syntax_object") ]

def contextRowAndLeakage
    (rootKey : String)
    (moduleName : String)
    (fileName : String)
    (nodeKey : String)
    (contextKey : String)
    (ctx : PartialContextInfo) : ContextRow × Array (String × String) :=
  match ctx with
  | .commandCtx info =>
      ( { schema := schema
          rootKey := rootKey
          module := moduleName
          file := fileName
          contextKey := contextKey
          nodeKey := nodeKey
          contextKind := "commandCtx"
          lctx_size? := none
          mctx_size? := some info.mctx.decls.toList.length
          mctx_depth? := some info.mctx.depth
          currNamespace? := some info.currNamespace.toString
          openDeclCount? := some info.openDecls.length
          openDeclsText? := none
          parentDecl? := none
          autoImplicitCount? := none
          autoImplicitText? := none
          fileSource? := none
          filePositionCount? := some info.fileMap.positions.size
          filePositionsText? := none
          optionsCount? := some (optionsRows info.options).size
          optionsText? := none
          optionsHasTrace? := some info.options.hasTrace
          nameGeneratorPrefix? := some info.ngen.namePrefix.toString
          nameGeneratorIndex? := some info.ngen.idx }
      , #[ ("command_context_env", "CommandContextInfo environment is not serialized in stage 1")
         , ("command_context_cmd_env", "CommandContextInfo final command environment is not serialized in stage 1")
         , ("command_context_mctx", "Metavariable context has reference/decl tables, but full expression/local-context structure is not serialized in stage 1")
         , ("command_context_open_decls_structure", "Open declarations are exported as text/count only, not as structured OpenDecl values in stage 1")
         , ("command_context_options_structure", "Options are exported as text/count/trace summary only, not as typed OptionValue entries in stage 1") ] )
  | .parentDeclCtx parentDecl =>
      ( { schema := schema
          rootKey := rootKey
          module := moduleName
          file := fileName
          contextKey := contextKey
          nodeKey := nodeKey
          contextKind := "parentDeclCtx"
          lctx_size? := none
          mctx_size? := none
          mctx_depth? := none
          currNamespace? := none
          openDeclCount? := none
          openDeclsText? := none
          parentDecl? := some parentDecl.toString
          autoImplicitCount? := none
          autoImplicitText? := none
          fileSource? := none
          filePositionCount? := none
          filePositionsText? := none
          optionsCount? := none
          optionsText? := none
          optionsHasTrace? := none
          nameGeneratorPrefix? := none
          nameGeneratorIndex? := none }
      , #[] )
  | .autoImplicitCtx autoImplicits =>
      ( { schema := schema
          rootKey := rootKey
          module := moduleName
          file := fileName
          contextKey := contextKey
          nodeKey := nodeKey
          contextKind := "autoImplicitCtx"
          lctx_size? := none
          mctx_size? := none
          mctx_depth? := none
          currNamespace? := none
          openDeclCount? := none
          openDeclsText? := none
          parentDecl? := none
          autoImplicitCount? := some autoImplicits.size
          autoImplicitText? := some (String.intercalate "\n" (autoImplicits.toList.map toString))
          fileSource? := none
          filePositionCount? := none
          filePositionsText? := none
          optionsCount? := none
          optionsText? := none
          optionsHasTrace? := none
          nameGeneratorPrefix? := none
          nameGeneratorIndex? := none }
      , #[exprGraphLeakage "auto_implicit_expr_graph"] )

def optionNameText (name? : Option Name) : String :=
  match name? with
  | some name => name.toString
  | none => ""

def optionNameDecls (name? : Option Name) : Array String :=
  match name? with
  | some name => #[name.toString]
  | none => #[]

def completionPayload
    (info : CompletionInfo) : Array (String × String) × Array String × Array (String × String) :=
  match info with
  | .dot termInfo expectedType? =>
      let fields :=
        #[ ("completionKind", "dot")
         , ("syntax", syntaxText termInfo.stx)
         , ("expr", toString termInfo.expr)
         , ("termExpectedType", optionExprText termInfo.expectedType?)
         , ("expectedType", optionExprText expectedType?)
         , ("elaborator", termInfo.elaborator.toString)
         , ("lctx_size", toString termInfo.lctx.decls.size) ]
      (fields,
        constNamesOfExpr termInfo.expr ++ constNamesOfOptionExpr termInfo.expectedType? ++ constNamesOfOptionExpr expectedType?,
        termInfoLeakage "completion_dot_term" ++ #[exprGraphLeakage "completion_dot_expected_type_expr_graph"])
  | .id stx id danglingDot lctx expectedType? =>
      let fields :=
        #[ ("completionKind", "id")
         , ("syntax", syntaxText stx)
         , ("id", id.toString)
         , ("danglingDot", toString danglingDot)
         , ("expectedType", optionExprText expectedType?)
         , ("lctx_size", toString lctx.decls.size) ]
      (fields, constNamesOfOptionExpr expectedType?,
        #[syntaxLeakage "completion_id_syntax_object", lctxLeakage "completion_id_lctx", exprGraphLeakage "completion_id_expected_type_expr_graph"])
  | .dotId stx id lctx expectedType? =>
      let fields :=
        #[ ("completionKind", "dotId")
         , ("syntax", syntaxText stx)
         , ("id", id.toString)
         , ("expectedType", optionExprText expectedType?)
         , ("lctx_size", toString lctx.decls.size) ]
      (fields, constNamesOfOptionExpr expectedType?,
        #[syntaxLeakage "completion_dot_id_syntax_object", lctxLeakage "completion_dot_id_lctx", exprGraphLeakage "completion_dot_id_expected_type_expr_graph"])
  | .fieldId stx id? lctx structName =>
      let fields :=
        #[ ("completionKind", "fieldId")
         , ("syntax", syntaxText stx)
         , ("id", optionNameText id?)
         , ("structName", structName.toString)
         , ("lctx_size", toString lctx.decls.size) ]
      (fields, #[structName.toString] ++ optionNameDecls id?,
        #[syntaxLeakage "completion_field_id_syntax_object", lctxLeakage "completion_field_id_lctx"])
  | .namespaceId stx =>
      (#[("completionKind", "namespaceId"), ("syntax", syntaxText stx)], #[],
        #[syntaxLeakage "completion_namespace_id_syntax_object"])
  | .option stx =>
      (#[("completionKind", "option"), ("syntax", syntaxText stx)], #[],
        #[syntaxLeakage "completion_option_syntax_object"])
  | .errorName stx partialId =>
      (#[("completionKind", "errorName"), ("syntax", syntaxText stx), ("partialId", syntaxText partialId)], #[],
        #[syntaxLeakage "completion_error_name_syntax_object", syntaxLeakage "completion_error_name_partial_id_syntax_object"])
  | .endSection stx id? danglingDot scopeNames =>
      let fields :=
        #[ ("completionKind", "endSection")
         , ("syntax", syntaxText stx)
         , ("id", optionNameText id?)
         , ("danglingDot", toString danglingDot)
         , ("scopeNames", String.intercalate "\n" scopeNames) ]
      (fields, optionNameDecls id?, #[syntaxLeakage "completion_end_section_syntax_object"])
  | .tactic stx =>
      (#[("completionKind", "tactic"), ("syntax", syntaxText stx)], #[],
        #[syntaxLeakage "completion_tactic_syntax_object"])

def emitCompletionLctxRefs
    (rootKey : String)
    (moduleName : String)
    (fileName : String)
    (nodeKey : String)
    (payloadKey : String)
    (info : CompletionInfo) : ExportM Unit := do
  match info with
  | .dot termInfo _ =>
      emitLctxRef rootKey moduleName fileName nodeKey "completion_dot_term" (mkKey "itlcs" #[payloadKey, "dotTerm"]) termInfo.lctx
  | .id _ _ _ lctx _ =>
      emitLctxRef rootKey moduleName fileName nodeKey "completion_id" (mkKey "itlcs" #[payloadKey, "id"]) lctx
  | .dotId _ _ lctx _ =>
      emitLctxRef rootKey moduleName fileName nodeKey "completion_dot_id" (mkKey "itlcs" #[payloadKey, "dotId"]) lctx
  | .fieldId _ _ lctx _ =>
      emitLctxRef rootKey moduleName fileName nodeKey "completion_field_id" (mkKey "itlcs" #[payloadKey, "fieldId"]) lctx
  | .namespaceId .. | .option .. | .errorName .. | .endSection .. | .tactic .. => pure ()

def emitInfoLctxRefs
    (rootKey : String)
    (moduleName : String)
    (fileName : String)
    (nodeKey : String)
    (payloadKey : String)
    (info : Elab.Info) : ExportM Unit := do
  match info with
  | .ofTermInfo ti =>
      emitLctxRef rootKey moduleName fileName nodeKey "term" (mkKey "itlcs" #[payloadKey, "term"]) ti.lctx
  | .ofPartialTermInfo ti =>
      emitLctxRef rootKey moduleName fileName nodeKey "partial_term" (mkKey "itlcs" #[payloadKey, "partialTerm"]) ti.lctx
  | .ofMacroExpansionInfo mi =>
      emitLctxRef rootKey moduleName fileName nodeKey "macro_expansion" (mkKey "itlcs" #[payloadKey, "macroExpansion"]) mi.lctx
  | .ofFieldInfo fi =>
      emitLctxRef rootKey moduleName fileName nodeKey "field" (mkKey "itlcs" #[payloadKey, "field"]) fi.lctx
  | .ofCompletionInfo ci =>
      emitCompletionLctxRefs rootKey moduleName fileName nodeKey payloadKey ci
  | .ofDelabTermInfo ti =>
      emitLctxRef rootKey moduleName fileName nodeKey "delab_term" (mkKey "itlcs" #[payloadKey, "delabTerm"]) ti.lctx
  | _ => pure ()

def emitInfoMctxRefsAndDecls
    (rootKey : String)
    (moduleName : String)
    (fileName : String)
    (nodeKey : String)
    (payloadKey : String)
    (info : Elab.Info) : ExportM Unit := do
  match info with
  | .ofTacticInfo ti =>
      discard <| emitMctxRefAndDecls rootKey moduleName fileName nodeKey (mkKey "itmr" #[payloadKey, "tacticBefore"]) ti.mctxBefore
      discard <| emitMctxRefAndDecls rootKey moduleName fileName nodeKey (mkKey "itmr" #[payloadKey, "tacticAfter"]) ti.mctxAfter
  | _ => pure ()

def emitInfoMctxLctxRefs
    (rootKey : String)
    (moduleName : String)
    (fileName : String)
    (nodeKey : String)
    (payloadKey : String)
    (info : Elab.Info) : ExportM Unit := do
  match info with
  | .ofTacticInfo ti =>
      let beforeKey ← emitMctxRefAndDecls rootKey moduleName fileName nodeKey (mkKey "itmr" #[payloadKey, "tacticBefore"]) ti.mctxBefore
      let afterKey ← emitMctxRefAndDecls rootKey moduleName fileName nodeKey (mkKey "itmr" #[payloadKey, "tacticAfter"]) ti.mctxAfter
      emitMctxDeclLctxRefs rootKey moduleName fileName nodeKey beforeKey ti.mctxBefore
      emitMctxDeclLctxRefs rootKey moduleName fileName nodeKey afterKey ti.mctxAfter
  | _ => pure ()

def infoKindAndPayload
    (info : Elab.Info) :
    String × Option String × Array (String × String) × Array (String × String) × Array String :=
  match info with
  | .ofTermInfo ti =>
      let fields :=
        #[ ("expr", exprProjection ti.expr)
         , ("expectedType", optionExprText ti.expectedType?)
         , ("elaborator", ti.elaborator.toString)
         , ("syntax", syntaxText ti.stx)
         , ("isBinder", toString ti.isBinder)
         , ("isDisplayableTerm", toString ti.isDisplayableTerm)
         , ("lctx_size", toString ti.lctx.decls.size) ]
      ("term", some (payloadText fields), fields, termInfoLeakage "term", constNamesOfExpr ti.expr ++ constNamesOfOptionExpr ti.expectedType?)
  | .ofPartialTermInfo ti =>
      let fields :=
        #[ ("expectedType", optionExprText ti.expectedType?)
         , ("elaborator", ti.elaborator.toString)
         , ("syntax", syntaxText ti.stx)
         , ("lctx_size", toString ti.lctx.decls.size) ]
      ("partial_term", some (payloadText fields), fields,
        #[ lctxLeakage "partial_term_lctx"
         , exprGraphLeakage "partial_term_expected_type_expr_graph"
         , syntaxLeakage "partial_term_syntax_object" ],
        constNamesOfOptionExpr ti.expectedType?)
  | .ofCommandInfo ci =>
      let fields := #[("elaborator", ci.elaborator.toString), ("syntax", syntaxText ci.stx)]
      ("command", some (payloadText fields), fields, #[syntaxLeakage "command_syntax_object"], #[])
  | .ofTacticInfo ti =>
      let fields :=
        #[ ("elaborator", ti.elaborator.toString)
         , ("syntax", syntaxText ti.stx)
         , ("goalsBefore", toString ti.goalsBefore.length)
         , ("goalsAfter", toString ti.goalsAfter.length)
         , ("goalsBeforeIds", String.intercalate "\n" (ti.goalsBefore.map mvarIdText))
         , ("goalsAfterIds", String.intercalate "\n" (ti.goalsAfter.map mvarIdText)) ]
      ("tactic", some (payloadText fields), fields,
        #[ syntaxLeakage "tactic_syntax_object"
         , ("tactic_mctx_before", "TacticInfo.mctxBefore has ref/decl/local-context tables, but full expression graph and assignment closure are not serialized")
         , ("tactic_mctx_after", "TacticInfo.mctxAfter has ref/decl/local-context tables, but full expression graph and assignment closure are not serialized") ], #[])
  | .ofMacroExpansionInfo mi =>
      let fields :=
        #[ ("syntax", syntaxText mi.stx)
         , ("output", syntaxText mi.output)
         , ("lctx_size", toString mi.lctx.decls.size) ]
      ("macro_expansion", some (payloadText fields), fields,
        #[ lctxLeakage "macro_expansion_lctx"
         , syntaxLeakage "macro_expansion_input_syntax_object"
         , syntaxLeakage "macro_expansion_output_syntax_object" ], #[])
  | .ofOptionInfo oi =>
      let fields := #[("optionName", oi.optionName.toString), ("declName", oi.declName.toString), ("syntax", syntaxText oi.stx)]
      ("option", some (payloadText fields), fields, #[], #[oi.declName.toString])
  | .ofErrorNameInfo ei =>
      let fields := #[("errorName", ei.errorName.toString), ("syntax", syntaxText ei.stx)]
      ("error_name", some (payloadText fields), fields, #[], #[ei.errorName.toString])
  | .ofFieldInfo fi =>
      let fields :=
        #[ ("projName", fi.projName.toString)
         , ("fieldName", fi.fieldName.toString)
         , ("value", exprProjection fi.val)
         , ("syntax", syntaxText fi.stx)
         , ("lctx_size", toString fi.lctx.decls.size) ]
      ("field", some (payloadText fields), fields,
        #[ lctxLeakage "field_lctx"
         , exprGraphLeakage "field_value_expr_graph"
         , syntaxLeakage "field_syntax_object" ],
        (#[fi.projName.toString] ++ constNamesOfExpr fi.val))
  | .ofCompletionInfo ci =>
      let (fields, decls, leakages) := completionPayload ci
      ("completion", some (payloadText fields), fields, leakages, decls)
  | .ofUserWidgetInfo wi =>
      let fields := #[("syntax", syntaxText wi.stx)]
      ("user_widget", some (payloadText fields), fields, #[("user_widget_payload", "Widget instance payload is not serialized in stage 1")], #[])
  | .ofCustomInfo ci =>
      let fields := #[("syntax", syntaxText ci.stx)]
      ("custom", some (payloadText fields), fields, #[("custom_dynamic_value", "Dynamic custom value is not serialized in stage 1")], #[])
  | .ofFVarAliasInfo ai =>
      let fields :=
        #[ ("userName", ai.userName.toString)
         , ("id", toString ai.id.name)
         , ("baseId", toString ai.baseId.name) ]
      ("fvar_alias", some (payloadText fields), fields, #[], #[])
  | .ofFieldRedeclInfo fri =>
      let fields := #[("syntax", syntaxText fri.stx)]
      ("field_redecl", some (payloadText fields), fields, #[syntaxLeakage "field_redecl_syntax_object"], #[])
  | .ofDelabTermInfo ti =>
      let fields :=
        #[ ("expr", exprProjection ti.expr)
         , ("expectedType", optionExprText ti.expectedType?)
         , ("elaborator", ti.elaborator.toString)
         , ("syntax", syntaxText ti.stx)
         , ("location", reprStr ti.location?)
         , ("docString", ti.docString?.getD "")
         , ("explicit", toString ti.explicit)
         , ("lctx_size", toString ti.lctx.decls.size) ]
      ("delab_term", some (payloadText fields), fields,
        termInfoLeakage "delab_term" ++
          #[("delab_term_location_structure", "DeclarationLocation is exported with repr text, not as a structured range/module table in stage 1")],
        constNamesOfExpr ti.expr ++ constNamesOfOptionExpr ti.expectedType?)
  | .ofChoiceInfo ci =>
      let fields := #[("elaborator", ci.elaborator.toString), ("syntax", syntaxText ci.stx)]
      ("choice", some (payloadText fields), fields,
        #[("choice_failures", "ChoiceInfo failed alternatives are represented by child InfoTrees, not serialized as a separate payload in stage 1")], #[])
  | .ofDocInfo di =>
      let fields := #[("elaborator", di.elaborator.toString), ("syntax", syntaxText di.stx)]
      ("doc", some (payloadText fields), fields, #[], #[])
  | .ofDocElabInfo di =>
      let fields :=
        #[ ("name", di.name.toString)
         , ("kind", reprStr di.kind)
         , ("elaborator", di.elaborator.toString)
         , ("syntax", syntaxText di.stx) ]
      ("doc_elab", some (payloadText fields), fields, #[], #[di.name.toString])

partial def walk
    (moduleName : String)
    (fileName : String)
    (rootKey : String)
    (parent? : Option String)
    (siblingIndex : Nat)
    (tree : InfoTree) : ExportM String := do
  let st ← get
  let preorder := st.nextNode
  modify fun s => { s with nextNode := s.nextNode + 1 }
  let nodeKey := mkKey "itn" #[rootKey, toString preorder]
  match tree with
  | .context ctx inner =>
      let row : NodeRow :=
        { schema := schema
          nodeKey := nodeKey
          rootKey := rootKey
          parentKey? := parent?
          preorder := preorder
          kind := "context"
          payloadKey? := none
          holeMVarId? := none }
      let contextKey := mkKey "itc" #[rootKey, toString preorder]
      let (contextRow, contextLeakages) :=
        contextRowAndLeakage rootKey moduleName fileName nodeKey contextKey ctx
      let contextEnvRefs : Array EnvRefRow :=
        match ctx with
        | .commandCtx info =>
            #[ envRefRow rootKey moduleName fileName nodeKey (mkKey "iter" #[rootKey, toString preorder, "env"]) "env" (some info.env)
             , envRefRow rootKey moduleName fileName nodeKey (mkKey "iter" #[rootKey, toString preorder, "cmdEnv"]) "cmdEnv" info.cmdEnv? ]
        | _ => #[]
      modify fun s =>
        { s with
          nodes := s.nodes.push row
          contexts := s.contexts.push contextRow
          envRefs := pushAll s.envRefs contextEnvRefs }
      match ctx with
      | .commandCtx info =>
          let mctxKey ← emitMctxRefAndDecls rootKey moduleName fileName nodeKey (mkKey "itmr" #[rootKey, toString preorder]) info.mctx
          emitMctxDeclLctxRefs rootKey moduleName fileName nodeKey mctxKey info.mctx
      | _ => pure ()
      for (field, reason) in contextLeakages do
        let leakageRow : LeakageRow :=
          { schema := schema
            rootKey := rootKey
            nodeKey? := some nodeKey
            field := field
            reason := reason }
        modify fun s => { s with leakage := s.leakage.push leakageRow }
      if let some parentKey := parent? then
        let edgeRow : EdgeRow :=
          { schema := schema
            edgeKey := mkKey "ite" #[parentKey, nodeKey, toString siblingIndex]
            rootKey := rootKey
            parentKey := parentKey
            childKey := nodeKey
            siblingIndex := siblingIndex }
        modify fun s => { s with edges := s.edges.push edgeRow }
      discard <| walk moduleName fileName rootKey (some nodeKey) 0 inner
      pure nodeKey
  | .node info children =>
      let (kind, payload?, payloadFields, leakages, decls) := infoKindAndPayload info
      let payloadKey? := payload?.map fun _ => mkKey "itp" #[rootKey, toString preorder]
      let row : NodeRow :=
        { schema := schema
          nodeKey := nodeKey
          rootKey := rootKey
          parentKey? := parent?
          preorder := preorder
          kind := kind
          payloadKey? := payloadKey?
          holeMVarId? := none }
      modify fun s => { s with nodes := s.nodes.push row }
      if let some parentKey := parent? then
        let edgeRow : EdgeRow :=
          { schema := schema
            edgeKey := mkKey "ite" #[parentKey, nodeKey, toString siblingIndex]
            rootKey := rootKey
            parentKey := parentKey
            childKey := nodeKey
            siblingIndex := siblingIndex }
        modify fun s => { s with edges := s.edges.push edgeRow }
      match payload?, payloadKey? with
      | some text, some payloadKey =>
          let payloadRow : PayloadRow :=
            { schema := schema
              rootKey := rootKey
              module := moduleName
              file := fileName
              payloadKey := payloadKey
              nodeKey := nodeKey
              kind := kind
              text := text }
          modify fun s => { s with payloads := s.payloads.push payloadRow }
          for i in [:payloadFields.size] do
            let (field, value) := payloadFields[i]!
            let fieldRow : PayloadFieldRow :=
              { schema := schema
                rootKey := rootKey
                module := moduleName
                file := fileName
                fieldKey := mkKey "itpf" #[payloadKey, toString i, sanitize field]
                payloadKey := payloadKey
                nodeKey := nodeKey
                field := field
                value := value }
            modify fun s => { s with payloadFields := s.payloadFields.push fieldRow }
          emitInfoLctxRefs rootKey moduleName fileName nodeKey payloadKey info
          emitInfoMctxLctxRefs rootKey moduleName fileName nodeKey payloadKey info
      | _, _ => pure ()
      for i in [:decls.size] do
        let decl := decls[i]!
        let linkRow : DeclLinkRow :=
          { schema := schema
            rootKey := rootKey
            module := moduleName
            file := fileName
            linkKey := mkKey "itdl" #[rootKey, toString preorder, toString i, sanitize decl]
            nodeKey := nodeKey
            declName := decl }
        modify fun s => { s with declLinks := s.declLinks.push linkRow }
      for (field, reason) in leakages do
        let leakageRow : LeakageRow :=
          { schema := schema
            rootKey := rootKey
            nodeKey? := some nodeKey
            field := field
            reason := reason }
        modify fun s => { s with leakage := s.leakage.push leakageRow }
      for i in [:children.size] do
        discard <| walk moduleName fileName rootKey (some nodeKey) i children[i]!
      pure nodeKey
  | .hole mvarId =>
      let row : NodeRow :=
        { schema := schema
          nodeKey := nodeKey
          rootKey := rootKey
          parentKey? := parent?
          preorder := preorder
          kind := "hole"
          payloadKey? := none
          holeMVarId? := some (mvarIdText mvarId) }
      let leakageRow : LeakageRow :=
        { schema := schema
          rootKey := rootKey
          nodeKey? := some nodeKey
          field := "hole_assignment"
          reason := "InfoTree hole MVarId is serialized, but InfoState assignment/lazyAssignment closure is not serialized in stage 1" }
      modify fun s =>
        { s with
          nodes := s.nodes.push row
          leakage := s.leakage.push leakageRow }
      if let some parentKey := parent? then
        let edgeRow : EdgeRow :=
          { schema := schema
            edgeKey := mkKey "ite" #[parentKey, nodeKey, toString siblingIndex]
            rootKey := rootKey
            parentKey := parentKey
            childKey := nodeKey
            siblingIndex := siblingIndex }
        modify fun s => { s with edges := s.edges.push edgeRow }
      pure nodeKey

def exportFile (file : System.FilePath) (outDir : System.FilePath) : IO UInt32 := do
  if !(← file.pathExists) then
    IO.eprintln s!"RawInfoTreeExport: file not found: {file}"
    return 2
  Lean.initSearchPath (← Lean.findSysroot)
  let opts := Elab.async.setIfNotSet ({} : Options) false
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file.toString
  let (headerStx, parserState, msgs) ← Parser.parseHeader inputCtx
  let (env0, msgs) ← Elab.processHeader headerStx opts msgs inputCtx 0
  if msgs.hasErrors then
    for msg in msgs.toList do
      if msg.severity == .error then
        IO.eprintln s!"RawInfoTreeExport: header error: {← msg.toString}"
    return 3
  let moduleName ← moduleNameOfFileName file none
  let env0 := env0.setMainModule moduleName
  let commandState0 := { Command.mkState env0 msgs opts with infoState.enabled := true }
  let frontendState ← IO.processCommands inputCtx parserState commandState0
  let moduleName := moduleName.toString
  let fileName := file.toString
  let fileKey := toString (stableHash fileName)
  let trees := frontendState.commandState.infoState.trees.toArray
  let mut roots : Array RootRow := #[]
  let mut exported : ExportState := {}
  for i in [:trees.size] do
    let rootKey := mkKey "itr" #[sanitize moduleName, fileKey, toString i]
    roots := roots.push
      { schema := schema
        rootKey := rootKey
        module := moduleName
        file := fileName
        commandIndex := i
        treeIndex := i }
    let (_, exported') ← (walk moduleName fileName rootKey none 0 trees[i]!).run exported
    exported := exported'
  writeJsonl (outDir / "raw_infotree_roots.jsonl") roots
  writeJsonl (outDir / "raw_infotree_nodes.jsonl") exported.nodes
  writeJsonl (outDir / "raw_infotree_edges.jsonl") exported.edges
  writeJsonl (outDir / "raw_infotree_payloads.jsonl") exported.payloads
  writeJsonl (outDir / "raw_infotree_payload_fields.jsonl") exported.payloadFields
  writeJsonl (outDir / "raw_infotree_projection_leakage.jsonl") exported.leakage
  writeJsonl (outDir / "raw_infotree_contexts.jsonl") exported.contexts
  writeJsonl (outDir / "raw_infotree_decl_links.jsonl") exported.declLinks
  writeJsonl (outDir / "raw_infotree_env_refs.jsonl") exported.envRefs
  writeJsonl (outDir / "raw_infotree_mctx_refs.jsonl") exported.mctxRefs
  writeJsonl (outDir / "raw_infotree_mctx_decls.jsonl") exported.mctxDecls
  writeJsonl (outDir / "raw_infotree_lctx_refs.jsonl") exported.lctxRefs
  writeJsonl (outDir / "raw_infotree_lctx_decls.jsonl") exported.lctxDecls
  let metadata : Json := Json.mkObj
    [ ("schema", toJson schema)
    , ("stage", toJson stage)
    , ("file", toJson fileName)
    , ("module", toJson moduleName)
    , ("root_count", toJson roots.size)
    , ("node_count", toJson exported.nodes.size)
    , ("edge_count", toJson exported.edges.size)
    , ("payload_count", toJson exported.payloads.size)
    , ("payload_field_count", toJson exported.payloadFields.size)
    , ("context_count", toJson exported.contexts.size)
    , ("decl_link_count", toJson exported.declLinks.size)
    , ("env_ref_count", toJson exported.envRefs.size)
    , ("mctx_ref_count", toJson exported.mctxRefs.size)
    , ("mctx_decl_count", toJson exported.mctxDecls.size)
    , ("lctx_ref_count", toJson exported.lctxRefs.size)
    , ("lctx_decl_count", toJson exported.lctxDecls.size)
    , ("leakage_count", toJson exported.leakage.size)
    , ("fully_lossless", toJson false)
    , ("loss_audited", toJson true)
    ]
  IO.FS.writeFile (outDir / "metadata.json") (metadata.pretty ++ "\n")
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [file, outDir] => exportFile (System.FilePath.mk file) (System.FilePath.mk outDir)
  | _ =>
      IO.eprintln "usage: RawInfoTreeExport <lean-file> <output-dir>"
      return 1

end DAG.RawInfoTreeExport

def main (args : List String) : IO UInt32 :=
  DAG.RawInfoTreeExport.main args
