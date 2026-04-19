import Lean

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

structure NodeRow where
  schema : String
  nodeKey : String
  rootKey : String
  parentKey? : Option String
  preorder : Nat
  kind : String
  payloadKey? : Option String
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
  leakage : Array LeakageRow := #[]
  nextNode : Nat := 0

abbrev ExportM := StateRefT ExportState IO

def schema : String := "info_geometry.raw_infotree_export.v1"

def mkKey (tag : String) (parts : Array String) : String :=
  tag ++ "_" ++ String.intercalate "_" parts.toList

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
  stx.reprint.getD ""

def constNamesOfExpr (e : Expr) : Array String :=
  let names : NameSet :=
    e.foldConsts (init := ({} : NameSet)) fun n acc => acc.insert n
  (names.toList.map Name.toString).toArray

def optionExprText (e? : Option Expr) : String :=
  match e? with
  | some e => toString e
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
      let directText := importNamesText directImports
      let allText := moduleNamesText allImports
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
        directImportsText? := some directText
        directImportsHash? := some (stableHash directText)
        allImportedModuleCount? := some allImports.size
        allImportedModulesText? := some allText
        allImportedModulesHash? := some (stableHash allText) }
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
    (mctxRefKey : String)
    (mctx : MetavarContext) : Array MctxDeclRow := Id.run do
  let mut rows := #[]
  for (mvarId, decl) in mctx.decls.toList do
    let assignment? := mctx.eAssignment.find? mvarId
    let assignmentText? := assignment?.map toString
    let delayed? := mctx.dAssignment.find? mvarId
    let delayedPending? := delayed?.map fun delayed => mvarIdText delayed.mvarIdPending
    let delayedFVarCount? := delayed?.map fun delayed => delayed.fvars.size
    let typeText := toString decl.type
    rows := rows.push
      { schema := schema
        rootKey := rootKey
        module := moduleName
        file := fileName
        declKey := mkKey "itmd" #[mctxRefKey, sanitize (mvarIdText mvarId)]
        mctxRefKey := mctxRefKey
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
          openDeclsText? := some (String.intercalate "\n" (info.openDecls.map toString))
          parentDecl? := none
          autoImplicitCount? := none
          autoImplicitText? := none
          fileSource? := some info.fileMap.source
          filePositionCount? := some info.fileMap.positions.size
          filePositionsText? := some (fileMapPositionsText info.fileMap)
          optionsCount? := some (optionsRows info.options).size
          optionsText? := some (optionsText info.options)
          optionsHasTrace? := some info.options.hasTrace
          nameGeneratorPrefix? := some info.ngen.namePrefix.toString
          nameGeneratorIndex? := some info.ngen.idx }
      , #[ ("command_context_env", "CommandContextInfo environment is not serialized in stage 1")
         , ("command_context_cmd_env", "CommandContextInfo final command environment is not serialized in stage 1")
         , ("command_context_mctx", "Metavariable context is counted but not serialized structurally in stage 1") ] )
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
      , #[] )

def optionNameText (name? : Option Name) : String :=
  match name? with
  | some name => name.toString
  | none => ""

def optionNameDecls (name? : Option Name) : Array String :=
  match name? with
  | some name => #[name.toString]
  | none => #[]

def completionPayload
    (info : CompletionInfo) : Array (String × String) × Array String :=
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
      (fields, constNamesOfExpr termInfo.expr ++ constNamesOfOptionExpr termInfo.expectedType? ++ constNamesOfOptionExpr expectedType?)
  | .id stx id danglingDot lctx expectedType? =>
      let fields :=
        #[ ("completionKind", "id")
         , ("syntax", syntaxText stx)
         , ("id", id.toString)
         , ("danglingDot", toString danglingDot)
         , ("expectedType", optionExprText expectedType?)
         , ("lctx_size", toString lctx.decls.size) ]
      (fields, constNamesOfOptionExpr expectedType?)
  | .dotId stx id lctx expectedType? =>
      let fields :=
        #[ ("completionKind", "dotId")
         , ("syntax", syntaxText stx)
         , ("id", id.toString)
         , ("expectedType", optionExprText expectedType?)
         , ("lctx_size", toString lctx.decls.size) ]
      (fields, constNamesOfOptionExpr expectedType?)
  | .fieldId stx id? lctx structName =>
      let fields :=
        #[ ("completionKind", "fieldId")
         , ("syntax", syntaxText stx)
         , ("id", optionNameText id?)
         , ("structName", structName.toString)
         , ("lctx_size", toString lctx.decls.size) ]
      (fields, #[structName.toString] ++ optionNameDecls id?)
  | .namespaceId stx =>
      (#[("completionKind", "namespaceId"), ("syntax", syntaxText stx)], #[])
  | .option stx =>
      (#[("completionKind", "option"), ("syntax", syntaxText stx)], #[])
  | .errorName stx partialId =>
      (#[("completionKind", "errorName"), ("syntax", syntaxText stx), ("partialId", syntaxText partialId)], #[])
  | .endSection stx id? danglingDot scopeNames =>
      let fields :=
        #[ ("completionKind", "endSection")
         , ("syntax", syntaxText stx)
         , ("id", optionNameText id?)
         , ("danglingDot", toString danglingDot)
         , ("scopeNames", String.intercalate "\n" scopeNames) ]
      (fields, optionNameDecls id?)
  | .tactic stx =>
      (#[("completionKind", "tactic"), ("syntax", syntaxText stx)], #[])

def infoKindAndPayload
    (info : Elab.Info) :
    String × Option String × Array (String × String) × Array (String × String) × Array String :=
  match info with
  | .ofTermInfo ti =>
      let fields :=
        #[ ("expr", toString ti.expr)
         , ("expectedType", optionExprText ti.expectedType?)
         , ("elaborator", ti.elaborator.toString)
         , ("syntax", syntaxText ti.stx)
         , ("isBinder", toString ti.isBinder)
         , ("isDisplayableTerm", toString ti.isDisplayableTerm)
         , ("lctx_size", toString ti.lctx.decls.size) ]
      ("term", some (payloadText fields), fields, #[], constNamesOfExpr ti.expr ++ constNamesOfOptionExpr ti.expectedType?)
  | .ofPartialTermInfo ti =>
      let fields :=
        #[ ("expectedType", optionExprText ti.expectedType?)
         , ("elaborator", ti.elaborator.toString)
         , ("syntax", syntaxText ti.stx)
         , ("lctx_size", toString ti.lctx.decls.size) ]
      ("partial_term", some (payloadText fields), fields, #[("partial_term_expr", "PartialTermInfo has no complete expression payload")], constNamesOfOptionExpr ti.expectedType?)
  | .ofCommandInfo ci =>
      let fields := #[("elaborator", ci.elaborator.toString), ("syntax", syntaxText ci.stx)]
      ("command", some (payloadText fields), fields, #[], #[])
  | .ofTacticInfo ti =>
      let fields :=
        #[ ("elaborator", ti.elaborator.toString)
         , ("syntax", syntaxText ti.stx)
         , ("goalsBefore", toString ti.goalsBefore.length)
         , ("goalsAfter", toString ti.goalsAfter.length) ]
      ("tactic", some (payloadText fields), fields, #[("tactic_mctx", "Full tactic metavariable context entries are not serialized in stage 1")], #[])
  | .ofMacroExpansionInfo mi =>
      let fields :=
        #[ ("syntax", syntaxText mi.stx)
         , ("output", syntaxText mi.output)
         , ("lctx_size", toString mi.lctx.decls.size) ]
      ("macro_expansion", some (payloadText fields), fields, #[], #[])
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
         , ("value", toString fi.val)
         , ("syntax", syntaxText fi.stx)
         , ("lctx_size", toString fi.lctx.decls.size) ]
      ("field", some (payloadText fields), fields, #[], (#[fi.projName.toString] ++ constNamesOfExpr fi.val))
  | .ofCompletionInfo ci =>
      let (fields, decls) := completionPayload ci
      ("completion", some (payloadText fields), fields, #[], decls)
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
      ("field_redecl", some (payloadText fields), fields, #[], #[])
  | .ofDelabTermInfo ti =>
      let fields :=
        #[ ("expr", toString ti.expr)
         , ("expectedType", optionExprText ti.expectedType?)
         , ("elaborator", ti.elaborator.toString)
         , ("syntax", syntaxText ti.stx) ]
      ("delab_term", some (payloadText fields), fields, #[], constNamesOfExpr ti.expr ++ constNamesOfOptionExpr ti.expectedType?)
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
          payloadKey? := none }
      let contextKey := mkKey "itc" #[rootKey, toString preorder]
      let (contextRow, contextLeakages) :=
        contextRowAndLeakage rootKey moduleName fileName nodeKey contextKey ctx
      let contextEnvRefs : Array EnvRefRow :=
        match ctx with
        | .commandCtx info =>
            #[ envRefRow rootKey moduleName fileName nodeKey (mkKey "iter" #[rootKey, toString preorder, "env"]) "env" (some info.env)
             , envRefRow rootKey moduleName fileName nodeKey (mkKey "iter" #[rootKey, toString preorder, "cmdEnv"]) "cmdEnv" info.cmdEnv? ]
        | _ => #[]
      let contextMctxRefs : Array MctxRefRow :=
        match ctx with
        | .commandCtx info =>
            #[mctxRefRow rootKey moduleName fileName nodeKey (mkKey "itmr" #[rootKey, toString preorder]) info.mctx]
        | _ => #[]
      let contextMctxDecls : Array MctxDeclRow :=
        match ctx with
        | .commandCtx info =>
            mctxDeclRows rootKey moduleName fileName nodeKey (mkKey "itmr" #[rootKey, toString preorder]) info.mctx
        | _ => #[]
      modify fun s =>
        { s with
          nodes := s.nodes.push row
          contexts := s.contexts.push contextRow
          envRefs := s.envRefs ++ contextEnvRefs
          mctxRefs := s.mctxRefs ++ contextMctxRefs
          mctxDecls := s.mctxDecls ++ contextMctxDecls }
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
          payloadKey? := payloadKey? }
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
      | _, _ => pure ()
      for decl in decls do
        let linkKey := mkKey "itdl" #[rootKey, toString preorder, sanitize decl]
        let linkRow : DeclLinkRow :=
          { schema := schema
            rootKey := rootKey
            module := moduleName
            file := fileName
            linkKey := linkKey
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
  | .hole _ =>
      let row : NodeRow :=
        { schema := schema
          nodeKey := nodeKey
          rootKey := rootKey
          parentKey? := parent?
          preorder := preorder
          kind := "hole"
          payloadKey? := none }
      let leakageRow : LeakageRow :=
        { schema := schema
          rootKey := rootKey
          nodeKey? := some nodeKey
          field := "hole"
          reason := "InfoTree hole is preserved as a node without payload in stage 0" }
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

partial def runCommands (hook : FrontendM Unit) : FrontendM Unit := do
  let done ← Frontend.processCommand
  hook
  unless done do
    runCommands hook

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
  let cmdState0 := Command.mkState env0 msgs opts
  let initSt : Frontend.State :=
    { commandState := cmdState0
      parserState := parserState
      cmdPos := parserState.pos
      commands := #[] }
  let ctx : Frontend.Context := { inputCtx := inputCtx }
  let rootsRef : IO.Ref (Array RootRow) ← IO.mkRef #[]
  let exportRef : IO.Ref ExportState ← IO.mkRef {}
  let treesRef : IO.Ref Nat ← IO.mkRef 0
  let commandRef : IO.Ref Nat ← IO.mkRef 0
  let moduleName := env0.mainModule.toString
  let fileName := file.toString

  let hook : FrontendM Unit := do
    let st ← get
    let trees := st.commandState.infoState.trees
    let prev ← treesRef.get
    let now := trees.size
    treesRef.set now
    let commandIndex ← commandRef.get
    commandRef.set (commandIndex + 1)
    for i in [prev:now] do
      let rootKey := mkKey "itr" #[sanitize moduleName, toString commandIndex, toString i]
      rootsRef.modify fun rows => rows.push
        { schema := schema
          rootKey := rootKey
          module := moduleName
          file := fileName
          commandIndex := commandIndex
          treeIndex := i }
      let state ← exportRef.get
      let (_, state') ← (walk moduleName fileName rootKey none 0 trees[i]!).run state
      exportRef.set state'

  let (_u, _stFinal) ← ((runCommands hook).run ctx).run initSt
  let roots ← rootsRef.get
  let exported ← exportRef.get
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
  let metadata : Json := Json.mkObj
    [ ("schema", toJson schema)
    , ("stage", toJson "stage_1_context_decllink_probe")
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
