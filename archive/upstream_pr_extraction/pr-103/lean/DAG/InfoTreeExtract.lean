import Lean
import Lean.Data.Json

open Lean
open Lean.Parser
open Lean.Elab
open Lean.Elab.Frontend
open Lean.Meta

namespace DAG
namespace InfoTreeExtract

structure PosJson where
  line : Nat
  column : Nat
  deriving ToJson

structure RangeJson where
  start : PosJson
  endPos : PosJson
  deriving ToJson

structure LocalContextSlot where
  slot : String
  rawFVarId : String
  name : String
  typeAst : String
  valueAst : String
  deriving ToJson

structure TacticTransitionRecord where
  schema : String
  kind : String
  module : String
  parentDecl : String
  currentNamespace : String
  range : RangeJson
  source : String
  goalsBefore : Array String
  goalsAfter : Array String
  constRefs : Array String
  localContext : Array LocalContextSlot
  deriving ToJson

structure DeclRecord where
  schema : String
  kind : String
  module : String
  name : String
  parentDecl : String
  declKind : String
  typeAst : String
  valueAst : String
  constRefs : Array String
  isSorrySourceScan : Bool
  deriving ToJson

def schemaVersion : String := "infogeom.infotojson.v0"

def trim (s : String) : String := (String.trimAscii s).toString

def moduleNameFromFile (fp : System.FilePath) : Name :=
  Id.run do
    let s0 : String := fp.toString
    let s1 : String :=
      if s0.endsWith ".lean" then
        (s0.dropEnd (".lean".length)).toString
      else
        s0
    let s2 : String :=
      if s1.startsWith "./" then
        (s1.drop 2).toString
      else if s1.startsWith "lean/" then
        (s1.drop 5).toString
      else
        s1
    let parts := (s2.split (fun c => c = '/')).toList
    let mut nameAccum : Name := Name.anonymous
    for p in parts do
      let part : String := p.toString
      if part ≠ "" then
        nameAccum := nameAccum.append <| Name.mkSimple part
    return nameAccum

def positionFromPos (p : String.Pos.Raw) (fm : FileMap) : PosJson :=
  let pos := fm.toPosition p
  { line := pos.line, column := pos.column }

def rangeFromSyntax (stx : Syntax) (fm : FileMap) : RangeJson :=
  match stx.getPos?, stx.getTailPos? with
  | some s, some e =>
      { start := positionFromPos s fm
        endPos := positionFromPos e fm }
  | some s, none =>
      let p := positionFromPos s fm
      { start := p, endPos := p }
  | none, some e =>
      let p := positionFromPos e fm
      { start := p, endPos := p }
  | none, none =>
      let p : PosJson := { line := 0, column := 0 }
      { start := p, endPos := p }

def tacticSource (ti : TacticInfo) : String :=
  ti.stx.reprint.getD ""

def constRefsOfExpr (e : Expr) : Array String := Id.run do
  let names : Std.HashSet Name := e.foldConsts (∅ : Std.HashSet Name) (fun n acc => acc.insert n)
  names.toList.toArray.map (·.toString)

def ppExprToString (e : Expr) : MetaM String := do
  let fmt ← ppExpr e
  return fmt.pretty

def goalsToStrings (mctx : MetavarContext) (goals : List MVarId) : MetaM (Array String) := do
  withMCtx mctx do
    let mut out := #[]
    for g in goals do
      if (← g.isAssigned) then
        continue
      let goalStr ← ppGoal g
      let t := trim goalStr.pretty
      unless t.isEmpty do
        out := out.push t
    return out

def constRefsFromGoals (mctx : MetavarContext) (goals : List MVarId) : MetaM (Array String) := do
  withMCtx mctx do
    let mut refs : Std.HashSet String := ∅
    for g in goals do
      if (← g.isAssigned) then
        continue
      let decl ← g.getDecl
      let t ← instantiateMVars decl.type
      for r in constRefsOfExpr t do
        refs := refs.insert r
    return refs.toList.toArray

def firstUnassignedGoal (goals : List MVarId) : MetaM (Option MVarId) := do
  for g in goals do
    if !(← g.isAssigned) then
      return some g
  return none

def localContextFromMVar (mvarId : MVarId) : MetaM (Array LocalContextSlot) := do
  let decl ← mvarId.getDecl
  let fvars := decl.lctx.getFVarIds
  let mut out : Array LocalContextSlot := #[]
  for i in [:fvars.size] do
    let fvarId := fvars[i]!
    let localDecl := decl.lctx.findDecl? (fun d =>
      if d.fvarId == fvarId then
        some d
      else
        none)
    let name := match localDecl with
      | some d => d.userName.toString
      | none => fvarId.name.toString
    let typeAst ← match localDecl with
      | some d => ppExprToString d.type
      | none => pure ""
    out := out.push
      { slot := s!"fvar#{i}"
        rawFVarId := fvarId.name.toString
        name := name
        typeAst := trim typeAst
        valueAst := "" }
  return out

def contextNamespace (ctx : Option ContextInfo) : String :=
  match ctx with
  | some c => c.toCommandContextInfo.currNamespace.toString
  | none => ""

def contextParentDecl (ctx : Option ContextInfo) : String :=
  match ctx with
  | some c =>
      match c.parentDecl? with
      | some n => n.toString
      | none => ""
  | none => ""

def declKindOf (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .quotInfo _ => "quot"
  | .recInfo _ => "recursor"

def declValueToString (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo info => toString info.value
  | .defnInfo info => toString info.value
  | .opaqueInfo info => toString info.value
  | _ => ""

def maybeExtractDeclRows (modName : String) (env : Environment) : Array DeclRecord :=
  env.constants.toList.foldl
    (fun acc pair =>
      if pair.1.toString.startsWith (modName ++ ".") then
        let refs := constRefsOfExpr pair.2.type
        acc.push {
          schema := schemaVersion
          kind := "decl"
          module := modName
          name := pair.1.toString
          parentDecl := ""
          declKind := declKindOf pair.2
          typeAst := trim (toString pair.2.type)
          valueAst := trim (declValueToString pair.2)
          constRefs := refs
          isSorrySourceScan := refs.contains "sorryAx" || refs.contains "sorry"
        }
      else
        acc)
    #[]

partial def collectTactics
    (tree : InfoTree)
    (ctx? : Option ContextInfo)
    (modName : String)
    (fileMap : FileMap)
    (acc : Array Json)
    : MetaM (Array Json) := do
  match tree with
  | .context c t =>
      let merged := c.mergeIntoOuter? ctx?
      collectTactics t merged modName fileMap acc
  | .node info children =>
      let updatedCtx : Option ContextInfo := info.updateContext? ctx?
      let mut nextAcc := acc
      for child in children do
        nextAcc ← collectTactics child updatedCtx modName fileMap nextAcc
      match info with
      | .ofTacticInfo ti =>
          let source := tacticSource ti
          let parent := contextParentDecl updatedCtx
          let ns := contextNamespace updatedCtx
          let range := rangeFromSyntax ti.stx fileMap
          let beforeGoals ← goalsToStrings ti.mctxBefore ti.goalsBefore
          let afterGoals ← goalsToStrings ti.mctxAfter ti.goalsAfter
          let refs ← constRefsFromGoals ti.mctxAfter ti.goalsAfter
          let locals ← withMCtx ti.mctxAfter do
            match (← firstUnassignedGoal ti.goalsAfter) with
            | some g => localContextFromMVar g
            | none => pure #[]
          let row : TacticTransitionRecord :=
            { schema := schemaVersion
              kind := "tacticTransition"
              module := modName
              parentDecl := parent
              currentNamespace := ns
              range := range
              source := trim source
              goalsBefore := beforeGoals
              goalsAfter := afterGoals
              constRefs := refs
              localContext := locals }
          nextAcc := nextAcc.push (toJson row)
      | _ =>
          pure ()
      pure nextAcc
  | .hole _ =>
      pure acc

def writeJsonl (out : System.FilePath) (lines : Array Json) : IO Unit := do
  let parent? := out.parent
  if let some p := parent? then
    IO.FS.createDirAll p
  let h ← IO.FS.Handle.mk out IO.FS.Mode.write
  for line in lines do
    h.putStrLn line.pretty

def extractFile (inFile : System.FilePath) (outFile : System.FilePath) : IO UInt32 := do
  if !(← inFile.pathExists) then
    IO.eprintln s!"input file does not exist: {inFile}"
    return 1

  let fileContent ← IO.FS.readFile inFile
  let inputCtx := Parser.mkInputContext fileContent inFile.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let opts := Elab.async.setIfNotSet ({} : Options) false
  let (env0, messages) ← processHeader header opts messages inputCtx
  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == MessageSeverity.error then
        IO.eprintln (← msg.toString)
  let moduleName := moduleNameFromFile inFile
  let env0 := env0.setMainModule moduleName
  let commandState0 : Command.State := { Command.mkState env0 messages opts with infoState.enabled := true }
  let frontendState ← IO.processCommands inputCtx parserState commandState0
  let moduleNameStr : String := moduleName.toString
  let fileMap := inputCtx.fileMap
  let (tacticRows, _) ←
    (MetaM.run' (ctx := {}) (s := {}) <| do
      let mut rows : Array Json := #[]
      for t in frontendState.commandState.infoState.trees do
        rows ← collectTactics t none moduleNameStr fileMap rows
      return rows
    ).toIO
      { fileName := inFile.toString
        fileMap := fileMap
        options := ({} : Options)
      } { env := frontendState.commandState.env }
  let declRows := maybeExtractDeclRows moduleNameStr frontendState.commandState.env
  let declJsons := declRows.map toJson
  let outRows := tacticRows ++ declJsons
  writeJsonl outFile outRows
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [inPath, outPath] =>
      unsafe Lean.initSearchPath (← Lean.findSysroot)
      unsafe Lean.enableInitializersExecution
      extractFile (System.FilePath.mk inPath) (System.FilePath.mk outPath)
  | _ =>
      IO.eprintln "usage: infotreeExtract <input-file> <output-jsonl>"
      return 1

end InfoTreeExtract
end DAG

def main (args : List String) : IO UInt32 :=
  DAG.InfoTreeExtract.main args
