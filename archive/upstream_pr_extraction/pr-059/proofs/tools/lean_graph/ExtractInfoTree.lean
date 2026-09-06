import Lean
import Mathlib
import Lean.Data.Json
import Lean.Server.InfoUtils

open Lean Elab

def ppGoalsJson
    (ctx : ContextInfo)
    (mctx : MetavarContext)
    (goals : List MVarId) :
    IO Json := do
  let ctx := { ctx with mctx := mctx }
  let goalStrings ← ctx.runMetaM {} <| do
    goals.mapM fun mvarId => do
      try
        let f ← Meta.ppGoal mvarId
        pure (toString f)
      catch _ =>
        pure "<ppGoal failed>"
  pure <| Json.arr ((goalStrings.map Json.str).toArray)

def parentDeclHash (ctx : ContextInfo) : UInt64 :=
  match ctx.parentDecl? with
  | none => 0
  | some name =>
      let env := ctx.cmdEnv?.getD ctx.env
      match env.find? name with
      | some ci => hash ci.type
      | none => 0

def parentDeclName (ctx : ContextInfo) : String :=
  match ctx.parentDecl? with
  | some name => name.toString
  | none => "unknown"

def visitInfo (path : String) (ctx : ContextInfo) (info : Info) (acc : Array Json) :
    IO (Array Json) := do
  match info with
  | .ofTacticInfo ti =>
      if ti.goalsBefore.isEmpty then
        return acc

      let goalsBeforeJson ← ppGoalsJson ctx ti.mctxBefore ti.goalsBefore
      let goalsAfterJson  ← ppGoalsJson ctx ti.mctxAfter  ti.goalsAfter

      let tacticStr := (ti.stx.reprint.getD (toString ti.stx)).trim
      let thmName := parentDeclName ctx
      let dbHash := parentDeclHash ctx

      let jsonObj : Json := Json.mkObj [
        ("file", Json.str path),
        ("theorem", Json.str thmName),
        ("de_bruijn_hash", Json.str (toString dbHash)),
        ("tactic", Json.str tacticStr),
        ("goals_before", goalsBeforeJson),
        ("goals_after", goalsAfterJson)
      ]

      IO.eprintln s!"Found Tactic! {tacticStr}"
      return acc.push jsonObj

  | _ =>
      return acc

unsafe def processFile (path : String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  enableInitializersExecution

  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  
  if messages.hasErrors then
    for msg in messages.toList do
      IO.eprintln s!"Header Error: {← msg.toString}"
    return

  let env := env.setMainModule (← moduleNameOfFileName ⟨path⟩ none)

  let commandState := { Command.mkState env messages {} with infoState.enabled := true }

  let s ← IO.processCommands inputCtx parserState commandState

  if s.commandState.messages.hasErrors then
    for msg in s.commandState.messages.toList do
      if msg.severity == .error then
        IO.eprintln s!"Compilation Error: {← msg.toString}"
  else
    IO.eprintln s!"No compilation errors."
      
  let infoState := s.commandState.infoState
  
  IO.eprintln s!"Total InfoTrees: {infoState.trees.size}"
  
  let mut allTactics : Array Json := #[]
  for tree in infoState.trees do
    allTactics ← tree.foldInfoM (visitInfo path) allTactics
    
  for t in allTactics do
    IO.println t.compress

unsafe def main (args : List String) : IO Unit := do
  if args.isEmpty then
    IO.println "Usage: lake env lean --run tools/lean_graph/ExtractInfoTree.lean <file1.lean> <file2.lean> ..."
    return
  for arg in args do
    IO.eprintln s!"Processing {arg}..."
    try
      processFile arg
    catch e =>
      IO.eprintln s!"Error processing {arg}: {e}"
    try
      processFile arg
    catch e =>
      IO.eprintln s!"Error processing {arg}: {e}"
