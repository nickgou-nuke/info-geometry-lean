import Lean
import Lean.Data.Json
import Std.Data.HashSet

open Lean Elab Meta

namespace GroundTruthHarvester

structure TacticStep where
  goalBefore : String
  tactic     : String
  goalAfter  : String
deriving ToJson, Repr

def getGoalStates (mctx : MetavarContext) (goals : List MVarId) : MetaM String :=
  withMCtx mctx do
    let mut out := ""
    for g in goals do
      if (← g.isAssigned) then continue
      let goalStr ← ppGoal g
      out := out ++ goalStr.pretty ++ "\n"
    return out.trimAscii.toString

def isPunctuation (tac : String) : Bool :=
  let t := tac.trim
  t == "focus" || t == "rotate_right" || t == "rotate_left" || t == ";" || t == "{" || t == "}" || t == "by" || t == "."

partial def collectSteps (tree : InfoTree) (ctx? : Option ContextInfo := none) : IO (Array TacticStep) := do
  let mut steps := #[]
  match tree with
  | .context ctx t => 
      steps := steps ++ (← collectSteps t (ctx.mergeIntoOuter? ctx?))
  | .node info children =>
    let ctx? := info.updateContext? ctx?
    for child in children do
      steps := steps ++ (← collectSteps child ctx?)
    
    if let .ofTacticInfo ti := info then
      if let some ctx := ctx? then
        let tactic := ti.stx.reprint.getD ""
        if !tactic.isEmpty && !isPunctuation tactic then
          let step ← ctx.runMetaM (lctx := (default : LocalContext)) do
            let before ← getGoalStates ti.mctxBefore ti.goalsBefore
            let after  ← getGoalStates ti.mctxAfter ti.goalsAfter
            return { goalBefore := before, tactic := tactic, goalAfter := after : TacticStep }
          if !step.goalBefore.isEmpty && step.goalBefore != step.goalAfter then
            steps := steps.push step
    
  | .hole _ => pure ()
  return steps

def harvestFile (path : System.FilePath) : IO Unit := do
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header .empty messages inputCtx
  
  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == MessageSeverity.error then
        IO.eprintln s!"Header error in {path}: {← msg.toString}"

  let commandState := Command.mkState env messages .empty
  let frontendState ← IO.processCommands inputCtx parserState commandState
  
  let coreCtx : Core.Context := { fileName := path.toString, fileMap := inputCtx.fileMap }
  let coreState : Core.State := { env := env }
  
  let (steps, _) ← (MetaM.run' (ctx := {}) (s := {}) <| do
    let mut allSteps : Array TacticStep := #[]
    for tree in frontendState.commandState.infoState.trees do
      allSteps := allSteps ++ (← collectSteps tree)
    return allSteps).toIO coreCtx coreState
  
  for step in steps do
    IO.println (toJson step).compress

end GroundTruthHarvester

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Usage: GroundTruthHarvester <file.lean>"
    return 1
  unsafe Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  for arg in args do
    GroundTruthHarvester.harvestFile arg
  return 0
