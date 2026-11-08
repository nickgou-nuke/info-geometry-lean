import Lean
import Lean.Elab.Frontend
import InfoGeometry.Meta.CompilerTelemetry

open Lean
open Lean.Parser
open Lean.Elab
open Lean.Elab.Frontend
open InfoGeometry.Meta

namespace DAG

structure HolonomyEvent where
  node : Name
  tactic_steps : Nat
  context_expansion : Int
  metavariable_flux : Int
  deriving Repr, ToJson, FromJson

/--
Extract telemetry packets from a single `InfoTree`.
-/
partial def collectHolonomy (tree : InfoTree) : Array TacticTelemetry :=
  match tree with
  | .context _ inner =>
      collectHolonomy inner
  | .node info children =>
      let self : Array TacticTelemetry :=
        match info with
        | .ofTacticInfo ti => #[telemetryOfTacticInfo ti]
        | _ => #[]
      children.foldl (init := self) fun acc child =>
        acc ++ collectHolonomy child
  | .hole _ => #[]

/--
Aggregate finite telemetry packets into one event row.
-/
def aggregateTelemetry (name : Name) (telemetries : Array TacticTelemetry) : HolonomyEvent :=
  let steps := telemetries.size
  let ctx_exp := telemetries.foldl (init := 0) fun acc t => acc + t.deltaGamma
  let mvar_flux := telemetries.foldl (init := 0) fun acc t => acc + t.deltaM
  { node := name, tactic_steps := steps, context_expansion := ctx_exp, metavariable_flux := mvar_flux }

/-- Run frontend commands while invoking `hook` after each command. -/
partial def runCommands (hook : FrontendM Unit) : FrontendM Unit := do
  let done ← Frontend.processCommand
  hook
  unless done do
    runCommands hook

private def collectNewDecls (env : Environment) (seen : NameSet) : Array Name × NameSet :=
  let (decls, seen') :=
    env.constants.foldStage2
      (fun (acc : Array Name × NameSet) n _ =>
        let (arr, s) := acc
        if s.contains n then
          (arr, s)
        else
          (arr.push n, s.insert n))
      (#[], seen)
  (decls.qsort Name.lt, seen')

/--
Extract holonomy telemetry for all declarations produced while elaborating `path`.
-/
def processFile (path : System.FilePath) : IO (Array HolonomyEvent) := do
  if !(← path.pathExists) then
    throw <| IO.userError s!"HolonomyExporter: file not found: {path}"

  Lean.initSearchPath (← Lean.findSysroot)
  let opts := Elab.async.setIfNotSet ({} : Options) false
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path.toString
  let (headerStx, parserState, msgs) ← Parser.parseHeader inputCtx
  let (env0, msgs) ← Elab.processHeader headerStx opts msgs inputCtx 0
  let cmdState0 := Command.mkState env0 msgs opts
  let initSt : Frontend.State :=
    { commandState := cmdState0
      parserState := parserState
      cmdPos := parserState.pos
      commands := #[] }
  let ctx : Frontend.Context := { inputCtx := inputCtx }

  let baseSeen : NameSet :=
    env0.constants.fold (init := ({} : NameSet)) (fun s n _ => s.insert n)
  let seenRef : IO.Ref NameSet ← IO.mkRef baseSeen
  let treesRef : IO.Ref Nat ← IO.mkRef 0
  let eventsRef : IO.Ref (Array HolonomyEvent) ← IO.mkRef #[]

  let hook : FrontendM Unit := do
    let st ← get
    let after := st.commandState

    let seen ← seenRef.get
    let (newDecls, seen') := collectNewDecls after.env seen
    seenRef.set seen'

    let trees := after.infoState.trees
    let prevCount ← treesRef.get
    let nowCount := trees.size
    treesRef.set nowCount

    let telemetries :=
      Id.run do
        let mut out : Array TacticTelemetry := #[]
        for i in [prevCount:nowCount] do
          out := out ++ collectHolonomy trees[i]!
        out

    if telemetries.isEmpty then
      return

    eventsRef.modify fun prior =>
      if newDecls.isEmpty then
        let synthetic := Name.mkSimple s!"<command:{prior.size}>"
        prior.push (aggregateTelemetry synthetic telemetries)
      else
        newDecls.foldl (init := prior) fun acc declName =>
          acc.push (aggregateTelemetry declName telemetries)

  let (_u, _stFinal) ← ((runCommands hook).run ctx).run initSt
  eventsRef.get

/-- CLI entrypoint. -/
def holonomyExporterMain (args : List String) : IO UInt32 := do
  match args with
  | [fileStr] =>
      let events ← processFile (System.FilePath.mk fileStr)
      IO.println (toJson events).pretty
      pure 0
  | _ =>
      IO.eprintln "usage: holonomy_exporter <lean-file>"
      pure 1

end DAG

def main (args : List String) : IO UInt32 :=
  DAG.holonomyExporterMain args
