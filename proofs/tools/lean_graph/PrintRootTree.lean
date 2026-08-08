import Lean
open Lean Elab

def visitInfo (ctx : ContextInfo) (info : Info) (acc : Nat) : IO Nat := do
  match info with
  | .ofCommandInfo ci =>
    IO.println s!"Command: {ci.stx.reprint.getD \"unknown\"}"
    return acc + 1
  | _ => return acc

def processFile (path : String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let commandState := Command.mkState env messages {}
  let frontendState : Frontend.State := { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }
  let frontendContext : Frontend.Context := { inputCtx := inputCtx }
  let ((), frontendState') ← (Frontend.processCommands).run frontendContext |>.run frontendState
  
  let infoState := frontendState'.commandState.infoState
  for tree in infoState.trees do
    let _ ← tree.foldInfoM (fun ctx info acc => visitInfo ctx info acc) 0

def main (args : List String) : IO Unit := do
  if args.isEmpty then return
  processFile args.head!
