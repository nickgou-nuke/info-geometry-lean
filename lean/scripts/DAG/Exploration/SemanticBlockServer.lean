import Lean.Server
import Lean.Server.FileWorker
import DAG.SemanticServerRpc

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  match args with
  | "--worker" :: _ =>
      Lean.Server.FileWorker.workerMain {}
  | _ =>
      Lean.Server.Watchdog.watchdogMain args
