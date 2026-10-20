/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import Lean.Server
import Lean.Server.FileWorker

import Agent.ProofServerRpc
import InfoGeometry.Meta.Architecture

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  match args with
  | "--worker" :: _ =>
      Lean.Server.FileWorker.workerMain {}
  | _ =>
      Lean.Server.Watchdog.watchdogMain args
