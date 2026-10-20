/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import Lean

open Lean
open Lean.Meta

namespace ScriptDAGExploration

def runEnvScript (imports : Array Import) (action : Environment → IO Unit) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules imports {}
  action env

def runMetaScript (imports : Array Import) (action : MetaM Unit) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules imports {}
  let ctxCore : Core.Context := { fileName := "<scripts.DAG.Exploration>", fileMap := default }
  let sCore : Core.State := { env := env }
  discard <| action.toIO ctxCore sCore

end ScriptDAGExploration
