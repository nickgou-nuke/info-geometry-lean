/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import Lean.Data.Json
import DAG.BlockExport
import DAG.ServerExport

/-!
Compatibility executable for the historical `semanticBlockExport` Lake target.

The semantic-block implementation is now owned by `DAG.BlockExport` and
`DAG.ServerExport`.  This wrapper deliberately contains no independent graph
algorithm: it translates the historical `[input, output]` invocation to the
current owner API and preserves the no-argument defaults.
-/

private def defaultInput : String :=
  "lean/InfoGeometry/Canonical/GrandSynthesis.lean"

private def defaultOutput : String :=
  "reports/dag/GrandSynthesis.semantic-block.json"

def main (args : List String) : IO UInt32 := do
  let argv := args.toArray
  let inputFile := argv.getD 0 defaultInput
  let outputFile := argv.getD 1 defaultOutput
  let result ← DAG.exportFile (System.FilePath.mk inputFile)
  let payload := DAG.Server.semanticBlocksPayload result
  if let some parent := (System.FilePath.mk outputFile).parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile (System.FilePath.mk outputFile) payload.pretty
  IO.println s!"[semanticBlockExport] wrote {outputFile}"
  pure 0
