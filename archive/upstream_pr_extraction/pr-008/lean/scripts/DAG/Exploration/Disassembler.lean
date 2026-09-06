import Lean
import Lean.Data.Json
import DAG.Disassembler

/-!
# scripts.DAG.Exploration.Disassembler

Exploratory script for disassembling declarations into expression-graph JSON summaries.
-/

open Lean
open DAG

-- A test to evaluate the disassembler on `Nat.add`
#eval show Lean.MetaM Unit from do
  let env ← Lean.getEnv
  if let some graph := DAG.disassembleConst env ``Nat.add then
    let msg :=
      m!"Disassembled Nat.add into {graph.nodes.size} nodes and " ++
        m!"{graph.edges.size} edges."
    Lean.logInfo msg
    -- Lean.logInfo (toJson graph).pretty -- Uncomment to see the full JSON dump
  else
    Lean.logWarning "Could not find or disassemble Nat.add"
