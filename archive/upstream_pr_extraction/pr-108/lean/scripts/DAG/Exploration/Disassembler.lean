import Lean
import Lean.Data.Json
import DAG.Disassembler
import scripts.DAG.Exploration.Common

/-!
# scripts.DAG.Exploration.Disassembler

Exploratory script for disassembling declarations into expression-graph JSON summaries.
-/

open Lean
open DAG

private def imports : Array Import := #[
  { module := `DAG.Disassembler }
]

private def runDisassembler (env : Environment) : IO Unit := do
  if let some graph := DAG.disassembleConst env ``Nat.add then
    IO.println s!"Disassembled Nat.add into {graph.nodes.size} nodes and {graph.edges.size} edges."
    -- IO.println (toJson graph).pretty -- Uncomment to see the full JSON dump
  else
    IO.println "Could not find or disassemble Nat.add"

def main : IO Unit :=
  ScriptDAGExploration.runEnvScript imports runDisassembler
