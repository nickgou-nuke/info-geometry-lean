import Lean
import DAG.Betti
import scripts.DAG.Exploration.Common

/-!
# scripts.DAG.Exploration.Betti

Exploratory script that computes basic homological summaries for declaration expression graphs.
-/

open Lean
open DAG

private def imports : Array Import := #[
  { module := `DAG.Betti }
]

private def runBetti : MetaM Unit := do
  let env ← getEnv
  if let some ci := env.find? ``Nat.add then
    if let some val := ci.value? then
      IO.println "Analyzing Nat.add..."
      DAG.computeExprHomology val

def main : IO Unit :=
  ScriptDAGExploration.runMetaScript imports runBetti
