import Lean
import DAG.QueryEngine

open Lean
open DAG.Query

def findRecursiveTheorems (depth : Nat) : DAG.QueryM (Name × Name) := do
  let (name, ci) ← matchDeclaration
  where_ (name.getRoot == `Nat)
  let rootExpr ← followChirality ci .Value
  let atom ← reachExpr rootExpr (maxDepth := depth)
  match atom with
  | .const n _ =>
      where_ (n.toString.endsWith ".rec" || n.toString.endsWith ".recOn" || n.toString.endsWith ".casesOn")
      return (name, n)
  | _ => where_ false; return (name, name)

#eval show MetaM Unit from do
  let env ← getEnv
  let queryState : DAG.QueryState := { env := env }

  Lean.logInfo "Running Deep Reasoning Query on Nat namespace (depth 10) for recursors..."
  let results := (findRecursiveTheorems 10 queryState).eraseDups
  Lean.logInfo s!"Found {results.length} recursive theorems/matches in Nat (depth 10):"
  for (thm, rec) in results.take 10 do
    Lean.logInfo s!"  - {thm} uses {rec}"
