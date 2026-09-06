import Lean
import DAG.Isomorphism
import scripts.DAG.Exploration.Common

/-!
# scripts.DAG.Exploration.Isomorphism

Exploratory script for structural-hash and symmetry comparisons of declaration templates.
-/

open Lean
open DAG

private def imports : Array Import := #[
  { module := `DAG.Isomorphism }
]

private def runIsomorphism (env : Environment) : IO Unit := do
  IO.println "--- Symmetry Analysis (WL Algorithm) ---"

  DAG.compareSymmetry env ``Nat.add ``Nat.mul
  DAG.compareSymmetry env ``Nat.add ``Nat.add

  let e1 :=
    Expr.lam `n (Expr.const ``Nat [])
      (Expr.app (Expr.const ``Nat.succ []) (Expr.bvar 0))
      .default
  let h1 := DAG.computeStructuralHash e1 (blindConstants := true)
  IO.println s!"Custom Succ Template Hash: {h1}"

def main : IO Unit :=
  ScriptDAGExploration.runEnvScript imports runIsomorphism
