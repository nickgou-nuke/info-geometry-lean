import Lean
import DAG.Isomorphism

open Lean
open DAG

#eval show MetaM Unit from do
  let env ← getEnv
  IO.println "--- Symmetry Analysis (WL Algorithm) ---"

  DAG.compareSymmetry env ``Nat.add ``Nat.mul
  DAG.compareSymmetry env ``Nat.add ``Nat.add

  let e1 := Expr.lam `n (Expr.const ``Nat []) (Expr.app (Expr.const ``Nat.succ []) (Expr.bvar 0)) .default
  let h1 := DAG.computeStructuralHash e1 (blindConstants := true)
  IO.println s!"Custom Succ Template Hash: {h1}"
