import Lean
import DAG.Functor

/-!
# scripts.DAG.Exploration.Functor

Exploratory script for searching small commutative-square patterns in declaration graphs.
-/

open Lean
open DAG

#eval show MetaM Unit from do
  let env ← getEnv
  IO.println "--- Small-Scale Categorical Square Search (Nat) ---"
  let squares ← DAG.findCommutativeSquares env (some `Nat)

  if squares.isEmpty then
    IO.println "No commutative squares found."
  else
    IO.println s!"Found {squares.size} Commutative Squares!"
    for (f, g, h, k) in squares[:5] do
      IO.println s!"Square: ({f.decl}, {g.decl}, {h.decl}, {k.decl})"
