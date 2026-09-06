import Lean
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading

open Lean

def main : IO Unit := do
  initSearchPath (← findSysroot)
  -- We import the base Clifford modules to ensure they are in the environment
  let env ← importModules #[{ module := `Mathlib.LinearAlgebra.CliffordAlgebra.Basic }, 
                             { module := `Mathlib.LinearAlgebra.CliffordAlgebra.Grading }] {}
  
  IO.println "Searching for Clifford-related finrank theorems..."
  let mut found := false
  for (name, _) in env.constants do
    let s := name.toString
    if s.contains "Clifford" && s.contains "finrank" then
      IO.println s!"Found: {s}"
      found := true
  
  if !found then
    IO.println "No exact match found. Searching for any finrank theorems..."
    for (name, _) in env.constants do
      if name.toString.contains "finrank" then
        if name.toString.contains "matrix" || name.toString.contains "prod" then
          IO.println s!"Found: {name}"
