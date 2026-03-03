import Mathlib
import Lean

open Lean Meta

def searchEnv (query : String) : MetaM Unit := do
  let env ← getEnv
  let mut matches : Array (String × Expr) := #[]
  
  for (name, cinfo) in env.constants do
    let nameStr := toString name
    if nameStr.contains query then
      matches := matches.push (nameStr, cinfo.type)

  if matches.isEmpty then
    IO.println s!"❌ No declarations found containing '{query}'."
  else
    IO.println s!"🔍 Found {matches.size} declarations matching '{query}':\n"
    for (n, t) in matches.take 30 do
      IO.println s!"{n}"

#eval! searchEnv "finrank_matrix"
#eval! searchEnv "finrank_exteriorAlgebra"
#eval! searchEnv "Clifford"
