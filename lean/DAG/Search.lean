import Mathlib
import Lean

open Lean Meta

def searchEnv (query : String) : MetaM Unit := do
  let env ← getEnv
  let mut results : Array (String × Expr) := #[]

  for (name, cinfo) in env.constants do
    let nameStr := toString name
    if nameStr.contains query then
      results := results.push (nameStr, cinfo.type)

  if results.isEmpty then
    IO.println s!"❌ No declarations found containing '{query}'."
  else
    IO.println s!"🔍 Found {results.size} declarations matching '{query}':\n"
    for (n, t) in results.take 30 do
      IO.println s!"{n}"
