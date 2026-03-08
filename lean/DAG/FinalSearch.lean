import Lean

open Lean Meta

namespace DAG.FinalSearch

/-- Collect all declaration names once. -/
private def collectNames (env : Environment) : Array String :=
  Id.run do
    let mut names : Array String := #[]
    for (name, _) in env.constants do
      names := names.push (toString name)
    return names

/--
Multi-query environment search utility for DAG exploration scripts.
Each query prints at most `preview` names plus the total match count.
-/
def searchEnv (queries : List String) (preview : Nat := 120) : MetaM Unit := do
  let env ← getEnv
  let names := collectNames env
  for q in queries do
    IO.println s!"--- Searching for '{q}' ---"
    let mut found := false
    let mut count := 0
    for n in names do
      if n.contains q then
        found := true
        if count < preview then
          IO.println n
        count := count + 1
    if !found then
      IO.println "❌ Not found."
    else
      IO.println s!"Total matches for '{q}': {count}"

end DAG.FinalSearch
