import Lean
import DAG.SearchCore

open Lean Meta

namespace DAG.FinalSearch

/--
Multi-query environment search utility for DAG exploration scripts.
Each query prints at most `preview` names plus the total match count.
-/
def searchEnv (queries : List String) (preview : Nat := 120) : MetaM Unit := do
  let env ← getEnv
  let names := DAG.SearchCore.collectNames env
  for q in queries do
    IO.println s!"--- Searching for '{q}' ---"
    let (hits, count) := DAG.SearchCore.queryContainsWithCount names q
    if hits.isEmpty then
      IO.println "❌ Not found."
    else
      for n in hits.take preview do
        IO.println n
      IO.println s!"Total matches for '{q}': {count}"

end DAG.FinalSearch
