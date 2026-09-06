import Lean

open Lean Meta

namespace DAG.SearchRank

/-- Collect all declaration names once. -/
private def collectNames (env : Environment) : Array String :=
  Id.run do
    let mut names : Array String := #[]
    for (name, _) in env.constants do
      names := names.push (toString name)
    return names

/-- Run one query on a pre-collected declaration-name array. -/
private def runQuery (names : Array String) (q : String) : MetaM Unit := do
  IO.println s!"--- Searching for {q} ---"
  let mut count := 0
  for n in names do
    if n.contains q then
      if count < 50 then
        IO.println n
      count := count + 1
  IO.println s!"Total matches for {q}: {count}"

/-- Single-query environment search with capped output + total count. -/
def searchEnv (q : String) : MetaM Unit := do
  let env ← getEnv
  let names := collectNames env
  runQuery names q

/-- Multi-query search reusing one environment-name pass. -/
def searchEnvMany (qs : List String) : MetaM Unit := do
  let env ← getEnv
  let names := collectNames env
  for q in qs do
    runQuery names q

end DAG.SearchRank
