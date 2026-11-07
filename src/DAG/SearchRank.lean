import Lean
import DAG.SearchCore

open Lean Meta

namespace DAG.SearchRank

/-- Run one query on a pre-collected declaration-name array. -/
private def runQuery (names : Array String) (q : String) : MetaM Unit := do
  IO.println s!"--- Searching for {q} ---"
  let (hits, count) := DAG.SearchCore.queryContainsWithCount names q
  for n in hits.take 50 do
    IO.println n
  IO.println s!"Total matches for {q}: {count}"

/-- Single-query environment search with capped output + total count. -/
def searchEnv (q : String) : MetaM Unit := do
  let env ← getEnv
  let names := DAG.SearchCore.collectNames env
  runQuery names q

/-- Multi-query search reusing one environment-name pass. -/
def searchEnvMany (qs : List String) : MetaM Unit := do
  let env ← getEnv
  let names := DAG.SearchCore.collectNames env
  for q in qs do
    runQuery names q

end DAG.SearchRank
