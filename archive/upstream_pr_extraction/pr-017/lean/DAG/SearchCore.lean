import Lean

open Lean

namespace DAG.SearchCore

/-- Collect all declaration names once. -/
def collectNames (env : Environment) : Array String :=
  Id.run do
    let mut names : Array String := #[]
    for (name, _) in env.constants do
      names := names.push (toString name)
    return names

/-- Case-insensitive substring check. -/
def containsCI (hay needle : String) : Bool :=
  hay.toLower.contains needle.toLower

/-- Case-sensitive substring query. -/
def queryContains (names : Array String) (query : String) : Array String :=
  Id.run do
    let mut out : Array String := #[]
    for n in names do
      if n.contains query then
        out := out.push n
    return out

/-- Case-insensitive substring query. -/
def queryContainsCI (names : Array String) (query : String) : Array String :=
  Id.run do
    let mut out : Array String := #[]
    for n in names do
      if containsCI n query then
        out := out.push n
    return out

/-- Case-sensitive substring query with total match count. -/
def queryContainsWithCount (names : Array String) (query : String) : Array String × Nat :=
  Id.run do
    let hits := queryContains names query
    return (hits, hits.size)

end DAG.SearchCore
