import Lean
import DAG.SearchCore

open Lean Meta

namespace DAG.Search

/-- Broad namespace suffixes that are poor discriminators in search. -/
private def isStopToken (t : String) : Bool :=
  t.toLower ∈ ["algebra", "theorem", "lemma", "proof", "private", "simp", "aux", "inst"]

/-- Split a chunk on camel-case boundaries, preserving order. -/
private def splitCamelCase (chunk : String) : List String :=
  let rec go (xs : List Char) (curr : List Char) (acc : List String) : List String :=
    match xs with
    | [] =>
      if curr.isEmpty then
        acc.reverse
      else
        (String.ofList curr.reverse :: acc).reverse
    | c :: cs =>
      match curr with
      | [] => go cs [c] acc
      | p :: _ =>
        if p.isLower && c.isUpper then
          go cs [c] (String.ofList curr.reverse :: acc)
        else
          go cs (c :: curr) acc
  go chunk.toList [] []

/-- Split a query into coarse tokens using `_`, `-`, and camel-case boundaries. -/
private def queryTokens (query : String) : List String :=
  let splitUnderscore := query.splitOn "_"
  let splitAll := splitUnderscore.foldr (fun part acc => part.splitOn "-" ++ acc) []
  let camelSplit := splitAll.foldr (fun part acc => splitCamelCase part ++ acc) []
  let tokens := camelSplit.filter (fun t => t != "")
  let normalized := tokens.map String.toLower
  (normalized.eraseDups).filter (fun t => t.length > 1 && !isStopToken t)

/-- Tokenize a declaration name for ranking. -/
private def nameTokens (name : String) : List String :=
  let splitDot := name.splitOn "."
  let splitAll := splitDot.foldr (fun part acc => part.splitOn "_" ++ acc) []
  let camelSplit := splitAll.foldr (fun part acc => splitCamelCase part ++ acc) []
  let normalized := (camelSplit.filter (fun t => t != "")).map String.toLower
  normalized.eraseDups

/-- Filter declaration names by predicate. -/
private def filterNames (names : Array String) (p : String → Bool) : Array String :=
  Id.run do
    let mut out : Array String := #[]
    for n in names do
      if p n then
        out := out.push n
    return out

/-- Print compact token-wise hints when no conjunctive match exists. -/
private def printTokenHints (names : Array String) (tokens : List String) : MetaM Unit := do
  IO.println "Closest token-wise matches:"
  for t in tokens do
    let tokenMatches := filterNames names (fun n => DAG.SearchCore.containsCI n t)
    IO.println s!"  - {t}: {tokenMatches.size}"
    if tokenMatches.size > 2000 then
      IO.println "      (too broad, refine token)"
    else
      for n in tokenMatches.take 5 do
        IO.println s!"      {n}"

/-- Score a declaration name against query tokens (coverage, weighted score). -/
private def scoreName (nameLower : String) (parts : List String) (tokens : List String) : Nat × Nat :=
  tokens.foldl (init := (0, 0)) fun (cov, score) t =>
    if parts.any (fun p => p = t) then
      (cov + 1, score + 10)
    else if parts.any (fun p => p.startsWith t) then
      (cov + 1, score + 6)
    else if nameLower.contains t then
      (cov + 1, score + 3)
    else
      (cov, score)

/-- Rank declaration names by cross-token match quality. -/
private def collectRankedMatches (candidates : Array String) (tokens : List String) :
    Array (Nat × Nat × String) :=
  Id.run do
    let mut results : Array (Nat × Nat × String) := #[]
    for nameStr in candidates do
      let nameLower := nameStr.toLower
      let parts := nameTokens nameStr
      let (cov, score) := scoreName nameLower parts tokens
      if cov > 0 then
        results := results.push (cov, score, nameStr)
    return results

/--
Ranked near-match fallback:
- strict hybrid first (`coverage ≥ 2`);
- then relaxed near-matches (`coverage = 1`) if no hybrid exists.
-/
private def rankedNearMatches (names : Array String) (tokens : List String) :
    Array String × Array String :=
  if tokens.length ≤ 1 then
    (#[], #[])
  else
    let tokenPools : Array (String × Array String) :=
      (tokens.toArray.map fun t => (t, filterNames names (fun n => DAG.SearchCore.containsCI n t)))
    let rankCandidates :=
      (tokenPools.foldl (init := none) fun best (_, pool) =>
        if pool.isEmpty then
          best
        else
          match best with
          | none => some pool
          | some prev => if pool.size < prev.size then some pool else some prev)
      |>.getD names
    let ranked := collectRankedMatches rankCandidates tokens
    let sorted := ranked.qsort (fun a b =>
      let (covA, scoreA, nameA) := a
      let (covB, scoreB, nameB) := b
      covA > covB ||
        (covA = covB &&
          (scoreA > scoreB ||
            (scoreA = scoreB && nameA.length < nameB.length)))
      || (covA = covB && scoreA = scoreB && nameA < nameB))
    let strict := (sorted.filter (fun (cov, _, _) => cov ≥ 2)).map (fun (_, _, n) => n)
    let relaxed :=
      if strict.isEmpty then
        let tokenOrder := (tokenPools.map fun (t, pool) => (t, pool.size)).qsort (fun a b => a.2 < b.2)
        Id.run do
          let mut out : Array String := #[]
          let mut seen : Std.HashSet String := {}
          for (t, _) in tokenOrder do
            let pool := (filterNames names (fun n => DAG.SearchCore.containsCI n t)).qsort (fun a b =>
              a.length < b.length || (a.length = b.length && a < b))
            for n in pool.take 15 do
              if !seen.contains n then
                seen := seen.insert n
                out := out.push n
          if out.isEmpty then
            return #[]
          return out
      else
        #[]
    (strict, relaxed)

/-- Search a query against a pre-collected declaration-name array. -/
private def searchInNames (names : Array String) (query : String) : MetaM Unit := do
  let direct := filterNames names (fun n => DAG.SearchCore.containsCI n query)
  let tokens := queryTokens query
  let fallback :=
    if direct.isEmpty && tokens.length > 1 then
      filterNames names (fun n => tokens.all (fun t => DAG.SearchCore.containsCI n t))
    else
      #[]
  let (nearStrict, nearRelaxed) :=
    if direct.isEmpty && fallback.isEmpty then
      rankedNearMatches names tokens
    else
      (#[], #[])
  let near := if !nearStrict.isEmpty then nearStrict else nearRelaxed
  let results := if !direct.isEmpty then direct else if !fallback.isEmpty then fallback else near
  if results.isEmpty then
    IO.println s!"❌ No declarations found containing '{query}'."
    if !tokens.isEmpty then
      printTokenHints names tokens
  else
    if direct.isEmpty && fallback.isEmpty && !nearStrict.isEmpty then
      IO.println s!"🔍 No exact hit for '{query}', ranked cross-token nearest matches ({near.size}):\n"
    else if direct.isEmpty && fallback.isEmpty && nearStrict.isEmpty && !nearRelaxed.isEmpty then
      IO.println s!"🔍 No hybrid hit for '{query}', ranked near-matches ({near.size}):\n"
    else
      IO.println s!"🔍 Found {results.size} declarations matching '{query}':\n"
    for n in results.take 30 do
      IO.println n

/-- Environment search with strict-hybrid and ranked-near fallback. -/
def searchEnv (query : String) : MetaM Unit := do
  let env ← getEnv
  let names := DAG.SearchCore.collectNames env
  searchInNames names query

/-- Run multiple searches using one pre-collected environment name table. -/
def searchEnvMany (queries : List String) : MetaM Unit := do
  let env ← getEnv
  let names := DAG.SearchCore.collectNames env
  for q in queries do
    searchInNames names q

end DAG.Search
