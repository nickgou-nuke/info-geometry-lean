import Lean

open Lean Meta Elab

/--
Metaprogramming command to analyze the proof term complexity of a declared theorem.
It traverses the elaborated `Expr` and counts non-trivial logical/algebraic steps.
-/
def analyzeProofComplexity (declName : Name) : MetaM Unit := do
  let env ← getEnv
  match env.find? declName with
  | some (ConstantInfo.thmInfo val) =>
    let term := val.value
    let depth := term.approxDepth
    -- Count the occurrences of non-trivial function applications
    let mut appCount := 0
    term.forEach fun e => do
      if e.isApp then
        appCount := appCount + 1
    if appCount < 3 then
      throwError "Theorem {declName} rejected: proof term complexity is too low ({appCount} applications). Nontrivial proofs are required."
  | _ => return ()