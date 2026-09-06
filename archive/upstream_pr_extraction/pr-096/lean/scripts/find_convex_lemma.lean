import Lean
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.FDeriv.Basic

open Lean

def main : IO Unit := do
  -- import modules that might contain fderiv/convex lemmas
  let env ← importModules #[
    {module := `Mathlib.Analysis.Convex.Function},
    {module := `Mathlib.Analysis.Convex.Slope},
    {module := `Mathlib.Analysis.Calculus.FDeriv.Basic}
  ] {} 0
  for (n, _) in env.constants.toList do
    let s := n.toString
    if (s.contains "ConvexOn" || s.contains "convex_on") && (s.contains "fderiv" || s.contains "deriv" || s.contains "dual") then
      IO.println s
