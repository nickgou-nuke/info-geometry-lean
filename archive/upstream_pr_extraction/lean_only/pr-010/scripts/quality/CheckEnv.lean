import Lean
open Lean

#eval do
  let env ← importModules #[{module := `InfoGeometry}] {} 0
  let cnt := (env.constants.toList).length
  IO.println s!"constants count: {cnt}"
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "InfoGeometry" then
      IO.println name
