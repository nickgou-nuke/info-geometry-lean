import Lean
open Lean in
#eval do
  let base <- importModules #[{ module := `Mathlib }] {}
  let full <- importModules #[{ module := `Mathlib }, { module := `Foo }] {}
  let baseNames := base.constants.toList.map (fun (entry : Name × ConstantInfo) => entry.fst)
  full.constants.toList.forM (fun (entry : Name × ConstantInfo) => do
    let n := entry.fst
    if !(baseNames.contains n) then
      IO.println s!"NEW:{n}")
