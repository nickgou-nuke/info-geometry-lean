import Lake
open Lake DSL

package «infogeometry» where
  srcDir := "."
  lintDriver := "strictCheck"

/-- Strict canonical checks run by `lake lint`. -/
script strictCheck (args) do
  let child ← IO.Process.spawn
    { cmd := "bash"
      args := #["scripts/strict-check.sh"] ++ args.toArray
      stdin := .inherit
      stdout := .inherit
      stderr := .inherit }
  child.wait

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "v4.28.0"

@[default_target]
lean_lib InfoGeometry where
