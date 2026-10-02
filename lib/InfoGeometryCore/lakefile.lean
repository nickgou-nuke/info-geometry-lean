import Lake
open Lake DSL

package InfoGeometryCore

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "1f9fffd5ff0b854b8a1f1f69adc11c61f05f2515"

@[default_target]
lean_lib InfoGeometryCore where
  globs := #[.andSubmodules `InfoGeometryCore]
