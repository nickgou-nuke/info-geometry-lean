import Lake
open Lake DSL

package spinorial_core_validation where
  srcDir := "../../lean"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib InfoGeometry where
  globs := #[.submodules `InfoGeometry.Canonical.SpinorialCore]
