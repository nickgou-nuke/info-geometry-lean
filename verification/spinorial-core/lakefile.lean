import Lake
open Lake DSL

package spinorial_core_validation where
  srcDir := "../../lean"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "1f9fffd5ff0b854b8a1f1f69adc11c61f05f2515"

lean_lib InfoGeometry where
  roots := #[`InfoGeometry.Canonical.SpinorialCore.All]
