import Lake
open Lake DSL

package lean_sandbox where
  -- Simple sandbox project for Pi extension's Lean verification tool

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "8f9d9cff6bd728b17a24e163c9402775d9e6a365"

@[default_target]
lean_lib Sandbox where
  globs := #[.andSubmodules `Sandbox]
