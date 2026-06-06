import Lake
open Lake DSL

package lean_sandbox where
  -- Simple sandbox project for Pi extension's Lean verification tool

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "v4.28.0"

@[default_target]
lean_lib Sandbox where
  globs := #[.andSubmodules `Sandbox]
