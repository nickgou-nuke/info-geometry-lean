import Lake
open Lake DSL

package lean_sandbox where
  -- Simple sandbox project for Pi extension's Lean verification tool

-- Use the single repo-local mathlib checkout shared with the main build.
require mathlib from "../.lake/packages" / "mathlib"

@[default_target]
lean_lib Sandbox where
  globs := #[.andSubmodules `Sandbox]
