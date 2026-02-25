import Lake
open Lake DSL

package «infogeometry» where
  srcDir := "lean"
  lintDriver := "strictCheck"

/-- Strict canonical checks run by `lake lint`. -/
script strictCheck (args) do
  let child ← IO.Process.spawn
    { cmd := "bash"
      args := #["lean/scripts/strict-check.sh"] ++ args.toArray
      stdin := .inherit
      stdout := .inherit
      stderr := .inherit }
  child.wait

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "v4.28.0"

-- optional tool for exporting blueprint data directly from Lean
require LeanArchitect from git
  "https://github.com/hanwenzhu/LeanArchitect.git"
  @ "v4.28.0"


-- the main umbrella library depends on the smaller components below
@[default_target]
lean_lib InfoGeometry.Library where
  -- InfoGeometry.Library is just a thin wrapper importing the
  -- canonical umbrella `InfoGeometry.Canonical.All`.
  -- it isn't needed by the subpackages themselves.

-- split the project into smaller lean_libs so that editing one
-- component doesn't force recompilation of the entire collection.
-- each `lean_lib` compiles independently and can declare
-- `requires` to depend on previously-built sublibraries.

lean_lib InfoGeometry.Core

lean_lib InfoGeometry.Convex

lean_lib InfoGeometry.ExponentialFamily
-- dependencies are expressed by `import` statements within
-- the source files rather than via `requires` fields, because
-- the Lake version being used does not support that field.
-- (imports between modules already enforce correct build order.)

lean_lib InfoGeometry.Potential
-- see note above about dependency management

lean_lib InfoGeometry.Projective
-- projective code depends on core via imports

lean_lib InfoGeometry.MaxEnt
-- MaxEnt imports convex and core modules as needed

lean_lib InfoGeometry.Canonical
-- the canonical umbrella imports the other sublibraries;
-- `requires` was omitted for compatibility.
-- the old top‑level `InfoGeometry` target still exists, but it
-- simply re‑exports Library for backward compatibility.

lean_lib InfoGeometry where
  -- root target simply re‑exports Library; no explicit requires
