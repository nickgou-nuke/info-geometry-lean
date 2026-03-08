import Lake
open Lake DSL

package infogeometry where
  srcDir := "lean"
  lintDriver := "strictCheck"

script strictCheck (args) do
  let child ← IO.Process.spawn {
    cmd := "bash",
    args := #["scripts/quality/strict-check.sh"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script graphToBlueprint (args) do
  -- simple wrapper to run the Python converter from the graph
  let child ← IO.Process.spawn {
    cmd := "python",
    args := #["-m", "scripts", "graph-to-blueprint"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "v4.28.0"
require LeanArchitect from git
  "https://github.com/hanwenzhu/LeanArchitect.git"
  @ "v4.28.0"
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git"
  @ "v4.28.0"

@[default_target]
lean_lib DAG where
  globs := #[.andSubmodules `DAG]

@[default_target]
lean_lib Docs where
  globs := #[.andSubmodules `Docs]

@[default_target]
lean_lib Socratic where
  globs := #[.andSubmodules `Socratic]

@[default_target]
lean_lib InfoGeometry.GraphExport

@[default_target]
lean_lib InfoGeometry where
  globs := #[.andSubmodules `InfoGeometry]

@[default_target]
lean_lib SelfReference where
  globs := #[.andSubmodules `SelfReference]

@[default_target]
lean_lib scripts where
  globs := #[.submodules `scripts]
