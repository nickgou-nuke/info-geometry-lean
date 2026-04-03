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

script semanticAudit (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["scripts/quality/audit_semantic.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script graphToBlueprint (args) do
  -- archived compatibility wrapper for the old graph-only blueprint bootstrap path
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["archive/legacy/scripts/graph_to_blueprint_inplace.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script refreshBlueprintTags (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/refresh_blueprint_tags.py"] ++ args.toArray,
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
lean_lib Agent where
  globs := #[.andSubmodules `Agent]

@[default_target]
lean_lib Docs where
  globs := #[.andSubmodules `Docs]

@[default_target]
lean_lib Socratic where
  globs := #[.andSubmodules `Socratic]


@[default_target]
lean_lib InfoGeometry where
  globs := #[.andSubmodules `InfoGeometry]

@[default_target]
lean_lib SelfReference where
  globs := #[.andSubmodules `SelfReference]

lean_lib scripts where
  globs := #[.submodules `scripts]

lean_exe semanticBlockExport where
  root := `scripts.DAG.Exploration.SemanticBlockExport
  supportInterpreter := true

lean_exe semanticBlockServer where
  root := `scripts.DAG.Exploration.SemanticBlockServer
  supportInterpreter := true

lean_exe compilerBridgeServer where
  root := `scripts.DAG.Exploration.CompilerBridgeServer
  supportInterpreter := true
