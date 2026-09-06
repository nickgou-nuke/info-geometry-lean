import Lake
open Lake DSL System

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
    args := #["tools/quality/audit_semantic.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script semanticSnapshot (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/frontier/semantic_snapshot.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script proofSession (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/frontier/proof_session.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script proofPrint (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/frontier/proof_print.py"] ++ args.toArray,
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

script bilingualSpineReport (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/reports/generate_bilingual_spine_report.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script dagStatus (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/dag_status.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script dagRefresh (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/dag_refresh.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script dagReports (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/dag_reports.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script dagDoctor (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/dag_doctor.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script dagAll (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/dag_all.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script changedVerify (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/changed_verify.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailConformance (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/conformance.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailExport (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/export.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailArangoIngest (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/arango_ingest.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailArangoPhysicsEval (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/arango_physics_evaluator.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailFailureHarvest (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/failure_harvester.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailPathLock (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/path_lock_registry.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailHolePackets (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/hole_packets.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

input_file dagToolchainConfigFile where
  path := "dag-toolchain.json"
  text := true

input_file dagRefreshWrapperFile where
  path := "tools/infra/dag_refresh.py"
  text := true

input_file dagManifestWrapperFile where
  path := "tools/infra/dag_manifest.py"
  text := true

input_file dagConfigFile where
  path := "tools/infra/dag_config.py"
  text := true

input_file dagArtifactsFile where
  path := "tools/infra/artifacts.py"
  text := true

input_file dagBuildFile where
  path := "tools/infra/build.py"
  text := true

input_file dagRefreshCoreFile where
  path := "tools/infra/refresh_decl_graph.py"
  text := true

input_file dagPathingFile where
  path := "tools/pathing.py"
  text := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "v4.28.0"
require LeanArchitect from git
  "https://github.com/hanwenzhu/LeanArchitect.git"
  @ "v4.28.0"
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git"
  @ "v4.28.0"

lean_lib DAG where
  globs := #[.andSubmodules `DAG]

lean_lib Agent where
  globs := #[.andSubmodules `Agent]

lean_lib Docs where
  globs := #[.andSubmodules `Docs]

lean_lib Socratic where
  globs := #[.andSubmodules `Socratic]

@[default_target]
lean_lib InfoGeometry where
  globs := #[.andSubmodules `InfoGeometry]

lean_lib InfoGeometryMeta where
  globs := #[.andSubmodules `InfoGeometry.Meta]

lean_lib InfoGeometryCanonical where
  roots := #[`InfoGeometry.Canonical.All]

lean_lib InfoGeometryLLM where
  globs := #[.andSubmodules `InfoGeometry.LLM]

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

lean_exe semanticSnapshotServer where
  root := `scripts.DAG.Exploration.SemanticSnapshotServer
  supportInterpreter := true

lean_exe dagIndexer where
  root := `DAG.Indexer
  supportInterpreter := true

lean_exe groundTruthHarvester where
  root := `DAG.GroundTruthHarvester
  supportInterpreter := true

/--
Experimental authoritative DAG facet.
 It intentionally reuses the managed
Python refresh path and skips its internal prebuild because Lake already tracks
the built `dagIndexer` executable and the umbrella import-root olean below.
-/
package_facet dagMeta (pkg : Package) : FilePath := do
  let configAndWrapperInputs := Job.collectArray <| #[
    ← dagToolchainConfigFile.fetch,
    ← dagRefreshWrapperFile.fetch,
    ← dagConfigFile.fetch,
    ← dagArtifactsFile.fetch,
    ← dagBuildFile.fetch,
    ← dagRefreshCoreFile.fetch,
    ← dagPathingFile.fetch
  ]
  let dagIndexerExe ← dagIndexer.fetch
  let some importRootMod := pkg.findModule? "InfoGeometry.All".toName
    | error "dagMeta facet expects InfoGeometry.All to be a buildable local module"
  let importRootOlean ← fetch <| importRootMod.facet `olean
  let metaPath := pkg.dir / "artifacts" / "dag" / "index" / "meta.json"
  configAndWrapperInputs.bindM (sync := true) fun _ =>
  dagIndexerExe.bindM (sync := true) fun _ =>
  importRootOlean.mapM (sync := true) fun _ => do
    buildFileUnlessUpToDate' metaPath (text := true) do
      proc {
        cmd := "python3"
        args := #[
          "tools/infra/dag_refresh.py",
          "--config", "dag-toolchain.json",
          "--skip-prebuild"
        ]
        cwd := some pkg.dir
      } (quiet := true)
    return metaPath

/--
Experimental manifest-style DAG facet. It tracks one small stamp file that
summarizes the current authoritative refresh state instead of pretending Lake
identically owns each large DAG artifact.
-/
package_facet dagArtifactsManifest (pkg : Package) : FilePath := do
  let configAndWrapperInputs := Job.collectArray <| #[
    ← dagToolchainConfigFile.fetch,
    ← dagManifestWrapperFile.fetch,
    ← dagRefreshWrapperFile.fetch,
    ← dagConfigFile.fetch,
    ← dagArtifactsFile.fetch,
    ← dagBuildFile.fetch,
    ← dagRefreshCoreFile.fetch,
    ← dagPathingFile.fetch
  ]
  let dagIndexerExe ← dagIndexer.fetch
  let some importRootMod := pkg.findModule? "InfoGeometry.All".toName
    | error "dagArtifactsManifest facet expects InfoGeometry.All to be a buildable local module"
  let importRootOlean ← fetch <| importRootMod.facet `olean
  let manifestPath := pkg.dir / "artifacts" / "dag" / "index" / "manifest.json"
  configAndWrapperInputs.bindM (sync := true) fun _ =>
  dagIndexerExe.bindM (sync := true) fun _ =>
  importRootOlean.mapM (sync := true) fun _ => do
    buildFileUnlessUpToDate' manifestPath (text := true) do
      proc {
        cmd := "python3"
        args := #[
          "tools/infra/dag_manifest.py",
          "--config", "dag-toolchain.json",
          "--skip-prebuild"
        ]
        cwd := some pkg.dir
      } (quiet := true)
    return manifestPath

lean_lib Experimental where
  globs := #[.andSubmodules `Experimental]

lean_lib AuditNative where
  globs := #[`AuditNative]

lean_lib AuditStrict where
  globs := #[`AuditStrict]
