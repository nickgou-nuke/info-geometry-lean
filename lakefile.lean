import Lake
open Lake DSL System

package infogeometry where
  srcDir := "lean"
  lintDriver := "strictCheck"

script shadowPlantWorker (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/shadow_plant_worker.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script strictCheck (args) do
  let child ← IO.Process.spawn {
    cmd := "bash",
    args := #["scripts/quality/strict-check.sh"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script smokeSpikes (args) do
  let child ← IO.Process.spawn {
    cmd := "bash",
    args := #[
      "-lc",
      "cd $(pwd) && lake build InfoGeometry.Topology.All InfoGeometry.Projective.All"
    ] ++ args.toArray,
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

script semanticContentAudit (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/quality/semantic_content_audit.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script ingestSemanticContentAudit (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/ingest_semantic_content_audit.py"] ++ args.toArray,
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

script leanGraphSlice (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/hydrated_dag_to_lean_graph.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leandojoV2Bridge (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/leandojo_v2_bridge.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script pdaFormL4Bridge (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/pda_forml4_bridge.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script ulamTraceBridge (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/ulam_trace_bridge.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script tacticPathRankingDataset (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/build_tactic_path_ranking_dataset.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script analyzeTacticPathRanking (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/analyze_tactic_path_ranking.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script lightconeSpectralFilter (args) do
  let child ← IO.Process.spawn {
    cmd := ".venv-py312/bin/python",
    args := #["tools/infra/lightcone_spectral_filter.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script enrichTacticPathLightconeSpectrum (args) do
  let child ← IO.Process.spawn {
    cmd := ".venv-py312/bin/python",
    args := #["tools/infra/enrich_tactic_path_with_lightcone_spectrum.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script enrichTacticPathOperatorSpectrum (args) do
  let child ← IO.Process.spawn {
    cmd := ".venv-py312/bin/python",
    args := #["tools/infra/enrich_tactic_path_operator_spectrum.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leanAutoTraceBridge (args) do
  let child ← IO.Process.spawn {
    cmd := ".venv-py312/bin/python",
    args := #["tools/infra/lean_auto_trace_bridge.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script improverTraceBridge (args) do
  let child ← IO.Process.spawn {
    cmd := ".venv-py312/bin/python",
    args := #["tools/infra/improver_trace_bridge.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script causalChiralPromptBuilder (args) do
  let child ← IO.Process.spawn {
    cmd := ".venv-py312/bin/python",
    args := #["tools/infra/causal_chiral_prompt_builder.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script jixiaTrainingData (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/jixia_batch_training.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script paperproofTraceBridge (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/paperproof_trace_bridge.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script paperproofRpcExport (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/paperproof_rpc_export_schema.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script paperproofJixiaCompare (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/paperproof_jixia_compare.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script blueprintAlexandriaBridge (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/blueprint_alexandria_bridge.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script blueprintArangoMatch (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/blueprint_arango_match.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script paperproofTrainingEffects (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/paperproof_training_effects.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script paperproofProofForest (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/paperproof_proof_forest.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script paperproofTableauDetector (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/paperproof_tableau_detector.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script paperproofBidirectionalCone (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/paperproof_bidirectional_cone.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leanParanoiaAudit (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/leanparanoia_audit_bridge.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script safeVerifyAudit (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/safeverify_audit_bridge.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script hiveSpecSubmission (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/hive_spec_submission_policy.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leanAutograderReport (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/lean_autograder_report_bridge.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script hiveMultiCheckerMerge (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/hive_multichecker_merge.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script buildPredigestionPackets (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/build_predigestion_packets.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script hivePredigestionIngest (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/hive_predigestion_ingest.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script txt2kgHiveIngest (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/alexandria/txt2kg_hive_ingest.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script extractCompressedCone (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/extract_compressed_cone.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script epistemicReactorEnsemble (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/epistemic_reactor_ensemble.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script predigestionHiveDemo (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/run_predigestion_to_hive_demo.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script checkResidentModel (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/check_resident_model_endpoint.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script checkVllmMistralCompat (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/check_vllm_mistral_compat.py"] ++ args.toArray,
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

script leantrailAstExtract (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/ast_extract.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailAQLSchema (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/aql_schema.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailArangoDump (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/arango_dump.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailOracleSearch (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/oracle_search.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailExternalIndex (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/external_index.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailAQLQuery (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/aql_query.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailAstAQLOptimize (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/ast_aql_optimize.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailSmoke (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/smoke_test.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailSyntaxDump (args) do
  let child ← IO.Process.spawn {
    cmd := "lake",
    args := #["env", "lean", "--run", "tools/leantrail/DumpLeanGraph.lean"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailCheckDumpShape (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/check_dump_shape.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailSyntaxIngest (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/ingest_syntax_to_arango.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailAQLSmoke (args) do
  let child ← IO.Process.spawn {
    cmd := "bash",
    args := #["tools/leantrail/aql_smoke_test.sh"] ++ args.toArray,
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

script leantrailVacuityIngest (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/vacuity_ingest.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailVacuityAudit (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/vacuity_audit.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailSurgeryPlan (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/surgery_plan.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailSurgeryApply (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/surgery_apply.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailCriticPackets (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/critic_packets.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailCriticPrompts (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/critic_prompt_builder.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script leantrailCriticIngest (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/leantrail/critic_ingest.py"] ++ args.toArray,
    stdin := .inherit,
    stdout := .inherit,
    stderr := .inherit
  }
  child.wait

script chatgptCollaborator (args) do
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #["tools/infra/chatgpt_collaborator_bridge.py"] ++ args.toArray,
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

require InfoGeometryCore from "lib" / "InfoGeometryCore"

require Qq from ".lake/packages/Qq"
require plausible from ".lake/packages/plausible"

-- Enforce a single local mathlib source for this repository.
-- Do not let Lake re-resolve mathlib from the upstream git URL.
require mathlib from ".lake/packages/mathlib"
require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"
  @ "c85fb0b45ce9ebaaa4715c7d043aadda80306c46" / "lean"
require paranoia from git "https://github.com/oOo0oOo/LeanParanoia.git"
  @ "11c2385ade3cc417d69ce837bfda9d2c5b1d61ab"
require LeanArchitect from git "https://github.com/hanwenzhu/LeanArchitect.git"
  @ "54d3fb249685db8e5a564e0b3f331cff77991607"
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git"
  @ "v4.28.1"

require «GIFT» from
  "external_refs/gift-framework-core"
require Atlas from
  "external_refs/atlas-lean"
require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git"
  @ "c360b5df5d8a67ed8f1a8769aa157f6adca7dd53"

lean_lib DAG where
  globs := #[.andSubmodules `DAG]

lean_lib Agent where
  globs := #[.andSubmodules `Agent]

lean_lib Docs where
  globs := #[.andSubmodules `Docs]

lean_lib Socratic where
  globs := #[.andSubmodules `Socratic]

lean_lib Omega where
  globs := #[.andSubmodules `Omega]

@[default_target]
lean_lib InfoGeometry where
  moreLinkArgs := #["-L./backend/cuda/build", "-L/usr/local/cuda/lib64", "-lzorn_cuda", "-lcudart", "-lcublas"]
  -- Build the root project entrypoint. Repository policy is that every
  -- repo-owned Lean module under `lean/InfoGeometry` must be buildable and
  -- provided through the root/`InfoGeometry.All` surface. Generated, proposal,
  -- and experimental modules are not exempt; if they fail this contract, repair
  -- them and wire them into the provided library surface.
  globs := #[.andSubmodules `InfoGeometry]

@[test_driver]
lean_lib InfoGeometryTestSuite where
  srcDir := "../tests"
  roots := #[
    `InfoGeometryTests,
    `ComplexAnalyticBridgeTests,
    `PrimitiveExactnessTests,
    `PrimitiveCuntzIsometryTests,
    `BekensteinHawkingDyadicEntropyTests,
    `PO55ConformalClosureTests,
    `DvorakSystemTest
  ]

/--
Pinned local clone of the formal Lean proof of Erdos Problem #1196.

The source lives under `external/Erdos1196` at commit
`02fba13be7487cc51315f68d8fa7ef277633d3c8`, with theorem
`PrimitiveSetsAboveX.mainTheorem`.

This library is intentionally not a default target: the external proof repo is
pinned to Lean `v4.30.0-rc1`, while this repository is currently pinned to
Lean `v4.28.1`. Build/import it explicitly after toolchain alignment.
-/
lean_lib PrimitiveSetsAboveX where
  globs := #[.andSubmodules `PrimitiveSetsAboveX]

lean_lib InfoGeometryMeta where
  globs := #[.andSubmodules `InfoGeometry.Meta]

lean_lib InfoGeometryCanonical where
  roots := #[`InfoGeometry.Canonical.All, `InfoGeometry.Canonical.SplitOctonionTKK55,
    `InfoGeometry.Canonical.SplitOctonionTKK55Blocks,
    `InfoGeometry.Canonical.SplitOctonionTKK55LieEquivalence,
    `InfoGeometry.Canonical.HyperbolicDiagonalO55,
    `InfoGeometry.Canonical.OrthogonalGroup55,
    `InfoGeometry.Canonical.Pin55OrthogonalBridge,
    `InfoGeometry.Canonical.Pin55NativeCover,
    `InfoGeometry.Canonical.SheetSplitQuaternionic,
    `InfoGeometry.Canonical.HexagonalSixRootTiling,
    `InfoGeometry.Canonical.SixStateSpectralBridge,
    `InfoGeometry.Canonical.SixStateCharacteristicPolynomial,
    `InfoGeometry.Canonical.TwoSheetOperatorCoordinates,
    `InfoGeometry.Canonical.TwoSheetStokesCoordinates]

lean_lib HestenesPauliSheet where
  roots := #[`InfoGeometry.Canonical.ChiralStokesPauliBasis,
    `InfoGeometry.Canonical.HestenesPauliSheetBridge]

lean_lib SixStateModularConjugation where
  roots := #[`InfoGeometry.Canonical.SixStateModularConjugationIdentification]

lean_lib AffineOrthogonal55Glide where
  roots := #[`InfoGeometry.Canonical.AffineOrthogonal55Glide]

lean_lib Clifford55PinFramework where
  roots := #[
      `InfoGeometry.Clifford.Cl55WittNativeCartanDieudonne,
      `InfoGeometry.Clifford.Cl55WittPinNativeTwistedAction,
      `InfoGeometry.Clifford.Cl55RealSplitPinVolumeAnticommutation,
      `InfoGeometry.Clifford.Cl55WittPinCoverEvidence,
      `InfoGeometry.Clifford.Pin55OrthogonalCover]

lean_lib Clifford55ChiralHyperbolicStructure where
  roots := #[`InfoGeometry.Clifford.Clifford55ChiralHyperbolicStructure]

lean_lib AffineOrthogonal55Semidirect where
  roots := #[`InfoGeometry.Canonical.AffineOrthogonal55Semidirect]

lean_lib Orthogonal55Components where
  roots := #[`InfoGeometry.Canonical.Orthogonal55Components]

lean_lib AffinePin55Cover where
  roots := #[`InfoGeometry.Canonical.AffinePin55Cover]

lean_lib TKK55LieEquivalence where
  roots := #[`InfoGeometry.Canonical.SplitOctonionTKK55LieEquivalence]

lean_lib HyperbolicDiagonalO55Bridge where
  roots := #[`InfoGeometry.Canonical.HyperbolicDiagonalO55]

lean_lib TwelveFoldSheetColorOmega where
  roots := #[`InfoGeometry.Canonical.TwelveFoldSheetColorOmega]

lean_lib SplitOctonionSixSectorBridge where
  roots := #[`InfoGeometry.Canonical.SplitOctonionSixSectorBridge]

lean_lib SplitOctonionChiralFrame where
  roots := #[`InfoGeometry.Canonical.SplitOctonionChiralFrame]

lean_lib SplitOctonionSixSectorFin3 where
  roots := #[`InfoGeometry.Canonical.SplitOctonionSixSectorFin3]

lean_lib TwelveFoldSpectralBridge where
  roots := #[`InfoGeometry.Canonical.TwelveFoldSpectralBridge]

lean_lib TwelveFoldParityCompatibility where
  roots := #[`InfoGeometry.Canonical.TwelveFoldParityCompatibility]

lean_lib HexIndexSplitOctonionBridge where
  roots := #[`InfoGeometry.Canonical.HexIndexSplitOctonionBridge]

lean_lib HexIndexTrialityEquivariance where
  roots := #[`InfoGeometry.Canonical.HexIndexTrialityEquivariance]

lean_lib HexIndexTrialityLabelBridge where
  roots := #[`InfoGeometry.Canonical.HexIndexTrialityLabelBridge]

lean_lib SplitOctonionParavectorCorners where
  roots := #[`InfoGeometry.Canonical.SplitOctonionParavectorCorners]

lean_lib SplitOctonionChiralReflectionBridge where
  roots := #[`InfoGeometry.Canonical.SplitOctonionChiralReflectionBridge]

lean_lib Cl55OddChiralityExchange where
  roots := #[`InfoGeometry.Clifford.Cl55OddChiralityExchange]

lean_lib HestenesQuaternionCore where
  roots := #[`InfoGeometry.Canonical.HestenesQuaternionCore]

lean_lib HestenesQuaternionSlice where
  roots := #[`InfoGeometry.Canonical.HestenesQuaternionSlice]

lean_lib ClPlus14DualProduct where
  roots := #[`InfoGeometry.Canonical.ClPlus14DualProduct]

lean_lib SixStateModularConjugationIdentification where
  roots := #[`InfoGeometry.Canonical.SixStateModularConjugationIdentification]

lean_lib FiniteKreinTomitaSixState where
  roots := #[`InfoGeometry.Canonical.FiniteKreinTomitaSixState]

lean_lib HestenesOmegaHyperbolic where
  roots := #[`InfoGeometry.Canonical.HestenesOmegaHyperbolic]

lean_lib HestenesSheetBoost where
  roots := #[`InfoGeometry.Canonical.HestenesSheetBoost]

lean_lib HestenesHyperbolicDoubling where
  roots := #[`InfoGeometry.Canonical.HestenesHyperbolicDoubling]

lean_lib HestenesPauliEvenClifford where
  roots := #[`InfoGeometry.Canonical.HestenesPauliEvenClifford]

lean_lib HestenesPauliEvenAdjoint where
  roots := #[`InfoGeometry.Canonical.HestenesPauliEvenAdjoint]

lean_lib HestenesPauliSheetBridge where
  roots := #[`InfoGeometry.Canonical.HestenesPauliSheetBridge]

lean_lib HestenesSplitOctonionBasis where
  roots := #[`InfoGeometry.Canonical.HestenesSplitOctonionBasis]

lean_lib QuaternionOmegaDoublingSquare where
  roots := #[`InfoGeometry.Canonical.QuaternionOmegaDoublingSquare]

lean_lib HestenesRotorOwners where
  roots := #[
    `InfoGeometry.Canonical.HestenesCircularSheetCAR,
    `InfoGeometry.Canonical.HestenesPhaseBoostRotors,
    `InfoGeometry.Canonical.HestenesLoxodromicRotor,
    `InfoGeometry.Canonical.HestenesLoxodromicCasimirs]

lean_lib HestenesStokesFlowTopCat where
  roots := #[`InfoGeometry.Canonical.HestenesStokesFlowTopCat]

lean_lib HestenesCliffordKrein where
  roots := #[`InfoGeometry.Canonical.HestenesCliffordKrein]

lean_lib TwoSheetKreinAdjoint where
  roots := #[`InfoGeometry.Canonical.TwoSheetKreinAdjoint]

lean_lib TwoSheetKreinRealLinear where
  roots := #[`InfoGeometry.Canonical.TwoSheetKreinRealLinear]

lean_lib TwoSheetStokesKreinRealLinear where
  roots := #[`InfoGeometry.Canonical.TwoSheetStokesKreinRealLinear]

lean_lib TwoSheetKreinModularCompatibility where
  roots := #[`InfoGeometry.Canonical.TwoSheetKreinModularCompatibility]

lean_lib TwoSheetStokesKreinModularCompatibility where
  roots := #[`InfoGeometry.Canonical.TwoSheetStokesKreinModularCompatibility]


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

lean_exe infotreeExtract where
  root := `DAG.InfoTreeExtract
  supportInterpreter := true

lean_exe disconnectedAudit where
  root := `DAG.DisconnectedAudit
  supportInterpreter := true

lean_exe exactProoflessnessAudit where
  root := `DAG.ExactProoflessnessAudit
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

lean_exe benchmark {
  root := `InfoGeometry.Hardware.Benchmark
  moreLinkArgs := #["-L./backend/cuda/build", "-L/usr/local/cuda/lib64", "-lzorn_cuda", "-lcudart", "-lcublas"]
}
