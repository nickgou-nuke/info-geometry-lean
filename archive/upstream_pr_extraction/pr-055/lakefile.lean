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

lean_lib proofs where
  srcDir := ".."
  -- Proofs folded in from external_refs/auto/proofs: single shared mathlib,
  -- single build hash (no separate root / no cache thrash). Not a default
  -- target so the main build stays green.
  globs := #[.andSubmodules `proofs]

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

lean_lib OperatorQGTSoldering where
  roots := #[`InfoGeometry.Optics.OperatorQGTSoldering]

lean_lib ChiralLorentzOperatorLift where
  roots := #[`InfoGeometry.Optics.ChiralLorentzOperatorLift]

lean_lib ChiralLorentzFockQuadratic where
  roots := #[`InfoGeometry.Clifford.ChiralLorentzFockQuadratic]

lean_lib ChiralGrandCanonicalOperatorGeometry where
  roots := #[`InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry]

lean_lib ChiralGrandCanonicalModularGenerator where
  roots := #[`InfoGeometry.Clifford.ChiralGrandCanonicalModularGenerator]

lean_lib ChiralGrandCanonicalThermalGeometry where
  roots := #[`InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry]

lean_lib ChiralGrandCanonicalHestenesRotor where
  roots := #[`InfoGeometry.Clifford.ChiralGrandCanonicalHestenesRotor]

lean_lib ChiralGrandCanonicalLoxodromicRotor where
  roots := #[`InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicRotor]

lean_lib ChiralGrandCanonicalLoxodromicThermalBridge where
  roots := #[`InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicThermalBridge]

lean_lib ChiralGrandCanonicalFiniteKMS where
  roots := #[`InfoGeometry.Physics.Thermodynamics.ChiralGrandCanonicalFiniteKMS]

lean_lib ChiralParitySuperalgebra where
  roots := #[`InfoGeometry.Canonical.ChiralParitySuperalgebra]

lean_lib UHFColimitSuperchargeBridge where
  roots := #[`InfoGeometry.Canonical.UHFColimitSuperchargeBridge]

lean_lib ChiralModularFlowColimitBridge where
  roots := #[`InfoGeometry.Canonical.ChiralModularFlowColimitBridge]

lean_lib OperatorValuedJonesProduct where
  roots := #[`InfoGeometry.Clifford.OperatorValuedJonesProduct]

lean_lib CliffordCARQuadraticClosure where
  roots := #[`InfoGeometry.OperatorAlgebra.CliffordCARQuadraticClosure]

lean_lib QuadraticNoncommutativeIdentity where
  roots := #[`InfoGeometry.OperatorAlgebra.QuadraticNoncommutativeIdentity]

lean_lib CliffordCARGrandCanonical where
  roots := #[`InfoGeometry.OperatorAlgebra.CliffordCARGrandCanonical]

lean_lib ThermalBogoliubovCAR where
  roots := #[`InfoGeometry.OperatorAlgebra.ThermalBogoliubovCAR]

lean_lib ThreeZ2OperatorGradings where
  roots := #[`InfoGeometry.OperatorAlgebra.ThreeZ2OperatorGradings]

lean_lib InnerConjugation where
  roots := #[`InfoGeometry.OperatorAlgebra.InnerConjugation]

lean_lib OperatorProjectiveRatio where
  roots := #[`InfoGeometry.OperatorAlgebra.OperatorProjectiveRatio]

lean_lib OperatorMobiusAction where
  roots := #[`InfoGeometry.OperatorAlgebra.OperatorMobiusAction]

lean_lib ColimitBracketTransport where
  roots := #[`InfoGeometry.OperatorAlgebra.ColimitBracketTransport]

lean_lib Z2ProjectorWeights where
  roots := #[`InfoGeometry.OperatorAlgebra.Z2ProjectorWeights]

lean_lib EmergentComplexStructure where
  roots := #[`InfoGeometry.OperatorAlgebra.EmergentComplexStructure]

lean_lib ModularZ2CubeGrading where
  roots := #[`InfoGeometry.Canonical.ModularZ2CubeGrading]

lean_lib TomitaTakesakiInvolutions where
  roots := #[`InfoGeometry.Canonical.TomitaTakesakiInvolutions]

lean_lib HestenesBivectorCarrier where
  roots := #[`InfoGeometry.Canonical.HestenesBivectorCarrier]

lean_lib A2WeylPermutationAction where
  roots := #[`InfoGeometry.Canonical.A2WeylPermutationAction]

lean_lib CuntzMatrixCompatibleStateNet where
  roots := #[`InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet]

lean_lib KleinSixStateAssociatedBundle where
  roots := #[`InfoGeometry.Canonical.KleinSixStateAssociatedBundle]

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

lean_lib Cl55ProjectiveBoundary where
  roots := #[`InfoGeometry.Canonical.Cl55ProjectiveBoundary]

lean_lib ProjectiveAffineConformalClosure55 where
  roots := #[`InfoGeometry.Canonical.ProjectiveAffineConformalClosure55]

lean_lib Pin55ColimitAnomalyBridge where
  roots := #[`InfoGeometry.Canonical.Pin55ColimitAnomalyBridge]

lean_lib TopologicalKMSFlow where
  roots := #[`InfoGeometry.Canonical.TopologicalKMSFlow]

lean_lib HeisenbergDerivative where
  roots := #[`InfoGeometry.Canonical.HeisenbergDerivative]

lean_lib OperatorPin55Action where
  roots := #[`InfoGeometry.Canonical.OperatorPin55Action]

lean_lib OperatorTKKAnomalyAnnihilation where
  roots := #[`InfoGeometry.Canonical.OperatorTKKAnomalyAnnihilation]

-- Focused canonical owners also have independent Lake gates.  These roots are
-- intentionally kept separate from the broad `InfoGeometryCanonical` bundle
-- so their kernel checks can be replayed without rebuilding the umbrella.
lean_lib SplitOctonionKleinFourTriality where
  roots := #[`InfoGeometry.Canonical.SplitOctonionKleinFourTriality]

lean_lib D4Incidence where
  roots := #[`InfoGeometry.Canonical.D4Incidence]

lean_lib PauliJungTrialityD4Synthesis where
  roots := #[`InfoGeometry.Canonical.PauliJungTrialityD4Synthesis]

lean_lib TriColorModularBoundaryFlow where
  roots := #[`InfoGeometry.Canonical.TriColorModularBoundaryFlow]

lean_lib ZornVectorMatrixMobiusAction where
  roots := #[`InfoGeometry.Canonical.ZornVectorMatrixMöbiusAction]

lean_lib LocalZornProjectiveAction where
  roots := #[`InfoGeometry.Canonical.LocalZornProjectiveAction]

lean_lib HestenesPauliSheet where
  roots := #[`InfoGeometry.Canonical.ChiralStokesPauliBasis,
    `InfoGeometry.Canonical.HestenesPauliSheetBridge,
    `InfoGeometry.Canonical.HestenesDiracAdjoint]

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

lean_lib Clifford55QuadraticSpinAction where
  roots := #[`InfoGeometry.Clifford.Cl55QuadraticSpinAction]

lean_lib DiracLorentzQuadraticAction where
  roots := #[`InfoGeometry.Clifford.DiracLorentzQuadraticAction]

lean_lib Cl55CAROperatorLift where
  roots := #[`InfoGeometry.Clifford.Cl55CAROperatorLift]

lean_lib Cl55SpinOperatorConnection where
  roots := #[`InfoGeometry.Clifford.Cl55SpinOperatorConnection]

lean_lib Cl55CAROperatorTransport where
  roots := #[`InfoGeometry.Clifford.Cl55CAROperatorTransport]

lean_lib AffineOrthogonal55Semidirect where
  roots := #[`InfoGeometry.Canonical.AffineOrthogonal55Semidirect]

lean_lib Orthogonal55Components where
  roots := #[`InfoGeometry.Canonical.Orthogonal55Components]

lean_lib OrthogonalGroup55 where
  roots := #[`InfoGeometry.Canonical.OrthogonalGroup55]

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

lean_lib SplitOctonionHyperbolicSpectralProjectors where
  roots := #[`InfoGeometry.Canonical.SplitOctonionHyperbolicSpectralProjectors]

lean_lib Cl11ChiralOperatorProjectors where
  roots := #[`InfoGeometry.Physics.Cl11ChiralOperatorProjectors]

lean_lib SplitOctonionRegularOperators where
  roots := #[`InfoGeometry.Canonical.SplitOctonionRegularOperators]

lean_lib SplitOctonionRegularProjectors where
  roots := #[`InfoGeometry.Canonical.SplitOctonionRegularProjectors]

lean_lib SplitOctonionRegularNormOperators where
  roots := #[`InfoGeometry.Canonical.SplitOctonionRegularNormOperators]

lean_lib SplitOctonionAlternativeLaws where
  roots := #[`InfoGeometry.Canonical.SplitOctonionAlternativeLaws]

lean_lib SplitOctonionLoxodromicCircularBridge where
  roots := #[`InfoGeometry.Canonical.SplitOctonionLoxodromicCircularBridge]

lean_lib SplitOctonionRegularEllipticOperators where
  roots := #[`InfoGeometry.Canonical.SplitOctonionRegularEllipticOperators]

lean_lib SplitOctonionDoubledLoxodromic where
  roots := #[`InfoGeometry.Canonical.SplitOctonionDoubledLoxodromic]

lean_lib SplitOctonionRegularParabolicOperators where
  roots := #[`InfoGeometry.Canonical.SplitOctonionRegularParabolicOperators]

lean_lib Cl11SplitQuaternionMobiusBridge where
  roots := #[`InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge]

lean_lib QutritMobiusTripotentOrientationBridge where
  roots := #[`InfoGeometry.Quantum.QutritMobiusTripotentOrientationBridge]

lean_lib TwelveFoldExplicitOperators where
  roots := #[`InfoGeometry.Canonical.TwelveFoldExplicitOperators]

lean_lib TwelveFoldArithmeticNative where
  roots := #[`InfoGeometry.Canonical.TwelveFoldArithmeticNative]

lean_lib TwelveFoldGaloisCharacterSets where
  roots := #[`InfoGeometry.Canonical.TwelveFoldGaloisCharacterSets]

lean_lib TwelveFoldGaloisPowerAction where
  roots := #[`InfoGeometry.Canonical.TwelveFoldGaloisPowerAction]

lean_lib TwelveFoldCyclotomicNative where
  roots := #[`InfoGeometry.Canonical.TwelveFoldCyclotomicNative]

lean_lib TwelveFoldAdditiveCharacter where
  roots := #[`InfoGeometry.Canonical.TwelveFoldAdditiveCharacter]

lean_lib TwelveFoldDirichletCharacters where
  roots := #[`InfoGeometry.Canonical.TwelveFoldDirichletCharacters]

lean_lib TwelveFoldCircleCyclotomic where
  roots := #[`InfoGeometry.Canonical.TwelveFoldCircleCyclotomic]

lean_lib TwelveFoldGaussSum where
  roots := #[`InfoGeometry.Canonical.TwelveFoldGaussSum]

lean_lib SixStateGeneralizedCliffordAlgebra where
  roots := #[`InfoGeometry.Canonical.SixStateGeneralizedCliffordAlgebra]

lean_lib SixStateWeylReflection where
  roots := #[`InfoGeometry.Canonical.SixStateWeylReflection]

lean_lib TwelveFoldGeneralizedCliffordExtension where
  roots := #[`InfoGeometry.Canonical.TwelveFoldGeneralizedCliffordExtension]

lean_lib TwelveFoldMasterCharpoly where
  roots := #[`InfoGeometry.Canonical.TwelveFoldMasterCharpoly]

lean_lib TwelveFoldCyclotomicBridge where
  roots := #[`InfoGeometry.Canonical.TwelveFoldCyclotomicBridge]

lean_lib TwelveFoldProjectiveReflection where
  roots := #[`InfoGeometry.Canonical.TwelveFoldProjectiveReflection]

lean_lib SixStateShiftHierarchy where
  roots := #[`InfoGeometry.Canonical.SixStateShiftHierarchy]

lean_lib A2QutritTransitionRootBridge where
  roots := #[`InfoGeometry.Canonical.A2QutritTransitionRootBridge]

lean_lib QutritFourierBasisChange where
  roots := #[`InfoGeometry.Canonical.QutritFourierBasisChange]

lean_lib TwelveFoldCyclicGroupStructure where
  roots := #[`InfoGeometry.Canonical.TwelveFoldCyclicGroupStructure]

lean_lib QutritWeylOperatorBasis where
  roots := #[`InfoGeometry.Canonical.QutritWeylOperatorBasis]

lean_lib QutritGellMannOperatorBasis where
  roots := #[`InfoGeometry.Canonical.QutritGellMannOperatorBasis]

lean_lib QutritGellMannCasimir where
  roots := #[`InfoGeometry.Canonical.QutritGellMannCasimir]

lean_lib QutritGellMannFierz where
  roots := #[`InfoGeometry.Canonical.QutritGellMannFierz]

lean_lib QutritLieJordanCoordinateLayer where
  roots := #[`InfoGeometry.Canonical.QutritLieJordanCoordinateLayer]

lean_lib QutritGellMannBasis where
  roots := #[`InfoGeometry.Canonical.QutritGellMannBasis]

lean_lib QutritGellMannRootCoordinates where
  roots := #[`InfoGeometry.Canonical.QutritGellMannRootCoordinates]

lean_lib QutritWeylCommutingLines where
  roots := #[`InfoGeometry.Canonical.QutritWeylCommutingLines]


lean_lib StokesQutritChannelBasis where
  roots := #[`InfoGeometry.Canonical.StokesQutritChannelBasis]

lean_lib StokesGellMannChannelBasis where
  roots := #[`InfoGeometry.Canonical.StokesGellMannChannelBasis]

lean_lib QutritPositiveCone where
  roots := #[`InfoGeometry.Canonical.QutritPositiveCone]

lean_lib A2QutritWeylAdjoint where
  roots := #[`InfoGeometry.Canonical.A2QutritWeylAdjoint]

lean_lib KleinSixStateC12Compatibility where
  roots := #[`InfoGeometry.Canonical.KleinSixStateC12Compatibility]

lean_lib KleinUnitaryLiftAssociatedBundle where
  roots := #[`InfoGeometry.Canonical.KleinUnitaryLiftAssociatedBundle]

lean_lib KleinUnitaryOperatorIntertwining where
  roots := #[`InfoGeometry.Canonical.KleinUnitaryOperatorIntertwining]

lean_lib CuntzCantorKMSColimitBridge where
  roots := #[`InfoGeometry.Categorical.CuntzCantorKMSColimitBridge]

lean_lib CuntzMatrixAlgebraicStarColimit where
  roots := #[`InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit]

lean_lib CuntzMatrixAlgebraicTraceFunctional where
  roots := #[`InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional]

lean_lib CuntzMatrixTraceModularInvariance where
  roots := #[`InfoGeometry.Canonical.CuntzMatrixTraceModularInvariance]

lean_lib AlgebraicKMSStateColimit where
  roots := #[`InfoGeometry.Canonical.AlgebraicKMSStateColimit]

lean_lib RindlerChiralLoxodromicBridge where
  roots := #[`InfoGeometry.Canonical.RindlerChiralLoxodromicBridge]


lean_lib CuntzMatrixStarColimitState where
  roots := #[`InfoGeometry.Canonical.CuntzMatrixStarColimitState]

lean_lib FiniteGibbsState where
  roots := #[`InfoGeometry.Canonical.FiniteGibbsState]

lean_lib FiniteMatrixGibbsFunctional where
  roots := #[`InfoGeometry.Canonical.FiniteMatrixGibbsFunctional]

lean_lib CuntzMatrixZeroHamiltonianGibbs where
  roots := #[`InfoGeometry.Canonical.CuntzMatrixZeroHamiltonianGibbs]

lean_lib FiniteThermalTraceState where
  roots := #[`InfoGeometry.Canonical.FiniteThermalTraceState]

lean_lib AlgebraicStarEnvelope where
  roots := #[`InfoGeometry.Canonical.AlgebraicStarEnvelope]

lean_lib CuntzAlgebraicStarEnvelope where
  roots := #[`InfoGeometry.Canonical.CuntzAlgebraicStarEnvelope]

lean_lib FilteredGNSFaithfulAlgebraicQuotient where
  roots := #[`InfoGeometry.Canonical.FilteredGNSFaithfulAlgebraicQuotient]

lean_lib FilteredGNSFaithfulCStarRepresentation where
  roots := #[`InfoGeometry.Canonical.FilteredGNSFaithfulCStarRepresentation]

lean_lib FilteredGNSNormPullbackBinding where
  roots := #[`InfoGeometry.Canonical.FilteredGNSNormPullbackBinding]

lean_lib ModularFlowIsometry where
  roots := #[`InfoGeometry.Canonical.ModularFlowIsometry]

lean_lib FilteredGNSCompletionKMSState where
  roots := #[`InfoGeometry.Canonical.FilteredGNSCompletionKMSState]

lean_lib OperatorFierzReadoutCorrespondence where
  roots := #[`InfoGeometry.Canonical.OperatorFierzReadoutCorrespondence]

lean_lib ModularFlowGeneratorDerivative where
  roots := #[`InfoGeometry.Canonical.ModularFlowGeneratorDerivative]

lean_lib ModularFlowExponentialGenerator where
  roots := #[`InfoGeometry.Canonical.ModularFlowExponentialGenerator]



lean_lib SplitOctonionConjugation where
  roots := #[`InfoGeometry.Canonical.SplitOctonionConjugation]

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
