"""Tests for source-first refactoring-map evidence and uncertainty boundaries."""

import hashlib
import json
import os
import subprocess
import tempfile
import unittest
from types import SimpleNamespace
from pathlib import Path
from unittest.mock import patch

from tools.repository_evolution import refactoring_map as refactoring_map_owner
from tools.repository_evolution.refactoring_map import (
    build_refactoring_map,
    _compiler_fingerprint_summaries,
    classify_file,
    graph_topology,
    _owner_membership_summary,
    _lake_package_targets,
    lean_module_index,
    parse_lake_targets,
)
from tools.infra.evolution_extract import aggregate_current_path_lineage


class RefactoringMapTests(unittest.TestCase):
    def test_selected_python_scan_excludes_unrelated_edges_and_marks_boundary(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tests").mkdir()
            (root / "tests/test_selected.py").write_text("import worker\n")
            graph = SimpleNamespace(records={}, import_graph={
                "tests/test_selected.py": {"tools/worker.py"},
                "tools/unrelated.py": {"tools/other.py"},
            })
            with patch.object(refactoring_map_owner, "_python_graph", return_value=graph):
                report = build_refactoring_map(root, paths=["tests/test_selected.py"])
        edges = report["dependencyEdges"]
        self.assertEqual(len(edges), 2)
        self.assertEqual({edge["from"] for edge in edges}, {"tests/test_selected.py"})
        self.assertEqual({edge["status"] for edge in edges}, {
            "static_import_candidate_outside_inventory",
            "static_test_dependency_outside_inventory",
        })

    def test_compiler_fingerprints_join_only_with_source_olean_and_export_hashes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            index = root / "index"
            index.mkdir()
            decls = index / "decls.jsonl"
            edges = index / "edges.jsonl"
            declaration_rows = [{
                "name": "Root.sample",
                "kind": "theorem",
                "relFile": "lean/Root.lean",
                "typeDigest": {"algorithmVersion": "lean-expr-debruijn-v4",
                               "digest": "abc", "openTerm": False},
                "valueDigest": {"algorithmVersion": "lean-expr-debruijn-v4",
                                "digest": "def", "openTerm": False},
            }, {
                "name": "Other.sample",
                "kind": "theorem",
                "module": "Other",
                "relFile": "lean/Other.lean",
                "typeDigest": {"algorithmVersion": "lean-expr-debruijn-v4",
                               "digest": "abc", "openTerm": False},
                "valueDigest": None,
            }]
            decls.write_text("".join(json.dumps(row) + "\n" for row in declaration_rows),
                             encoding="utf-8")
            edges.write_text("", encoding="utf-8")
            digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
            meta = {
                "schemaVersion": 3,
                "nodeCount": 2,
                "edgeCount": 0,
                "sourceHash": "source-current",
                "oleanHash": "olean-current",
                "outputHashAlgorithm": "sha256",
                "outputHashes": {"decls.jsonl": digest(decls), "edges.jsonl": digest(edges)},
                "importRoot": "Root",
                "nsFilter": "Root",
            }
            meta_path = index / "meta.json"
            meta_path.write_text(json.dumps(meta), encoding="utf-8")
            with patch("tools.infra.build.compute_lean_source_hash", return_value="source-current"), \
                 patch("tools.infra.build.compute_olean_content_hash", return_value="olean-current"):
                evidence, per_file = _compiler_fingerprint_summaries(root, meta_path, meta)

        self.assertEqual(evidence["status"], "source_olean_and_export_hashes_verified")
        self.assertEqual(evidence["declarationCount"], 2)
        self.assertEqual(per_file["lean/Root.lean"]["declarationCount"], 1)
        self.assertEqual(per_file["lean/Root.lean"]["uniqueTypeDigestCount"], 1)
        cohort = evidence["crossFileExactTypeDigestCohorts"][0]
        self.assertEqual(cohort["sourceFiles"], ["lean/Other.lean", "lean/Root.lean"])
        self.assertEqual({row["declaration"] for row in cohort["declarationWitnesses"]},
                         {"Other.sample", "Root.sample"})

    def test_compiler_fingerprint_export_tampering_prevents_join(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            index = root / "index"
            index.mkdir()
            (index / "decls.jsonl").write_text("{}\n", encoding="utf-8")
            (index / "edges.jsonl").write_text("", encoding="utf-8")
            meta = {
                "schemaVersion": 3,
                "sourceHash": "source-current",
                "oleanHash": "olean-current",
                "outputHashAlgorithm": "sha256",
                "outputHashes": {"decls.jsonl": "wrong", "edges.jsonl": "wrong"},
            }
            meta_path = index / "meta.json"
            meta_path.write_text(json.dumps(meta), encoding="utf-8")
            with patch("tools.infra.build.compute_lean_source_hash", return_value="source-current"), \
                 patch("tools.infra.build.compute_olean_content_hash", return_value="olean-current"):
                evidence, per_file = _compiler_fingerprint_summaries(root, meta_path, meta)

        self.assertEqual(evidence["status"], "export_hash_mismatch_do_not_join")
        self.assertEqual(evidence["mismatchedArtifact"], "decls.jsonl")
        self.assertEqual(per_file, {})

    def test_map_attaches_verified_compiler_summary_to_current_source_file(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean").mkdir()
            (root / "lakefile.lean").write_text(
                'package sample where\n  srcDir := "lean"\n'
                'lean_lib Root where\n  root := `Root\n', encoding="utf-8"
            )
            (root / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
            (root / "lean/Root.lean").write_text("theorem sample : True := True.intro\n",
                                                   encoding="utf-8")
            index = root / "index"
            index.mkdir()
            decls = index / "decls.jsonl"
            edges = index / "edges.jsonl"
            decls.write_text(json.dumps({
                "name": "Root.sample",
                "kind": "theorem",
                "relFile": "lean/Root.lean",
                "typeDigest": {"algorithmVersion": "lean-expr-debruijn-v4",
                               "digest": "abc", "openTerm": False},
                "valueDigest": None,
            }) + "\n", encoding="utf-8")
            edges.write_text("", encoding="utf-8")
            meta = {
                "schemaVersion": 3,
                "nodeCount": 1,
                "edgeCount": 0,
                "sourceHash": "source-current",
                "oleanHash": "olean-current",
                "outputHashAlgorithm": "sha256",
                "outputHashes": {
                    "decls.jsonl": hashlib.sha256(decls.read_bytes()).hexdigest(),
                    "edges.jsonl": hashlib.sha256(edges.read_bytes()).hexdigest(),
                },
                "importRoot": "Root",
                "nsFilter": "Root",
            }
            meta_path = index / "meta.json"
            meta_path.write_text(json.dumps(meta), encoding="utf-8")
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            subprocess.run(["git", "config", "user.name", "Test"], cwd=root, check=True)
            subprocess.run(["git", "config", "user.email", "test@example.invalid"], cwd=root, check=True)
            subprocess.run(["git", "add", "lakefile.lean", "lake-manifest.json",
                            "lean/Root.lean"], cwd=root, check=True)
            subprocess.run(["git", "commit", "-qm", "current source fossil"], cwd=root, check=True)
            with patch("tools.infra.build.compute_lean_source_hash", return_value="source-current"), \
                 patch("tools.infra.build.compute_olean_content_hash", return_value="olean-current"):
                report = build_refactoring_map(
                    root, paths=["lakefile.lean", "lean/Root.lean"],
                    python_scan=False, git_history=True, compiler_meta=meta_path,
                )

        source = next(row for row in report["files"] if row["path"] == "lean/Root.lean")
        self.assertEqual(source["compilerFingerprints"]["declarationCount"], 1)
        self.assertEqual(report["summary"]["compilerFingerprintJoinedFileCount"], 1)
        self.assertEqual(report["summary"]["currentDnaToFossilPathJoinCount"], 1)
        self.assertEqual(report["compilerArtifactEvidence"]["joinStatus"],
                         "verified_fingerprint_rows_joined_by_source_file")
        self.assertEqual(source["evolutionaryLineage"]["status"],
                         "current_fingerprint_joined_to_path_fossils")
        self.assertEqual(source["evolutionaryLineage"]["relation"],
                         "path_continuity_candidate_not_historical_content_identity")

    def test_overlapping_lake_owners_count_as_memberships_not_pseudo_owners(self):
        summary = _owner_membership_summary([
            {"owner": ["Root", "Root.Tests"],
             "ownerStatus": "ambiguous_multiple_lake_roots"},
            {"owner": "Root"},
            {"owner": "unresolved_lean_build_owner",
             "ownerStatus": "uncertain_no_root_reachability"},
        ])
        self.assertEqual(summary, {
            "ownerCount": 2,
            "largestOwnerGroups": {
                "Root": 2,
                "Root.Tests": 1,
            },
            "ownerMembershipCount": 3,
            "ambiguousOwnerArtifactCount": 1,
            "unresolvedOwnerArtifactCount": 1,
        })

    def test_path_roles_are_explicitly_evidence_labeled(self):
        self.assertEqual(classify_file("lean/InfoGeometry/A.lean")["role"], "lean_source")
        self.assertEqual(
            classify_file("external_refs/example/Main.lean"),
            {"role": "external_reference", "status": "path_observed",
             "owner": "external_ref_boundary"},
        )
        self.assertEqual(classify_file("mystery/widget.rs")["status"], "uncertain")

    def test_repository_evolution_components_are_finer_than_the_directory_role(self):
        manifest = classify_file("tools/repository_evolution/generation_manifest.py")
        self.assertEqual(manifest["role"], "repository_evolution_analysis")
        self.assertEqual(manifest["component"], "source_generation_provenance")
        self.assertEqual(manifest["componentStatus"], "repo_entrypoint_role_reviewed")
        unknown = classify_file("tools/repository_evolution/future_module.py")
        self.assertEqual(unknown["component"], "unclassified_evolution_subsystem")
        self.assertEqual(unknown["componentStatus"], "uncertain_unmapped_entrypoint")

    def test_scoped_map_reports_evolution_component_counts(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "tools/repository_evolution/generation_manifest.py"
            source.parent.mkdir(parents=True)
            source.write_text("def main():\n    return 0\n", encoding="utf-8")
            report = build_refactoring_map(
                root, paths=["tools/repository_evolution/generation_manifest.py"],
                python_scan=False,
            )

        self.assertTrue(report["sourceSnapshot"]["worktreeConsistentDuringScan"])
        self.assertEqual(report["sourceSnapshot"]["changedPathsDuringScan"], [])
        self.assertEqual(
            report["sourceSnapshot"]["changedPathSetSha256"],
            hashlib.sha256(b"[]").hexdigest(),
        )
        self.assertEqual(report["summary"]["componentCounts"], {
            "source_generation_provenance": 1,
        })

    def test_known_root_language_and_tooling_boundaries_precede_generic_lean_fallback(self):
        self.assertEqual(classify_file("tools/infra/axiom_index.lean")["role"],
                         "infrastructure_tool")
        self.assertEqual(classify_file("tools/quality/Header.lean")["role"],
                         "quality_gate_or_audit")
        self.assertEqual(classify_file("scripts/Atomizer.lean")["role"],
                         "operational_script")
        self.assertEqual(classify_file("python/birkhoff_routing_sympy.py")["role"],
                         "formalization_support_artifact")
        self.assertEqual(classify_file("sage/birkhoff_routing.sage")["status"],
                         "source_observed_verification_unchecked")
        self.assertEqual(classify_file("pi-omega-extension/index.ts")["role"],
                         "agent_or_app_extension")
        self.assertEqual(classify_file("migrations/identity_v1.js")["role"],
                         "database_migration_source")
        self.assertEqual(classify_file("jsonschema_shadow/validators.py"), {
            "role": "repository_source_candidate",
            "status": "path_observed_owner_uncertain",
            "owner": "jsonschema_shadow",
        })
        self.assertEqual(classify_file("lib/InfoGeometryCore/lakefile.lean")["role"],
                         "build_or_package_configuration")
        self.assertEqual(classify_file("verification/spinorial-core/lakefile.lean")["role"],
                         "build_or_package_configuration")
        self.assertEqual(classify_file("lean/DAG/README.md")["role"],
                         "documentation_or_agent_contract")
        self.assertEqual(classify_file("lean/DAG/ingest.py"), {
            "role": "repository_source_candidate",
            "status": "path_observed_owner_uncertain",
            "owner": "lean/DAG",
        })

    def test_known_source_boundaries_are_separate_from_proof_status(self):
        recovery = classify_file(
            "tools/multisystem/major_restore_non_overwriting/lean/InfoGeometry/Recovered/CliffordMatrixBridge.lean"
        )
        self.assertEqual(recovery["role"], "sandbox_or_historical_candidate")
        self.assertEqual(recovery["status"], "path_observed_uncertain_scope")
        self.assertEqual(
            classify_file("backend/cuda/eigen/Eigen/Core/Matrix.h"),
            {"role": "vendored_dependency_source",
             "status": "path_and_license_observed",
             "owner": "backend/cuda/eigen"},
        )
        self.assertEqual(classify_file("backend/cuda/twistor_isp.py")["role"],
                         "gpu_backend_source")
        proof = classify_file("proofs/OperatorIdentity.py")
        self.assertEqual(proof["role"], "formalization_support_artifact")
        self.assertEqual(proof["status"], "path_observed_not_proof_validation")
        self.assertEqual(classify_file(
            "proofs/antigravity-sdk-python/google/agent.py")["role"],
            "vendored_or_external_reference")
        self.assertEqual(classify_file("src/igf/config/env_aliases.py")["owner"],
                         "src.igf")
        self.assertEqual(classify_file(".spectral-sandbox/Locality.lean")["role"],
                         "sandbox_or_historical_candidate")

    def test_lake_parser_extracts_roots_and_exact_glob_kinds(self):
        lakefile = '''
package test where
  srcDir := "lean"

lean_lib Root where
  roots := #[`Root, `Extra]

lean_exe checker where
  root := `Checker
  srcDir := "../tests"
lean_lib Graph where
  globs := #[.andSubmodules `Graph]
lean_lib Standalone where
  roots := #[]
  globs := #[`B3PresentedGroup, `lean.InfoGeometry.Spectral.Spectrum.Basic,
            .submodules `Other]
/-! Following prose mentions `fake.Module and `external/path.lean. -/
require fake from "fake"
'''
        targets = parse_lake_targets(lakefile, Path("."))
        self.assertEqual([item["name"] for item in targets],
                         ["Root", "checker", "Graph", "Standalone"])
        self.assertEqual(targets[0]["roots"], ["Root", "Extra"])
        self.assertEqual(targets[1]["sourceDir"], "../tests")
        self.assertEqual(targets[1]["roots"], ["Checker"])
        self.assertEqual(targets[2]["globs"], [{
            "module": "Graph", "includeSelf": True,
            "includeSubmodules": True, "globKind": "andSubmodules",
        }])
        self.assertEqual(targets[3]["roots"], [])
        self.assertEqual(targets[3]["rootParseStatus"], "complete_static_parse")
        self.assertEqual(targets[3]["globParseStatus"], "complete_static_parse")
        self.assertEqual(targets[3]["globs"], [
            {"module": "B3PresentedGroup", "includeSelf": True,
             "includeSubmodules": False, "globKind": "one"},
            {"module": "lean.InfoGeometry.Spectral.Spectrum.Basic",
             "includeSelf": True, "includeSubmodules": False, "globKind": "one"},
            {"module": "Other", "includeSelf": False,
             "includeSubmodules": True, "globKind": "submodules"},
        ])

    def test_lake_target_globs_stop_at_array_boundary_and_ignore_comment_text(self):
        lakefile = '''
package test where
  srcDir := "lean"
lean_lib Root where
  roots := #[]
  globs := #[`Root]
/-! Fake references `fake.Module and `outside/path.lean must not leak. -/
require dependency from "dependency"
lean_lib Next where
  globs := #[.andSubmodules `Next]
'''
        targets = parse_lake_targets(lakefile, Path("."))
        self.assertEqual(targets[0]["globs"], [{
            "module": "Root", "includeSelf": True,
            "includeSubmodules": False, "globKind": "one",
        }])
        self.assertEqual(targets[1]["globs"], [{
            "module": "Next", "includeSelf": True,
            "includeSubmodules": True, "globKind": "andSubmodules",
        }])

    def test_lake_parser_marks_unrecognized_glob_syntax_incomplete(self):
        lakefile = '''
lean_lib Dynamic where
  roots := #[]
  globs := #[.submodules .anonymous]
'''
        target = parse_lake_targets(lakefile, Path("."))[0]
        self.assertEqual(target["globs"], [])
        self.assertEqual(target["globParseStatus"], "partial_static_parse")
        self.assertEqual(target["globParseRemainder"], ".submodules.anonymous")

    def test_compiler_source_hash_failure_preserves_actionable_reason(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lakefile.lean").write_text(
                'package sample where\n  srcDir := "lean"\n', encoding="utf-8"
            )
            meta = root / "meta.json"
            meta.write_text(json.dumps({"sourceHash": "old"}), encoding="utf-8")
            with patch(
                "tools.infra.build.compute_lean_source_hash",
                side_effect=RuntimeError("source files changed while hashing sources"),
            ):
                report = build_refactoring_map(
                    root, paths=["lakefile.lean"], python_scan=False,
                    git_history=False, compiler_meta=meta,
                )
        self.assertEqual(
            report["compilerArtifactEvidence"]["sourceCheckError"],
            "RuntimeError: source files changed while hashing sources",
        )
        self.assertEqual(report["compilerArtifactEvidence"]["status"],
                         "source_binding_unavailable")

    def test_exact_lake_globs_do_not_select_child_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean/Standalone").mkdir(parents=True)
            for rel in ("lean/Standalone.lean", "lean/Standalone/Child.lean"):
                (root / rel).write_text("theorem ok : True := True.intro\n", encoding="utf-8")
            (root / "lakefile.lean").write_text(
                'package sample where\n  srcDir := "lean"\n'
                'lean_lib Standalone where\n  roots := #[]\n'
                '  globs := #[`Standalone]\n', encoding="utf-8"
            )
            targets = _lake_package_targets(root, ["lakefile.lean"])
            modules, _, _ = lean_module_index(
                root, ["lean/Standalone.lean", "lean/Standalone/Child.lean"],
                targets, "lean",
            )
        self.assertIn("Standalone", modules)
        self.assertNotIn("Standalone.Child", modules)

    def test_lake_target_reports_a_missing_declared_source_root(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean").mkdir()
            (root / "lakefile.lean").write_text(
                'package sample where\n  srcDir := "lean"\n'
                'lean_lib OAI where\n'
                '  srcDir := "../external_refs/openai-math/lean"\n'
                '  roots := #[`OAI.GroupTheory.BooneHigman.TwistedSimplicity]\n',
                encoding="utf-8",
            )

            targets = _lake_package_targets(root, ["lakefile.lean"])
            report = build_refactoring_map(
                root, paths=["lakefile.lean"], python_scan=False,
                git_history=False, compiler_meta=root / "missing-meta.json",
            )

        self.assertEqual(len(targets), 1)
        self.assertEqual(targets[0]["sourceRootStatus"],
                         "declared_source_root_missing")
        self.assertEqual(targets[0]["sourceRoot"],
                         "external_refs/openai-math/lean")
        self.assertEqual(report["summary"]["missingLakeSourceRootCount"], 1)
        self.assertEqual(report["summary"]["missingLakeSourceRoots"], [{
            "packageName": "sample", "target": "OAI",
            "sourceRoot": "external_refs/openai-math/lean",
        }])

    def test_coarse_graph_counts_python_ast_and_test_edges(self):
        files = [
            {"path": "tools/infra/worker.py", "role": "infrastructure_tool", "owner": "tools.infra"},
            {"path": "tests/test_worker.py", "role": "test_or_fixture", "owner": "tests"},
        ]
        edges = [
            {"from": "tests/test_worker.py", "to": "tools/infra/worker.py", "kind": "python_import"},
            {"from": "tests/test_worker.py", "to": "tools/infra/worker.py", "kind": "test_import"},
        ]
        topology = graph_topology(files, edges, [])
        self.assertEqual(topology["typedEdgeCounts"], {"python_import": 1, "test_import": 1})
        test_group = next(group for group in topology["coarseGroups"] if group["id"] == "tests")
        self.assertEqual(test_group["outgoingBoundaryCounts"],
                         {"python_import": 1, "test_import": 1})
        tool_group = next(group for group in topology["coarseGroups"] if group["id"] == "tools/infra")
        self.assertEqual(tool_group["incomingBoundaryCounts"],
                         {"python_import": 1, "test_import": 1})

    def test_structural_cohorts_cross_lake_targets_and_keep_membership_evidence(self):
        files = [
            {"path": "lean/Alpha.lean", "role": "lean_source",
             "buildTargets": ["Alpha"]},
            {"path": "lean/Beta.lean", "role": "lean_source",
             "buildTargets": ["Beta", "Combined"]},
            {"path": "lean/Shared.lean", "role": "lean_source",
             "buildTargets": ["Alpha", "Beta", "Combined"]},
        ]
        edges = [
            {"from": "lean/Alpha.lean", "to": "lean/Shared.lean",
             "kind": "lean_source_import"},
            {"from": "lean/Beta.lean", "to": "lean/Shared.lean",
             "kind": "lean_source_import"},
        ]
        declarations = [
            {"sourcePath": "lean/Alpha.lean", "kind": "theorem"},
            {"sourcePath": "lean/Beta.lean", "kind": "theorem"},
        ]

        topology = graph_topology(files, edges, declarations)

        cohort = next(candidate for candidate in topology["structuralCohortCandidates"]
                      if candidate["members"] == ["lean/Alpha.lean", "lean/Beta.lean"])
        self.assertEqual(cohort["profile"], {
            "declarationKinds": {"theorem": 1},
            "repoImportOutDegree": 1,
            "typedDependencyCounts": {"lean_source_import": 1},
        })
        self.assertEqual(cohort["lakeTargetMemberships"], {
            "lean/Alpha.lean": ["Alpha"],
            "lean/Beta.lean": ["Beta", "Combined"],
        })

    def test_partial_inventory_preserves_known_repo_import_degree(self):
        files = [{"path": path, "role": "lean_source"}
                 for path in ("lean/Alpha.lean", "lean/Beta.lean")]
        edges = [{"from": row["path"], "to": "lean/Outside.lean",
                  "kind": "lean_source_import_outside_inventory"} for row in files]
        edges += [{"from": row["path"], "to": "Mathlib",
                   "kind": "lean_external_package_import"} for row in files]
        topology = graph_topology(files, edges, [])
        self.assertEqual(len(topology["structuralCohortCandidates"]), 1)
        profile = topology["structuralCohortCandidates"][0]["profile"]
        self.assertEqual(profile["repoImportOutDegree"], 1)
        self.assertEqual(profile["typedDependencyCounts"], {
            "lean_source_import_outside_inventory": 1,
            "lean_external_package_import": 1,
        })

    def test_two_hop_typed_neighborhood_refines_a_one_hop_match(self):
        paths = ["Alpha", "Beta", "Left", "Right", "Leaf"]
        files = [{
            "path": f"lean/{path}.lean",
            "role": "lean_source",
            "buildTargets": [path],
        } for path in paths]
        edges = [
            {"from": "lean/Alpha.lean", "to": "lean/Left.lean",
             "kind": "lean_source_import"},
            {"from": "lean/Beta.lean", "to": "lean/Right.lean",
             "kind": "lean_source_import"},
            {"from": "lean/Left.lean", "to": "lean/Leaf.lean",
             "kind": "lean_external_package_import"},
        ]
        declarations = [
            {"sourcePath": "lean/Alpha.lean", "kind": "theorem"},
            {"sourcePath": "lean/Beta.lean", "kind": "theorem"},
        ]

        topology = graph_topology(files, edges, declarations)

        one_hop = [candidate for candidate in topology["neighborhoodCohortCandidates"]
                   if candidate["depth"] == 1]
        two_hop = [candidate for candidate in topology["neighborhoodCohortCandidates"]
                   if candidate["depth"] == 2]
        self.assertTrue(any(candidate["members"] ==
                            ["lean/Alpha.lean", "lean/Beta.lean"]
                            for candidate in one_hop))
        self.assertFalse(any(candidate["members"] ==
                             ["lean/Alpha.lean", "lean/Beta.lean"]
                             for candidate in two_hop))

    def test_neighborhood_fingerprint_retains_external_package_identity(self):
        files = [
            {"path": "lean/Alpha.lean", "role": "lean_source",
             "buildTargets": ["Alpha"]},
            {"path": "lean/Beta.lean", "role": "lean_source",
             "buildTargets": ["Beta"]},
        ]
        edges = [
            {"from": "lean/Alpha.lean", "to": ".lake/packages/mathlib/Mathlib/A.lean",
             "kind": "lean_external_package_import", "dependencyPackage": "mathlib",
             "importedModule": "Mathlib.Algebra.Group.Defs"},
            {"from": "lean/Beta.lean", "to": ".lake/packages/batteries/Batteries/A.lean",
             "kind": "lean_external_package_import", "dependencyPackage": "batteries",
             "importedModule": "Batteries.Data.List.Basic"},
        ]
        declarations = [
            {"sourcePath": "lean/Alpha.lean", "kind": "theorem"},
            {"sourcePath": "lean/Beta.lean", "kind": "theorem"},
        ]

        topology = graph_topology(files, edges, declarations)
        one_hop = [candidate for candidate in topology["neighborhoodCohortCandidates"]
                   if candidate["depth"] == 1]

        self.assertFalse(any(candidate["members"] ==
                             ["lean/Alpha.lean", "lean/Beta.lean"]
                             for candidate in one_hop))

    def test_git_path_fossils_follow_renames_without_copying_revisions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess_run = subprocess.run
            subprocess_run(["git", "init", "-q"], cwd=root, check=True)
            subprocess_run(["git", "config", "user.name", "Test"], cwd=root, check=True)
            subprocess_run(["git", "config", "user.email", "test@example.invalid"], cwd=root, check=True)

            source = root / "src/A.lean"
            source.parent.mkdir()
            source.write_text("def first := 1\n", encoding="utf-8")
            subprocess_run(["git", "add", "src/A.lean"], cwd=root, check=True)
            subprocess_run(["git", "commit", "-qm", "add source"], cwd=root, check=True)

            source.write_text("def first := 2\n", encoding="utf-8")
            subprocess_run(["git", "add", "src/A.lean"], cwd=root, check=True)
            subprocess_run(["git", "commit", "-qm", "change source"], cwd=root, check=True)

            destination = root / "src/B.lean"
            source.rename(destination)
            subprocess_run(["git", "add", "-A"], cwd=root, check=True)
            subprocess_run(["git", "commit", "-qm", "rename source"], cwd=root, check=True)

            events = []
            history = aggregate_current_path_lineage(
                root, ["src/B.lean", "src/missing.lean"], event_callback=events.append
            )

        current = history["src/B.lean"]
        self.assertEqual(current["touchCount"], 3)
        self.assertEqual(current["changeTypes"], {"A": 1, "M": 1, "R": 1})
        self.assertEqual(current["renamedFromPathSample"], ["src/A.lean"])
        self.assertEqual(current["status"], "path_continuity_candidate_not_content_identity")
        self.assertTrue(all(event["artifactPath"] == "src/B.lean" for event in events))
        self.assertEqual(len(events), 3)
        self.assertIn("R", [event["changeType"] for event in events])
        self.assertEqual(events[-1]["historyRevision"], current["historyRevision"])
        self.assertEqual(history["src/missing.lean"]["status"],
                         "no_path_event_found_in_revision_scope")

    def test_map_joins_current_source_dependencies_and_keeps_cache_unjoined(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean/Root").mkdir(parents=True)
            (root / "lean/Root.lean").write_text("import Root.Dependency\n", encoding="utf-8")
            (root / "lean/Root/Dependency.lean").write_text(
                "namespace Root\ntheorem sample : True := True.intro\nend Root\n", encoding="utf-8"
            )
            (root / "lakefile.lean").write_text(
                'package test where\n  srcDir := "lean"\n\n'
                'lean_lib Root where\n  root := `Root\n', encoding="utf-8"
            )
            meta = root / "meta.json"
            meta.write_text(json.dumps({"timestamp": "old", "sourceHash": "abc",
                                        "nodeCount": 7, "edgeCount": 9}), encoding="utf-8")
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            subprocess.run(["git", "config", "user.name", "Test"], cwd=root, check=True)
            subprocess.run(["git", "config", "user.email", "test@example.invalid"], cwd=root, check=True)
            subprocess.run(["git", "add", "lakefile.lean", "lean/Root.lean",
                            "lean/Root/Dependency.lean"], cwd=root, check=True)
            subprocess.run(["git", "commit", "-qm", "fixture source"], cwd=root, check=True)
            path_events = root / "tmp/path-events.jsonl"

            report = build_refactoring_map(
                root,
                paths=["lakefile.lean", "lean/Root.lean", "lean/Root/Dependency.lean"],
                python_scan=False,
                git_history=True,
                compiler_meta=meta,
                git_path_events_output=path_events,
            )

            fossil_events = [json.loads(line) for line in path_events.read_text().splitlines()]
            selected_events_path = root / "tmp/selected-path-events.jsonl"
            selected_report = build_refactoring_map(
                root,
                paths=["lakefile.lean", "lean/Root.lean", "lean/Root/Dependency.lean"],
                python_scan=False,
                git_history=True,
                compiler_meta=meta,
                git_path_events_output=selected_events_path,
                git_path_event_paths={"lean/Root.lean"},
            )
            selected_events = [json.loads(line) for line in selected_events_path.read_text().splitlines()]

        records = {row["path"]: row for row in report["files"]}
        self.assertEqual(records["lean/Root.lean"]["buildTargets"], ["Root"])
        self.assertEqual(records["lean/Root/Dependency.lean"]["buildTargets"], ["Root"])
        self.assertTrue(any(edge["from"] == "lean/Root.lean"
                            and edge["to"] == "lean/Root/Dependency.lean"
                            and edge["kind"] == "lean_source_import"
                            for edge in report["dependencyEdges"]))
        self.assertEqual(report["compilerArtifactEvidence"]["status"],
                         "stale_source_generation")
        self.assertEqual(report["compilerArtifactEvidence"]["joinStatus"],
                         "source_hash_mismatch_do_not_join")
        self.assertFalse(report["compilerArtifactEvidence"]["sourceHashMatchesCurrent"])
        self.assertEqual(report["sourceSnapshot"]["pathCount"], 3)
        self.assertEqual(report["sourceSnapshot"]["inventoryScope"], "explicit_path_selection")
        self.assertTrue(report["sourceSnapshot"]["worktreeConsistentDuringScan"])
        self.assertEqual(len(report["analysisProvenance"]["scannerSourceSha256"]), 64)
        self.assertFalse(report["analysisProvenance"]["analysisInputsConsistentDuringScan"])
        self.assertIsNone(report["analysisProvenance"]["lakeManifestSha256"])
        self.assertEqual(report["gitPathHistory"]["status"], "path_history_candidate")
        self.assertEqual(report["gitPathHistory"]["revision"], report["sourceSnapshot"]["gitHead"])
        self.assertEqual(report["gitPathHistory"]["eventStreamCount"], len(fossil_events))
        self.assertTrue(all(event["historyRevision"] == report["sourceSnapshot"]["gitHead"]
                            for event in fossil_events))
        self.assertEqual({event["artifactPath"] for event in fossil_events},
                         {"lakefile.lean", "lean/Root.lean", "lean/Root/Dependency.lean"})
        self.assertEqual(len(selected_events), 1)
        self.assertEqual(selected_events[0]["artifactPath"], "lean/Root.lean")
        self.assertEqual(selected_report["gitPathHistory"]["eventStreamScope"], {
            "mode": "selected_current_paths", "artifactPaths": ["lean/Root.lean"]
        })
        self.assertEqual(records["lean/Root.lean"]["gitPathHistory"]["touchCount"], 1)
        self.assertEqual(records["lean/Root.lean"]["gitPathHistory"]["status"],
                         "path_continuity_candidate_not_content_identity")
        self.assertEqual(report["summary"]["leanDeclarationCandidateCount"], 1)
        declaration = report["leanDeclarationCandidates"][0]
        self.assertEqual(declaration["name"], "sample")
        self.assertEqual(declaration["namespaceContext"], "Root")
        self.assertEqual(declaration["buildTargets"], ["Root"])
        self.assertEqual(declaration["status"], "lexical_candidate_not_lean_parser_output")
        topology = report["topology"]
        root_group = next(group for group in topology["coarseGroups"] if group["id"] == "lake:Root")
        self.assertEqual(root_group["artifactCount"], 2)
        self.assertEqual(root_group["internalEdgeCounts"], {"lean_source_import": 1})
        self.assertEqual(topology["structuralCohortStatus"],
                         "candidate grouping only; not semantic archetype assignment")

    def test_lean_path_role_does_not_imply_lake_module_or_build_ownership(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            active = root / "lean/active"
            active.mkdir(parents=True)
            (active / "Root.lean").write_text(
                "theorem root_fact : True := True.intro\n", encoding="utf-8"
            )
            (root / "lean/Orphan.lean").write_text(
                "theorem orphan_fact : True := True.intro\n", encoding="utf-8"
            )
            (root / "lakefile.lean").write_text(
                'package test where\n  srcDir := "lean/active"\n\n'
                'lean_lib Root where\n  root := `Root\n', encoding="utf-8"
            )
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            subprocess.run(["git", "config", "user.name", "Test"], cwd=root, check=True)
            subprocess.run(["git", "config", "user.email", "test@example.invalid"],
                           cwd=root, check=True)
            subprocess.run(["git", "add", "lakefile.lean", "lean/active/Root.lean",
                            "lean/Orphan.lean"], cwd=root, check=True)
            subprocess.run(["git", "commit", "-qm", "fixture"], cwd=root, check=True)

            report = build_refactoring_map(
                root,
                paths=["lakefile.lean", "lean/active/Root.lean", "lean/Orphan.lean"],
                python_scan=False,
            )

        records = {row["path"]: row for row in report["files"]}
        self.assertEqual(records["lean/active/Root.lean"]["buildTargets"], ["Root"])
        self.assertEqual(records["lean/Orphan.lean"]["role"], "lean_source")
        self.assertEqual(records["lean/Orphan.lean"]["ownerStatus"],
                         "uncertain_module_not_in_lake_target_index")
        self.assertEqual(records["lean/Orphan.lean"]["status"],
                         "lake_module_index_unresolved")
        self.assertEqual(report["summary"]["unindexedLeanSourceCount"], 1)
        self.assertEqual(report["summary"]["uncertainBuildOwnershipCount"], 1)

    def test_unindexed_lean_source_imports_remain_in_the_dependency_graph(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean").mkdir()
            (root / "lean/Root.lean").write_text(
                "theorem root_fact : True := True.intro\n", encoding="utf-8"
            )
            (root / "lean/Standalone.lean").write_text(
                "import Root\ntheorem standalone_fact : True := root_fact\n",
                encoding="utf-8",
            )
            (root / "lakefile.lean").write_text(
                'package test where\n  srcDir := "lean"\n'
                'lean_lib Root where\n  roots := #[`Root]\n',
                encoding="utf-8",
            )
            report = build_refactoring_map(
                root, paths=["lakefile.lean", "lean/Root.lean", "lean/Standalone.lean"],
                python_scan=False, git_history=False,
            )

        records = {row["path"]: row for row in report["files"]}
        standalone = records["lean/Standalone.lean"]
        self.assertEqual(standalone["ownerStatus"],
                         "uncertain_module_not_in_lake_target_index")
        self.assertEqual(standalone["moduleCandidate"], "Standalone")
        self.assertEqual(standalone["moduleCandidateStatus"],
                         "lexical_source_root_candidate_not_lake_indexed")
        self.assertNotIn("module", standalone)
        self.assertFalse(standalone.get("buildTargets"))
        self.assertTrue(any(
            edge["from"] == "lean/Standalone.lean"
            and edge["to"] == "lean/Root.lean"
            and edge["kind"] == "lean_source_import"
            for edge in report["dependencyEdges"]
        ))

    def test_map_resolves_manifest_declared_local_lake_package(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean").mkdir()
            (root / "lean/Root.lean").write_text(
                "import InfoGeometryCore.Basic\n", encoding="utf-8"
            )
            package_root = root / "lib/InfoGeometryCore"
            (package_root / "InfoGeometryCore").mkdir(parents=True)
            (package_root / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\npackage InfoGeometryCore\n"
                "lean_lib InfoGeometryCore where\n"
                "  globs := #[.andSubmodules `InfoGeometryCore]\n",
                encoding="utf-8",
            )
            (package_root / "InfoGeometryCore/Basic.lean").write_text(
                "def coreValue := 1\n", encoding="utf-8"
            )
            (root / "lakefile.lean").write_text(
                'import Lake\nopen Lake DSL\npackage sample where\n'
                '  srcDir := "lean"\n'
                'require InfoGeometryCore from "lib" / "InfoGeometryCore"\n'
                'lean_lib Root where\n  root := `Root\n',
                encoding="utf-8",
            )
            (root / "lake-manifest.json").write_text(json.dumps({
                "packages": [{"name": "InfoGeometryCore", "type": "path",
                              "dir": "lib/InfoGeometryCore"}],
            }), encoding="utf-8")

            report = build_refactoring_map(
                root,
                paths=["lakefile.lean", "lake-manifest.json", "lean/Root.lean",
                       "lib/InfoGeometryCore/lakefile.lean",
                       "lib/InfoGeometryCore/InfoGeometryCore/Basic.lean"],
                python_scan=False,
            )

        records = {row["path"]: row for row in report["files"]}
        core = records["lib/InfoGeometryCore/InfoGeometryCore/Basic.lean"]
        self.assertEqual(core["role"], "lean_source")
        self.assertEqual(core["buildTargets"], ["InfoGeometryCore"])
        self.assertTrue(any(
            edge["from"] == "lean/Root.lean"
            and edge["to"] == "lib/InfoGeometryCore/InfoGeometryCore/Basic.lean"
            and edge["kind"] == "lean_source_import"
            for edge in report["dependencyEdges"]
        ))
        self.assertNotIn("module", records["lib/InfoGeometryCore/lakefile.lean"])

    def test_wide_package_srcdir_does_not_claim_unrelated_lean_files(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "proofs").mkdir()
            (root / ".agents").mkdir()
            (root / "proofs/Root.lean").write_text("def proofTool := 1\n", encoding="utf-8")
            (root / ".agents/Probe.lean").write_text("def probe := 2\n", encoding="utf-8")
            (root / "lakefile.lean").write_text(
                'import Lake\nopen Lake DSL\npackage sample where\n'
                '  srcDir := "."\n'
                'lean_lib Proofs where\n'
                '  globs := #[.submodules `proofs]\n',
                encoding="utf-8",
            )

            report = build_refactoring_map(
                root,
                paths=["lakefile.lean", "proofs/Root.lean", ".agents/Probe.lean"],
                python_scan=False,
            )

        records = {row["path"]: row for row in report["files"]}
        self.assertEqual(records["proofs/Root.lean"].get("module"), "proofs.Root")
        self.assertEqual(records["proofs/Root.lean"]["buildTargets"], ["Proofs"])
        self.assertNotIn("module", records[".agents/Probe.lean"])
        self.assertNotIn("buildTargets", records[".agents/Probe.lean"])

    def test_selected_scan_marks_existing_local_import_outside_its_scope(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean/Root").mkdir(parents=True)
            (root / "lean/Root.lean").write_text(
                "import Root.Dependency\n", encoding="utf-8"
            )
            (root / "lean/Root/Dependency.lean").write_text(
                "def dependency := 1\n", encoding="utf-8"
            )
            (root / "lakefile.lean").write_text(
                'package sample where\n  srcDir := "lean"\n'
                'lean_lib Root where\n  root := `Root\n',
                encoding="utf-8",
            )

            report = build_refactoring_map(
                root, paths=["lakefile.lean", "lean/Root.lean"],
                python_scan=False,
            )

        edge = next(edge for edge in report["dependencyEdges"]
                    if edge["importedModule"] == "Root.Dependency")
        self.assertEqual(edge["to"], "lean/Root/Dependency.lean")
        self.assertEqual(edge["kind"], "lean_source_import_outside_inventory")
        self.assertEqual(edge["status"], "repo_source_present_outside_selected_inventory")

    def test_manifest_pinned_dependency_import_is_not_reported_missing(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean").mkdir()
            (root / "lean/Root.lean").write_text(
                "import Mathlib.Data.Basic\n", encoding="utf-8"
            )
            (root / "lakefile.lean").write_text(
                'package sample where\n  srcDir := "lean"\n'
                'lean_lib Root where\n  root := `Root\n',
                encoding="utf-8",
            )
            dependency_root = root / ".lake/packages/mathlib"
            dependency_module = dependency_root / "Mathlib/Data/Basic.lean"
            dependency_module.parent.mkdir(parents=True)
            dependency_module.write_text("def dependency := 1\n", encoding="utf-8")
            (dependency_root / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\npackage mathlib\n"
                "lean_lib scripts where\n  srcDir := \"scripts\"\n",
                encoding="utf-8",
            )
            (root / "lake-manifest.json").write_text(json.dumps({
                "packagesDir": ".lake/packages",
                "packages": [{"name": "mathlib", "type": "git",
                              "rev": "abc123", "configFile": "lakefile.lean"}],
            }), encoding="utf-8")

            report = build_refactoring_map(
                root, paths=["lakefile.lean", "lean/Root.lean"],
                python_scan=False,
            )

        edge = next(edge for edge in report["dependencyEdges"]
                    if edge["importedModule"] == "Mathlib.Data.Basic")
        self.assertEqual(edge["kind"], "lean_external_package_import")
        self.assertEqual(edge["to"], ".lake/packages/mathlib/Mathlib/Data/Basic.lean")
        self.assertEqual(edge["dependencyPackage"], "mathlib")
        self.assertEqual(edge["dependencyRevision"], "abc123")

    def test_lean_import_resolves_sources_inside_external_ref_boundary(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean").mkdir()
            external_module = root / "external_refs/example/GIFT/Algebraic/Octonions.lean"
            external_module.parent.mkdir(parents=True)
            source = "namespace GIFT\nend GIFT\n"
            external_module.write_text(source, encoding="utf-8")
            (root / "lean/Root.lean").write_text(
                "import GIFT.Algebraic.Octonions\n", encoding="utf-8"
            )
            (root / "lakefile.lean").write_text(
                'package sample where\n  srcDir := "lean"\n'
                'lean_lib Root where\n  roots := #[`Root]\n',
                encoding="utf-8",
            )

            report = build_refactoring_map(
                root,
                paths=["lakefile.lean", "lean/Root.lean"],
                python_scan=False,
            )

        edge = next(edge for edge in report["dependencyEdges"]
                    if edge.get("from") == "lean/Root.lean")
        self.assertEqual(edge["kind"], "lean_external_reference_import")
        self.assertEqual(edge["to"],
                         "external_refs/example/GIFT/Algebraic/Octonions.lean")
        self.assertEqual(edge["status"], "external_reference_source_present")
        self.assertEqual(edge["resolution"],
                         "external_submodule_source_observed_by_module_path")
        self.assertEqual(edge["contentSha256"],
                         hashlib.sha256(source.encode("utf-8")).hexdigest())

    def test_lean_import_index_ignores_nested_block_and_line_comments(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean/Root").mkdir(parents=True)
            (root / "lean/Root.lean").write_text(
                "import Root.Dependency /- inline note: import Fake.Inline -/\n"
                "-- import Fake.Line\n"
                "/- outer documentation\n"
                "import Fake.Block\n"
                "/- nested note import Fake.Nested -/\n"
                "-/\n"
                'def note := "import Fake.String"\n',
                encoding="utf-8",
            )
            (root / "lean/Root/Dependency.lean").write_text(
                "def dependency := 1\n", encoding="utf-8"
            )
            (root / "lakefile.lean").write_text(
                'package sample where\n  srcDir := "lean"\n'
                'lean_lib Root where\n'
                '  globs := #[.andSubmodules `Root]\n',
                encoding="utf-8",
            )

            report = build_refactoring_map(
                root,
                paths=["lakefile.lean", "lean/Root.lean",
                       "lean/Root/Dependency.lean"],
                python_scan=False,
            )

        imports = {edge["importedModule"] for edge in report["dependencyEdges"]
                   if edge["from"] == "lean/Root.lean"}
        self.assertEqual(imports, {"Root.Dependency"})

    def test_lean_import_index_preserves_unicode_module_names(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            module_dir = root / "lean/InfoGeometry/Canonical"
            module_dir.mkdir(parents=True)
            (root / "lean/Root.lean").write_text(
                "import InfoGeometry.Canonical.ZornVectorMatrixMöbiusAction\n",
                encoding="utf-8",
            )
            (module_dir / "ZornVectorMatrixMöbiusAction.lean").write_text(
                "def marker := 1\n", encoding="utf-8"
            )
            (root / "lakefile.lean").write_text(
                'package sample where\n  srcDir := "lean"\n'
                'lean_lib Root where\n  roots := #[`Root]\n',
                encoding="utf-8",
            )

            report = build_refactoring_map(
                root,
                paths=["lakefile.lean", "lean/Root.lean",
                       "lean/InfoGeometry/Canonical/ZornVectorMatrixMöbiusAction.lean"],
                python_scan=False,
            )

        edge = next(edge for edge in report["dependencyEdges"]
                    if edge["from"] == "lean/Root.lean")
        self.assertEqual(
            edge["importedModule"],
            "InfoGeometry.Canonical.ZornVectorMatrixMöbiusAction",
        )
        self.assertEqual(
            edge["to"],
            "lean/InfoGeometry/Canonical/ZornVectorMatrixMöbiusAction.lean",
        )
        self.assertEqual(report["leanImportDiagnostics"], [])

    def test_lean_import_index_normalizes_quoted_identifiers(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "proofs/BraidProject").mkdir(parents=True)
            (root / "lean").mkdir()
            (root / "lean/Root.lean").write_text(
                "import proofs.«BraidProject».Basic\n",
                encoding="utf-8",
            )
            (root / "proofs/BraidProject/Basic.lean").write_text(
                "def marker := 1\n", encoding="utf-8"
            )
            (root / "lakefile.lean").write_text(
                'package sample where\n  srcDir := "lean"\n'
                'lean_lib Root where\n  roots := #[`Root]\n'
                'lean_lib Proofs where\n  srcDir := ".."\n'
                '  roots := #[`proofs.BraidProject]\n',
                encoding="utf-8",
            )

            report = build_refactoring_map(
                root,
                paths=["lakefile.lean", "lean/Root.lean",
                       "proofs/BraidProject/Basic.lean"],
                python_scan=False,
            )

        edge = next(edge for edge in report["dependencyEdges"]
                    if edge.get("from") == "lean/Root.lean")
        self.assertEqual(edge["importedModule"], "proofs.BraidProject.Basic")
        self.assertEqual(edge["to"], "proofs/BraidProject/Basic.lean")
        self.assertEqual(report["leanImportDiagnostics"], [])

    def test_lean_import_index_reports_path_like_names_without_fake_edges(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean").mkdir()
            (root / "lean/Root.lean").write_text(
                "import proofs/BraidProject/Basic.lean\n", encoding="utf-8"
            )
            (root / "lakefile.lean").write_text(
                'package sample where\n  srcDir := "lean"\n'
                'lean_lib Root where\n  roots := #[`Root]\n',
                encoding="utf-8",
            )

            report = build_refactoring_map(
                root, paths=["lakefile.lean", "lean/Root.lean"], python_scan=False
            )

        self.assertFalse(any(edge.get("from") == "lean/Root.lean"
                             for edge in report["dependencyEdges"]))
        self.assertEqual(report["leanImportDiagnostics"], [{
            "sourcePath": "lean/Root.lean",
            "line": 1,
            "rawImport": "proofs/BraidProject/Basic.lean",
            "status": "unsupported_import_name_syntax",
            "evidence": "Lean import command text; module edges withheld",
        }])

    def test_unresolved_import_counts_are_stratified_by_source_role(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean/archive").mkdir(parents=True)
            (root / "lean/Root.lean").write_text(
                "theorem root_fact : True := True.intro\n", encoding="utf-8"
            )
            (root / "lean/archive/Old.lean").write_text(
                "import Missing.LocalModule\n", encoding="utf-8"
            )
            (root / "lakefile.lean").write_text(
                'package sample where\n  srcDir := "lean"\n'
                'lean_lib Root where\n  root := `Root\n', encoding="utf-8"
            )
            report = build_refactoring_map(
                root, paths=["lakefile.lean", "lean/Root.lean",
                             "lean/archive/Old.lean"],
                python_scan=False, git_history=False,
            )
        self.assertEqual(report["summary"]["leanImportsWithoutRepoSource"], 1)
        self.assertEqual(report["summary"]["unresolvedLeanImportsBySourceRole"], {
            "sandbox_or_historical_candidate": 1,
        })

    def test_repository_snapshot_detects_paths_added_during_scan(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean").mkdir()
            (root / "lean/Root.lean").write_text(
                "theorem root_fact : True := True.intro\n", encoding="utf-8"
            )
            (root / "lakefile.lean").write_text(
                'package sample where\n  srcDir := "lean"\n'
                'lean_lib Root where\n  root := `Root\n', encoding="utf-8"
            )
            initial_paths = ["lakefile.lean", "lean/Root.lean"]
            final_paths = [*initial_paths, "lean/New.lean"]
            calls = 0

            def inventory(_root: Path) -> list[str]:
                nonlocal calls
                calls += 1
                if calls == 1:
                    return initial_paths
                (root / "lean/New.lean").write_text(
                    "theorem new_fact : True := True.intro\n", encoding="utf-8"
                )
                return final_paths

            with patch.object(refactoring_map_owner, "tracked_paths", side_effect=inventory):
                report = build_refactoring_map(root, python_scan=False, git_history=False)

        snapshot = report["sourceSnapshot"]
        self.assertFalse(snapshot["worktreeConsistentDuringScan"])
        self.assertEqual(snapshot["addedPathCountDuringScan"], 1)
        self.assertEqual(snapshot["addedPathSampleDuringScan"], ["lean/New.lean"])
        self.assertIn("lean/New.lean", snapshot["changedPathSampleDuringScan"])

    def test_map_records_symlink_as_alias_and_binds_its_target(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / "external/Target.lean"
            target.parent.mkdir(parents=True)
            target.write_text("theorem target : True := True.intro\n", encoding="utf-8")
            alias = root / "lean/Alias.lean"
            alias.parent.mkdir(parents=True)
            try:
                os.symlink("../external/Target.lean", alias)
            except OSError as exc:
                self.skipTest(f"symlink creation unavailable: {exc}")
            (root / "lakefile.lean").write_text(
                'package test where\n  srcDir := "lean"\n', encoding="utf-8"
            )
            (root / "lake-manifest.json").write_text("{}\n", encoding="utf-8")

            report = build_refactoring_map(
                root,
                paths=["external/Target.lean", "lake-manifest.json",
                       "lakefile.lean", "lean/Alias.lean"],
                python_scan=False,
                git_history=False,
            )

        rows = {row["path"]: row for row in report["files"]}
        self.assertEqual(rows["lean/Alias.lean"]["filesystemEntry"], "symlink")
        self.assertEqual(rows["lean/Alias.lean"]["symlinkResolvedPath"],
                         "external/Target.lean")
        self.assertEqual(rows["lean/Alias.lean"]["contentSha256"],
                         rows["external/Target.lean"]["contentSha256"])
        alias_edge = next(edge for edge in report["dependencyEdges"]
                          if edge["kind"] == "filesystem_symlink_alias")
        self.assertEqual((alias_edge["from"], alias_edge["to"], alias_edge["status"]),
                         ("lean/Alias.lean", "external/Target.lean", "path_alias"))
        self.assertEqual(len(report["sourceSnapshot"]["filesystemTopologySha256"]), 64)
        self.assertTrue(report["sourceSnapshot"]["worktreeConsistentDuringScan"])

    def test_symlink_inside_lake_source_root_keeps_lexical_module_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / "external/Target.lean"
            target.parent.mkdir(parents=True)
            target.write_text("theorem target : True := True.intro\n", encoding="utf-8")
            alias = root / "lean/PrimitiveSetsAboveX.lean"
            alias.parent.mkdir(parents=True)
            try:
                os.symlink("../external/Target.lean", alias)
            except OSError as exc:
                self.skipTest(f"symlink creation unavailable: {exc}")
            (root / "lakefile.lean").write_text(
                'package test where\n  srcDir := "lean"\n'
                'lean_lib PrimitiveSetsAboveX where\n'
                '  globs := #[.andSubmodules `PrimitiveSetsAboveX]\n',
                encoding="utf-8",
            )
            report = build_refactoring_map(
                root,
                paths=["external/Target.lean", "lakefile.lean",
                       "lean/PrimitiveSetsAboveX.lean"],
                python_scan=False, git_history=False,
            )
        row = next(row for row in report["files"]
                   if row["path"] == "lean/PrimitiveSetsAboveX.lean")
        self.assertEqual(row["module"], "PrimitiveSetsAboveX")
        self.assertIn("PrimitiveSetsAboveX", row["buildTargets"])

    def test_map_uses_leading_generation_markers_as_separate_source_evidence(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            generated = root / "InfoGeometry/GeneratedTags.lean"
            handwritten = root / "InfoGeometry/Handwritten.lean"
            generated.parent.mkdir(parents=True)
            generated.write_text(
                "/-!\nAUTO-GENERATED FILE. DO NOT EDIT BY HAND.\n"
                "Generated by scripts/auto_tag.py.\n-/\nattribute [blueprint] Example.thm\n",
                encoding="utf-8",
            )
            handwritten.write_text("theorem handwritten : True := True.intro\n",
                                   encoding="utf-8")
            (root / "lakefile.lean").write_text(
                'package sample where\n  srcDir := "lean"\n', encoding="utf-8"
            )
            (root / "lake-manifest.json").write_text("{}\n", encoding="utf-8")

            report = build_refactoring_map(
                root,
                paths=["InfoGeometry/GeneratedTags.lean", "InfoGeometry/Handwritten.lean",
                       "lakefile.lean", "lake-manifest.json"],
                python_scan=False,
            )

        records = {row["path"]: row for row in report["files"]}
        self.assertEqual(records["InfoGeometry/GeneratedTags.lean"]["role"],
                         "generated_source_artifact")
        self.assertEqual(records["InfoGeometry/GeneratedTags.lean"]["status"],
                         "content_marker_observed_candidate")
        self.assertEqual(records["InfoGeometry/GeneratedTags.lean"]["contentRoleEvidence"]["evidence"],
                         "leading_source_generation_markers")
        self.assertEqual(records["InfoGeometry/Handwritten.lean"]["role"],
                         "lean_candidate_outside_package_source")

    def test_map_marks_a_mixed_worktree_snapshot_inconsistent(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean").mkdir()
            source = root / "lean/Root.lean"
            source.write_text("def before := 1\n", encoding="utf-8")
            (root / "lakefile.lean").write_text(
                'package test where\n  srcDir := "lean"\n'
                'lean_lib Root where\n  root := `Root\n', encoding="utf-8"
            )

            def mutate_source(_root, _paths):
                source.write_text("def after := 2\n", encoding="utf-8")
                return []

            with patch.object(refactoring_map_owner, "lean_declaration_candidates",
                              side_effect=mutate_source):
                report = build_refactoring_map(
                    root, paths=["lakefile.lean", "lean/Root.lean"],
                    python_scan=False, compiler_meta=root / "missing-meta.json",
                )

        self.assertFalse(report["sourceSnapshot"]["worktreeConsistentDuringScan"])
        self.assertEqual(report["sourceSnapshot"]["consistencyStatus"],
                         "paths_changed_during_scan")
        self.assertIn("lean/Root.lean", report["sourceSnapshot"]["changedPathSampleDuringScan"])


if __name__ == "__main__":
    unittest.main()
