#!/usr/bin/env python3
"""Build an offline, evidence-labeled refactoring map of the current worktree.

This composes source roles, Lean imports/Lake roots, the existing Python
dependency oracle, and source/olean/output-bound compiler fingerprints when
their generation receipts verify. Fingerprints remain navigation candidates.
No source files are copied and no ArangoDB connection is made.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import gzip
import os
import sys
from collections import Counter, defaultdict, deque
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
SOURCE_SUFFIXES = {
    ".lean", ".py", ".ts", ".tsx", ".js", ".jsx", ".sh", ".go", ".rs",
    ".c", ".h", ".cc", ".cpp", ".cxx", ".hpp", ".java", ".scala", ".kt",
    ".hs", ".lhs", ".ml", ".mli", ".jl", ".sage", ".m2", ".g", ".v",
}
TEST_PARTS = {"test", "tests", "testing"}
GENERATED_PARTS = {".lake", "build", "dist", "node_modules", "__pycache__"}
HISTORICAL_PARTS = {
    "archive", "archives", "scratch", "sandbox",
    "major_restore_non_overwriting",
    "proofs_removed_from_default_2026_06_15",
}
SKIP_PARTS = {".git", ".lake", "node_modules", "__pycache__", ".venv"}
EVOLUTION_COMPONENT_BY_NAME = {
    "__init__.py": "package_boundary",
    "ancestry_hodge.py": "commit_graph_topology",
    "attention_scc.py": "directed_scc_attention",
    "context_transport.py": "balanced_context_transport",
    "dna-affinity-viewer.html": "affinity_visualization",
    "dna_character_tree.py": "declaration_digest_affinity",
    "edge_attention_baseline.py": "typed_edge_attention",
    "generation_manifest.py": "source_generation_provenance",
    "git_fossil_overlay.py": "git_path_lineage_overlay",
    "infotree_dna.py": "current_infotree_fingerprints",
    "latent_taxonomy.py": "latent_expert_inference",
    "materialize_taxonomy_adjudications.py": "reviewed_label_materialization",
    "phylogeny_export.py": "commit_ancestry_export",
    "refactoring_map.py": "source_role_dependency_inventory",
    "render_explorer.py": "evidence_linked_visualization",
    "repository-phylogeny.template.html": "phylogeny_visualization_template",
    "requirements-hodge.txt": "analysis_runtime_dependencies",
    "reviewed_taxonomy_corpus.py": "reviewed_label_corpus_and_splits",
    "source_embeddings.py": "source_embedding_extraction",
    "taxonomy_adjudication_queue.py": "review_queue_management",
    "taxonomy_training_readiness.py": "reviewed_data_readiness",
    "train_code_transformer.py": "self_supervised_source_encoder",
    "train_graph_context_encoder.py": "self_supervised_graph_context_encoder",
    "train_taxonomy_baseline.py": "supervised_taxonomy_training",
}


def tracked_paths(root: Path) -> list[str]:
    """Return tracked plus non-ignored worktree paths; do not recurse submodules."""
    result = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
        cwd=root, check=True, stdout=subprocess.PIPE,
    )
    paths = []
    for raw in result.stdout.split(b"\0"):
        if not raw:
            continue
        rel = raw.decode("utf-8", errors="surrogateescape")
        if any(part in SKIP_PARTS for part in Path(rel).parts):
            continue
        target = root / rel
        # A gitlink is a directory. Keep its boundary record without reading it.
        if target.is_file() or rel.startswith("external_refs/"):
            paths.append(rel)
    return sorted(set(paths))


def _worktree_file_state(root: Path, paths: Iterable[str]) -> tuple[tuple[str, tuple[int, ...] | None], ...]:
    """Capture path identities to detect edits during a long inventory scan."""
    state = []
    for rel in paths:
        try:
            stat = (root / rel).lstat()
            identity = (stat.st_dev, stat.st_ino, stat.st_mode, stat.st_size,
                        stat.st_mtime_ns, stat.st_ctime_ns)
        except OSError:
            identity = None
        state.append((rel, identity))
    return tuple(state)


def _sha256_path(path: Path) -> str | None:
    """Hash a configuration or analyzer input when it exists as a regular file."""
    try:
        if not path.is_file():
            return None
        digest = hashlib.sha256()
        with path.open("rb") as stream:
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(block)
        return digest.hexdigest()
    except OSError:
        return None


def _compiler_fingerprint_summaries(
    root: Path, meta_path: Path, meta: dict[str, Any],
    current_source_hash: str | None = None,
    snapshot_verified: bool = True,
) -> tuple[dict[str, Any], dict[str, dict[str, Any]]]:
    """Read compiler fingerprints only when source, olean, and export bytes bind.

    The returned digests are navigation features, never declaration identity or
    proof evidence. Per-file rows are deliberately aggregated to keep the
    taxonomy report bounded.
    """
    try:
        from tools.infra.build import compute_lean_source_hash, compute_olean_content_hash

        source_hash = current_source_hash or compute_lean_source_hash(root)
        if not source_hash or meta.get("sourceHash") != source_hash:
            return {"status": "source_hash_mismatch_do_not_join"}, {}
        if not snapshot_verified:
            return {"status": "worktree_snapshot_unstable_do_not_join"}, {}
        olean_hash = compute_olean_content_hash(root)
        if not olean_hash or meta.get("oleanHash") != olean_hash:
            return {"status": "olean_hash_mismatch_do_not_join"}, {}
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as exc:
        return {"status": "build_identity_check_failed",
                "error": f"{type(exc).__name__}: {exc}"}, {}

    expected_outputs = meta.get("outputHashes")
    if meta.get("schemaVersion") != 3:
        return {"status": "unsupported_declaration_export_schema_do_not_join"}, {}
    if meta.get("outputHashAlgorithm") != "sha256" or not isinstance(expected_outputs, dict):
        return {"status": "export_hashes_missing_do_not_join"}, {}
    decls_path = meta_path.parent / "decls.jsonl"
    edges_path = meta_path.parent / "edges.jsonl"
    for name, path in (("decls.jsonl", decls_path), ("edges.jsonl", edges_path)):
        actual = _sha256_path(path)
        if not actual or expected_outputs.get(name) != actual:
            return {"status": "export_hash_mismatch_do_not_join",
                    "mismatchedArtifact": name}, {}

    file_rows: dict[str, dict[str, Any]] = {}
    type_cohorts: dict[tuple[str, str], dict[str, list[dict[str, str]]]] = defaultdict(dict)
    declaration_count = 0
    malformed_count = 0
    invalid_fingerprint_count = 0
    try:
        with decls_path.open("r", encoding="utf-8") as stream:
            for raw in stream:
                if not raw.strip():
                    continue
                try:
                    row = json.loads(raw)
                except json.JSONDecodeError:
                    malformed_count += 1
                    continue
                if not isinstance(row, dict):
                    malformed_count += 1
                    continue
                type_digest = row.get("typeDigest")
                if not (isinstance(type_digest, dict)
                        and type_digest.get("algorithmVersion") == "lean-expr-debruijn-v4"
                        and isinstance(type_digest.get("digest"), str)):
                    invalid_fingerprint_count += 1
                    continue
                declaration_count += 1
                rel = row.get("relFile")
                if not isinstance(rel, str) or not rel:
                    rel = row.get("file")
                if not isinstance(rel, str) or not rel:
                    continue
                rel_path = Path(rel)
                if rel_path.is_absolute():
                    try:
                        rel = rel_path.resolve().relative_to(root.resolve()).as_posix()
                    except (OSError, ValueError):
                        continue
                else:
                    rel = rel_path.as_posix()
                summary = file_rows.setdefault(rel, {
                    "declarationCount": 0,
                    "typeDigests": set(),
                    "valueDigests": set(),
                    "openTypeDigestCount": 0,
                    "openValueDigestCount": 0,
                })
                summary["declarationCount"] += 1
                digest = type_digest["digest"]
                summary["typeDigests"].add(digest)
                kind = row.get("kind")
                cohort_files = type_cohorts[(kind if isinstance(kind, str) else "?", digest)]
                witnesses = cohort_files.setdefault(rel, [])
                declaration_name = row.get("name")
                if len(witnesses) < 4 and isinstance(declaration_name, str):
                    witness = {"sourceFile": rel, "declaration": declaration_name}
                    module_name = row.get("module")
                    if isinstance(module_name, str):
                        witness["module"] = module_name
                    witnesses.append(witness)
                if type_digest.get("openTerm") is True:
                    summary["openTypeDigestCount"] += 1
                value_digest = row.get("valueDigest")
                if isinstance(value_digest, dict) and value_digest.get("algorithmVersion") == "lean-expr-debruijn-v4":
                    digest = value_digest.get("digest")
                    if isinstance(digest, str):
                        summary["valueDigests"].add(digest)
                    if value_digest.get("openTerm") is True:
                        summary["openValueDigestCount"] += 1
    except OSError as exc:
        return {"status": "declaration_export_unreadable",
                "error": f"{type(exc).__name__}: {exc}"}, {}

    edge_count = 0
    try:
        with edges_path.open("r", encoding="utf-8") as stream:
            edge_count = sum(bool(raw.strip()) for raw in stream)
    except OSError as exc:
        return {"status": "edge_export_unreadable",
                "error": f"{type(exc).__name__}: {exc}"}, {}
    if malformed_count or invalid_fingerprint_count:
        return {"status": "malformed_declaration_export_do_not_join",
                "malformedRecordCount": malformed_count,
                "invalidFingerprintCount": invalid_fingerprint_count}, {}
    if declaration_count != meta.get("nodeCount") or edge_count != meta.get("edgeCount"):
        return {"status": "export_record_count_mismatch_do_not_join",
                "declarationCount": declaration_count,
                "metadataDeclarationCount": meta.get("nodeCount"),
                "edgeCount": edge_count,
                "metadataEdgeCount": meta.get("edgeCount")}, {}

    normalized: dict[str, dict[str, Any]] = {}
    for rel, summary in file_rows.items():
        normalized[rel] = {
            "declarationCount": summary["declarationCount"],
            "uniqueTypeDigestCount": len(summary["typeDigests"]),
            "uniqueValueDigestCount": len(summary["valueDigests"]),
            "openTypeDigestCount": summary["openTypeDigestCount"],
            "openValueDigestCount": summary["openValueDigestCount"],
            "typeDigestAlgorithm": "lean-expr-debruijn-v4",
        }
    cohort_count = sum(len(source_files) > 1 for source_files in type_cohorts.values())
    cohorts = []
    for (kind, digest), source_files in type_cohorts.items():
        if len(source_files) <= 1:
            continue
        if len(cohorts) < 1000:
            cohorts.append({
                "kind": kind, "typeDigest": digest, "sourceFiles": sorted(source_files),
                "declarationWitnesses": [
                    witness for rel in sorted(source_files)
                    for witness in source_files[rel]
                ][:20],
                "status": "exact_fingerprint_candidate_requires_kernel_review",
            })
    return {
        "status": "source_olean_and_export_hashes_verified",
        "importRoot": meta.get("importRoot"),
        "namespace": meta.get("nsFilter"),
        "declarationCount": declaration_count,
        "fileCount": len(normalized),
        "malformedRecordCount": malformed_count,
        "invalidFingerprintCount": invalid_fingerprint_count,
        "edgeCount": edge_count,
        "crossFileExactTypeDigestCohortCount": cohort_count,
        "crossFileExactTypeDigestCohorts": cohorts,
        "algorithm": "lean-expr-debruijn-v4",
        "interpretation": "fingerprint equality is a navigation candidate, not declaration identity or semantic equivalence",
    }, normalized


def _symlink_metadata(root: Path, rel: str) -> dict[str, Any]:
    """Describe a tracked symlink without treating its target as a new copy."""
    path = root / rel
    if not path.is_symlink():
        return {"filesystemEntry": "regular_file"}
    try:
        raw_target = os.readlink(path)
        resolved = (path.parent / raw_target).resolve(strict=False)
        try:
            resolved_rel = resolved.relative_to(root.resolve()).as_posix()
        except ValueError:
            resolved_rel = None
        return {"filesystemEntry": "symlink", "symlinkTarget": raw_target,
                "symlinkResolvedPath": resolved_rel}
    except (OSError, RuntimeError):
        return {"filesystemEntry": "symlink", "symlinkTarget": None,
                "symlinkResolvedPath": None,
                "symlinkResolutionStatus": "unreadable_or_cyclic"}


def _generated_source_marker(raw: bytes) -> dict[str, str] | None:
    """Return explicit leading-file generation evidence, not a path guess."""
    header = raw[:4096].decode("utf-8", errors="replace")
    lines = header.splitlines()[:30]
    marker_lines = [line.strip() for line in lines
                    if re.search(r"auto[- ]generated|generated automatically", line, re.I)]
    directive_lines = [line.strip() for line in lines
                       if re.search(r"do not edit|generated by", line, re.I)]
    if marker_lines and directive_lines:
        return {
            "marker": marker_lines[0],
            "directive": directive_lines[0],
            "evidence": "leading_source_generation_markers",
        }
    return None


def classify_file(path: str) -> dict[str, str]:
    """Classify by repository path convention and preserve the rule basis."""
    parts = Path(path).parts
    low = [part.lower() for part in parts]
    suffix = Path(path).suffix.lower()
    if parts[0] == "external_refs":
        return {"role": "external_reference", "status": "path_observed",
                "owner": "external_ref_boundary"}
    if any((part.startswith(".") and ("archive" in part.lower()
                                       or "sandbox" in part.lower()))
           or part.lower() in HISTORICAL_PARTS
           or part.lower() == "lean_sandbox" for part in parts):
        return {"role": "sandbox_or_historical_candidate",
                "status": "path_observed_uncertain_scope",
                "owner": "/".join(parts[:2]) if len(parts) > 1 else parts[0]}
    if parts[0] in {".agents", ".hermes", "agent_memory_recovery", "agent_memory_recovery_stitched",
                    "agent_writes_recovery_v4"} or any(part.lower() in HISTORICAL_PARTS for part in low):
        return {"role": "sandbox_or_historical_candidate", "status": "path_observed_uncertain_scope",
                "owner": parts[0] if parts[0].startswith(".") else "/".join(parts[:2])}
    if any(part in GENERATED_PARTS for part in low) or path.startswith(("artifacts/", "reports/")):
        return {"role": "generated_or_build_artifact", "status": "path_observed",
                "owner": "generated_artifact_boundary"}
    if any(part in TEST_PARTS for part in low) or Path(path).name.startswith("test_"):
        return {"role": "test_or_fixture", "status": "path_observed",
                "owner": "/".join(parts[:2]) if len(parts) > 1 else parts[0]}
    if path.startswith(("proofs/external/repos/", "proofs/antigravity-sdk-python/")):
        return {"role": "vendored_or_external_reference",
                "status": "path_boundary_candidate",
                "owner": "/".join(parts[:3])}
    if path.startswith("backend/cuda/eigen/") and suffix in SOURCE_SUFFIXES:
        return {"role": "vendored_dependency_source",
                "status": "path_and_license_observed",
                "owner": "backend/cuda/eigen"}
    if path.startswith("backend/cuda/") and suffix in SOURCE_SUFFIXES:
        return {"role": "gpu_backend_source", "status": "path_observed",
                "owner": "backend/cuda"}
    if path.startswith("proofs/tools/") and suffix in SOURCE_SUFFIXES:
        return {"role": "proof_analysis_tool", "status": "path_observed_candidate",
                "owner": "proofs/tools"}
    if path.startswith("proofs/") and suffix in SOURCE_SUFFIXES:
        return {"role": "formalization_support_artifact",
                "status": "path_observed_not_proof_validation",
                "owner": "/".join(parts[:2]) if len(parts) > 1 else "proofs"}
    if path.startswith("formalizations/") and suffix in SOURCE_SUFFIXES:
        return {"role": "formalization_support_artifact",
                "status": "path_observed_not_proof_validation",
                "owner": "formalizations"}
    if path.startswith("witnesses/") and suffix in SOURCE_SUFFIXES:
        return {"role": "symbolic_witness_artifact",
                "status": "path_observed_not_proof_validation",
                "owner": "/".join(parts[:2]) if len(parts) > 1 else "witnesses"}
    if path.startswith(("coq/", "formal/coq/", "theories/")) and suffix in SOURCE_SUFFIXES:
        return {"role": "non_lean_formalization_source",
                "status": "source_observed_verification_unchecked",
                "owner": "/".join(parts[:2])}
    if path.startswith("leantrail/") and suffix in SOURCE_SUFFIXES:
        return {"role": "verification_tooling", "status": "path_observed",
                "owner": "leantrail"}
    if path.startswith("extensions/") and suffix in SOURCE_SUFFIXES:
        return {"role": "agent_or_app_extension", "status": "path_observed",
                "owner": "extensions"}
    if path.startswith("src/igf/") and suffix in SOURCE_SUFFIXES:
        return {"role": "python_package_source", "status": "path_observed",
                "owner": "src.igf"}
    if path.startswith("src/") and suffix in SOURCE_SUFFIXES:
        return {"role": "repository_source_candidate",
                "status": "path_observed_owner_uncertain",
                "owner": "/".join(parts[:2])}
    if path.startswith(("python/", "sage/", "clifford/", "macaulay2/", "tech/sage/")) \
            and suffix in SOURCE_SUFFIXES:
        owner = "/".join(parts[:2]) if parts[0] == "tech" else parts[0]
        return {"role": "formalization_support_artifact",
                "status": "source_observed_verification_unchecked", "owner": owner}
    if path.startswith(".claude/tools/") and suffix in SOURCE_SUFFIXES:
        return {"role": "agent_or_app_extension", "status": "path_observed",
                "owner": ".claude/tools"}
    if path.startswith("cli/") and suffix in SOURCE_SUFFIXES:
        return {"role": "command_line_interface_source", "status": "path_observed",
                "owner": "cli"}
    if path.startswith("pi-omega-extension/") and suffix in SOURCE_SUFFIXES:
        return {"role": "agent_or_app_extension", "status": "path_observed",
                "owner": "pi-omega-extension"}
    if path.startswith("migrations/") and suffix in SOURCE_SUFFIXES:
        return {"role": "database_migration_source", "status": "path_observed",
                "owner": "migrations"}
    if path.startswith("presentation/") and suffix in SOURCE_SUFFIXES:
        return {"role": "presentation_or_visualization_tool", "status": "path_observed",
                "owner": "presentation"}
    if path.startswith(("jsonschema/", "jsonschema_shadow/")) and suffix in SOURCE_SUFFIXES:
        return {"role": "repository_source_candidate",
                "status": "path_observed_owner_uncertain", "owner": parts[0]}
    if Path(path).name in {
        "lakefile.lean", "lake-manifest.json", "lean-toolchain", "package.json",
        "pyproject.toml",
    }:
        return {"role": "build_or_package_configuration", "status": "path_observed",
                "owner": "repository_build_configuration"}
    if path.startswith("lean/") and suffix == ".lean":
        return {"role": "lean_source", "status": "path_observed",
                "owner": "lake_target_pending_resolution"}
    if path.startswith("lean/") and suffix in SOURCE_SUFFIXES:
        return {"role": "repository_source_candidate",
                "status": "path_observed_owner_uncertain",
                "owner": "/".join(parts[:2])}
    if path.startswith("tools/quality/"):
        return {"role": "quality_gate_or_audit", "status": "path_observed",
                "owner": "tools.quality"}
    if path.startswith("tools/repository_evolution/"):
        component = EVOLUTION_COMPONENT_BY_NAME.get(Path(path).name)
        return {"role": "repository_evolution_analysis", "status": "path_observed",
                "owner": "tools.repository_evolution",
                "component": component or "unclassified_evolution_subsystem",
                "componentStatus": ("repo_entrypoint_role_reviewed" if component
                                    else "uncertain_unmapped_entrypoint")}
    if path.startswith("tools/infra/"):
        return {"role": "infrastructure_tool", "status": "path_observed",
                "owner": "tools.infra"}
    if path.startswith("tools/"):
        return {"role": "tool_or_library", "status": "path_observed",
                "owner": "/".join(parts[:2])}
    if path.startswith("scripts/"):
        return {"role": "operational_script", "status": "path_observed",
                "owner": "/".join(parts[:2])}
    if path.startswith(("docs/", "skills/")) or Path(path).suffix.lower() in {".md", ".rst"}:
        return {"role": "documentation_or_agent_contract", "status": "path_observed",
                "owner": "/".join(parts[:2]) if len(parts) > 1 else parts[0]}
    if len(parts) == 1 and suffix in {".py", ".sh", ".js", ".ts"}:
        return {"role": "repository_root_script", "status": "path_observed_candidate",
                "owner": "repository_root_scripts"}
    if path.endswith(".lean"):
        return {"role": "lean_candidate_outside_package_source", "status": "uncertain",
                "owner": "unresolved_lean_scope"}
    if Path(path).suffix.lower() in SOURCE_SUFFIXES:
        return {"role": "source_file_unclassified", "status": "uncertain",
                "owner": "unresolved"}
    return {"role": "non_source_asset", "status": "path_observed",
            "owner": "/".join(parts[:2]) if len(parts) > 1 else parts[0]}


def parse_lake_targets(lakefile: str, repo_root: Path) -> list[dict[str, Any]]:
    """Extract declared Lean library/executable roots as static build evidence."""
    lakefile = _strip_lean_comments(lakefile)
    package_src = re.search(r'^\s*srcDir\s*:=\s*"([^"]+)"', lakefile, re.M)
    package_src_dir = package_src.group(1) if package_src else "lean"
    headers = list(re.finditer(r"^\s*lean_(lib|exe)\s+([A-Za-z0-9_.]+)\s+where\s*$",
                               lakefile, re.M))
    targets: list[dict[str, Any]] = []
    for index, match in enumerate(headers):
        end = headers[index + 1].start() if index + 1 < len(headers) else len(lakefile)
        block = lakefile[match.end():end]
        source_match = re.search(r'^\s*srcDir\s*:=\s*"([^"]+)"', block, re.M)
        source_dir = source_match.group(1) if source_match else "."

        def assignment(field: str) -> str | None:
            found = re.search(rf"^\s*{field}\s*:=\s*", block, re.M)
            if not found:
                return None
            start = found.end()
            if block.startswith("#[", start):
                depth = 0
                in_string = False
                escaped = False
                for offset in range(start, len(block)):
                    char = block[offset]
                    if in_string:
                        if escaped:
                            escaped = False
                        elif char == "\\":
                            escaped = True
                        elif char == '"':
                            in_string = False
                    elif char == '"':
                        in_string = True
                    elif char == "[":
                        depth += 1
                    elif char == "]":
                        depth -= 1
                        if depth == 0:
                            return block[start:offset + 1].strip()
                return block[start:].strip()
            line_end = block.find("\n", start)
            return block[start:line_end if line_end >= 0 else len(block)].strip()

        def names(expression: str) -> list[str]:
            return [name.replace("«", "").replace("»", "") for name in
                    re.findall(rf"`({LEAN_MODULE_NAME.pattern})", expression)]

        def unmatched_text(expression: str, pattern: re.Pattern[str]) -> str:
            remainder = list(expression)
            for item in pattern.finditer(expression):
                remainder[item.start():item.end()] = " " * (item.end() - item.start())
            return re.sub(r"[\s,#\[\]]", "", "".join(remainder))

        root_expr = assignment("root")
        roots_expr = assignment("roots")
        roots_present = root_expr is not None or roots_expr is not None
        selected_root_expr = root_expr if root_expr is not None else roots_expr
        selected_root_expr = selected_root_expr or ""
        root_pattern = re.compile(rf"`({LEAN_MODULE_NAME.pattern})")
        root_names = names(selected_root_expr)
        root_parse_remainder = unmatched_text(selected_root_expr, root_pattern)
        if not roots_present:
            root_names = [match.group(2)]

        globs_expr = assignment("globs")
        globs: list[dict[str, Any]] = []
        if globs_expr is not None:
            glob_pattern = re.compile(
                rf"\.(andSubmodules|submodules)\s+`({LEAN_MODULE_NAME.pattern})"
                rf"|`({LEAN_MODULE_NAME.pattern})"
            )
            for glob_match in glob_pattern.finditer(globs_expr):
                kind = glob_match.group(1)
                module = glob_match.group(2) or glob_match.group(3)
                module = module.replace("«", "").replace("»", "")
                globs.append({
                    "module": module,
                    "includeSelf": kind != "submodules",
                    "includeSubmodules": kind in {"andSubmodules", "submodules"},
                    "globKind": kind or "one",
                })
            glob_parse_remainder = unmatched_text(globs_expr, glob_pattern)
            glob_parse_status = ("complete_static_parse" if not glob_parse_remainder
                                 else "partial_static_parse")
        else:
            globs = [{"module": module, "includeSelf": True,
                      "includeSubmodules": False, "globKind": "one"}
                     for module in root_names]
            glob_parse_remainder = ""
            glob_parse_status = "derived_from_roots"
        targets.append({
            "name": match.group(2),
            "kind": "lean_lib" if match.group(1) == "lib" else "lean_exe",
            "sourceDir": source_dir,
            "roots": list(dict.fromkeys(root_names)),
            "rootParseStatus": ("complete_static_parse" if not root_parse_remainder
                                else "partial_static_parse"),
            "rootParseRemainder": root_parse_remainder,
            "globs": globs,
            "globParseStatus": glob_parse_status,
            "globParseRemainder": glob_parse_remainder,
            "evidence": "lakefile_static_parse",
            "status": "static_build_boundary_candidate",
        })
    return targets


def _package_source_dir(lakefile: str, default: str) -> str:
    """Read only package-level srcDir, excluding target-level declarations."""
    first_target = re.search(r"^\s*lean_(?:lib|exe)\s+", lakefile, re.M)
    package_block = lakefile[:first_target.start()] if first_target else lakefile
    match = re.search(r'^\s*srcDir\s*:=\s*"([^"]+)"', package_block, re.M)
    return match.group(1) if match else default


def _lake_package_targets(root: Path, paths: Iterable[str]) -> list[dict[str, Any]]:
    """Read root and manifest-declared local Lake package target boundaries."""
    package_specs: list[tuple[str, str, Path, Path]] = []
    root_lakefile = root / "lakefile.lean"
    if root_lakefile.is_file():
        text = root_lakefile.read_text(encoding="utf-8", errors="replace")
        name_match = re.search(r"^\s*package\s+([A-Za-z0-9_.-]+)", text, re.M)
        package_specs.append((name_match.group(1) if name_match else "root",
                              ".", root, root / _package_source_dir(text, "lean")))

    manifest_path = root / "lake-manifest.json"
    if manifest_path.is_file():
        try:
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            manifest = {}
        for package in manifest.get("packages", []):
            if not isinstance(package, dict) or package.get("type") != "path":
                continue
            package_dir_value = package.get("dir")
            if not isinstance(package_dir_value, str):
                continue
            package_root = (root / package_dir_value).resolve()
            try:
                package_rel = package_root.relative_to(root.resolve()).as_posix()
            except ValueError:
                continue
            package_lakefile = package_root / "lakefile.lean"
            if not package_lakefile.is_file():
                continue
            package_text = package_lakefile.read_text(encoding="utf-8", errors="replace")
            package_src_root = package_root / _package_source_dir(package_text, ".")
            package_specs.append((str(package.get("name") or package_rel),
                                  package_rel, package_root, package_src_root))

    result: list[dict[str, Any]] = []
    for package_name, package_rel, package_root, package_src_root in package_specs:
        lakefile_path = package_root / "lakefile.lean"
        if not lakefile_path.is_file():
            continue
        text = lakefile_path.read_text(encoding="utf-8", errors="replace")
        for target in parse_lake_targets(text, package_root):
            source_root = (package_src_root / target["sourceDir"]).resolve()
            try:
                source_root_rel = source_root.relative_to(root.resolve()).as_posix()
            except ValueError:
                target["sourceRoot"] = None
                target["sourceRootStatus"] = "outside_repository"
            else:
                target["sourceRoot"] = source_root_rel
                target["sourceRootStatus"] = (
                    "lake_static_configuration" if source_root.is_dir()
                    else "declared_source_root_missing"
                )
            target["packageName"] = package_name
            target["packageRoot"] = package_rel
            result.append(target)
    return result


def _strip_lean_comments(text: str) -> str:
    """Remove Lean line/nested block comments while preserving line positions."""
    output: list[str] = []
    index = 0
    block_depth = 0
    line_comment = False
    in_string = False
    escaped = False
    while index < len(text):
        pair = text[index:index + 2]
        char = text[index]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                index += 2
            elif pair == "-/":
                block_depth -= 1
                index += 2
            else:
                if char == "\n":
                    output.append("\n")
                index += 1
        elif line_comment:
            if char == "\n":
                output.append("\n")
                line_comment = False
            index += 1
        elif in_string:
            output.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
        elif pair == "/-":
            block_depth = 1
            index += 2
        elif pair == "--":
            line_comment = True
            index += 2
        else:
            output.append(char)
            if char == '"':
                in_string = True
            index += 1
    return "".join(output)


# Lean module identifiers can contain Unicode letters (for example, "Möbius").
# Require complete whitespace-separated module tokens: a permissive findall
# splits such identifiers into false missing-import edges and turns malformed
# quoted/path-like import text into several unrelated names.
LEAN_MODULE_IDENTIFIER = r"(?:[^\W\d]|_)[\w']*"
LEAN_MODULE_SEGMENT = rf"(?:{LEAN_MODULE_IDENTIFIER}|«[^»]+»)"
LEAN_MODULE_NAME = re.compile(
    rf"{LEAN_MODULE_SEGMENT}(?:\.{LEAN_MODULE_SEGMENT})*", re.UNICODE
)


def lean_module_index(root: Path, paths: Iterable[str], targets: list[dict[str, Any]],
                      package_source_dir: str = "lean", *,
                      candidate_module_by_path: dict[str, str] | None = None,
                      candidate_source_root_by_path: dict[str, str] | None = None) -> tuple[
                          dict[str, str], dict[str, list[str]], list[dict[str, Any]]
                      ]:
    """Index modules declared by Lake roots/globs and their local import closure."""
    candidate_modules: dict[tuple[str, str], str] = {}
    candidate_imports: dict[str, list[str]] = {}
    import_diagnostics: list[dict[str, Any]] = []
    source_roots: list[Path] = []
    for target in targets:
        source_root = (root / target["sourceRoot"]).resolve() \
            if isinstance(target.get("sourceRoot"), str) else \
            (root / package_source_dir / target["sourceDir"]).resolve()
        try:
            source_root.relative_to(root.resolve())
        except ValueError:
            continue
        if source_root.is_dir():
            source_roots.append(source_root)
    source_roots = sorted(set(source_roots), key=lambda path: len(path.parts), reverse=True)
    for rel in paths:
        if (not rel.endswith(".lean") or Path(rel).name == "lakefile.lean"
                or rel.startswith("external_refs/")):
            continue
        # Module identity follows the lexical path Lake sees. Resolving first
        # loses in-tree symlink aliases whose target lives outside srcDir.
        absolute = root / rel
        module = None
        for source_root in source_roots:
            try:
                suffix = absolute.relative_to(source_root)
            except ValueError:
                continue
            module = suffix.with_suffix("").as_posix().replace("/", ".")
            if not LEAN_MODULE_NAME.fullmatch(module):
                module = None
            break
        if not module:
            continue
        if candidate_module_by_path is not None:
            candidate_module_by_path[rel] = module
        source_root_key = source_root.relative_to(root.resolve()).as_posix()
        if candidate_source_root_by_path is not None:
            candidate_source_root_by_path[rel] = source_root_key
        candidate_modules[(source_root_key, module)] = rel
        try:
            text = (root / rel).read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        modules: list[str] = []
        for line_number, line in enumerate(_strip_lean_comments(text).splitlines(), 1):
            match = re.match(r"^\s*(?:(?:public|meta)\s+)?import\s+(.+)$", line)
            if match:
                imported = re.sub(r"^(?:all)\s+", "", match.group(1).strip())
                names = imported.split()
                if names and all(LEAN_MODULE_NAME.fullmatch(name) for name in names):
                    modules.extend(re.sub(r"«([^»]+)»", r"\1", name) for name in names)
                else:
                    import_diagnostics.append({
                        "sourcePath": rel,
                        "line": line_number,
                        "rawImport": match.group(1).strip(),
                        "status": "unsupported_import_name_syntax",
                        "evidence": "Lean import command text; module edges withheld",
                    })
        candidate_imports[rel] = list(dict.fromkeys(modules))

    module_to_path: dict[str, str] = {}
    imports_by_path: dict[str, list[str]] = {}
    candidate_path_to_module = {rel: module for (_, module), rel in candidate_modules.items()}
    for target in targets:
        source_root_value = target.get("sourceRoot")
        if not isinstance(source_root_value, str):
            continue
        target_modules = {
            module: rel for (source_root, module), rel in candidate_modules.items()
            if source_root == Path(source_root_value).as_posix()
        }
        seeds: set[str] = set()
        for root_module in target.get("roots", []):
            if root_module in target_modules:
                seeds.add(root_module)
        for glob in target.get("globs", []):
            prefix = glob["module"]
            for module in target_modules:
                if ((glob["includeSelf"] and module == prefix)
                        or (glob.get("includeSubmodules", True)
                            and module.startswith(prefix + "."))):
                    seeds.add(module)
        queue = deque(target_modules[module] for module in sorted(seeds))
        seen_paths: set[str] = set()
        while queue:
            rel = queue.popleft()
            if rel in seen_paths:
                continue
            seen_paths.add(rel)
            module = candidate_path_to_module.get(rel)
            if module is not None:
                module_to_path.setdefault(module, rel)
            for imported in candidate_imports.get(rel, []):
                local_path = target_modules.get(imported)
                if local_path is not None:
                    queue.append(local_path)

    # Preserve imports from every source candidate under a declared Lake
    # source root. Reachability controls build ownership, not whether a real
    # source dependency is retained in the repository graph.
    imports_by_path = candidate_imports
    return module_to_path, imports_by_path, import_diagnostics


def _target_membership(root: Path, targets: list[dict[str, Any]],
                       module_to_path: dict[str, str],
                       imports_by_path: dict[str, list[str]]) -> dict[str, list[str]]:
    path_to_module = {path: module for module, path in module_to_path.items()}
    module_to_targets: dict[str, list[str]] = defaultdict(list)
    for target in targets:
        source_root_value = target.get("sourceRoot")
        if not isinstance(source_root_value, str):
            continue
        source_root = (root / source_root_value).resolve()
        target_modules: dict[str, str] = {}
        for module, rel_path in module_to_path.items():
            try:
                (root / rel_path).relative_to(source_root)
            except ValueError:
                continue
            target_modules[module] = rel_path
        for glob in target.get("globs", []):
            prefix = glob["module"]
            for module in target_modules:
                if ((module == prefix and glob["includeSelf"])
                        or (glob.get("includeSubmodules", True)
                            and module.startswith(prefix + "."))):
                    module_to_targets[module].append(target["name"])
        for root_module in target["roots"]:
            root_path = target_modules.get(root_module)
            if root_path is None:
                continue
            queue = deque([root_path])
            seen: set[str] = set()
            while queue:
                path = queue.popleft()
                if path in seen:
                    continue
                seen.add(path)
                module = path_to_module.get(path)
                if module:
                    module_to_targets[module].append(target["name"])
                for imported in imports_by_path.get(path, []):
                    local_path = target_modules.get(imported)
                    if local_path is not None:
                        queue.append(local_path)
        # Keep executable and library source roots distinct when they overlap.
    return {module: sorted(set(names)) for module, names in module_to_targets.items()}


def _unindexed_import_source(root: Path, module: str,
                             targets: list[dict[str, Any]]) -> str | None:
    """Resolve a conventional Lean module file outside the selected module map."""
    module_path = Path(*module.split(".")).with_suffix(".lean")
    source_roots = sorted(
        {target["sourceRoot"] for target in targets
         if isinstance(target.get("sourceRoot"), str)},
        key=lambda value: len(Path(value).parts), reverse=True,
    )
    for source_root in source_roots:
        candidate = (root / source_root / module_path).resolve()
        try:
            relative = candidate.relative_to(root.resolve()).as_posix()
        except ValueError:
            continue
        if candidate.is_file():
            return relative
    return None


def _external_reference_import_source(root: Path, module: str) -> str | None:
    """Resolve a module directly inside an external-ref boundary, without indexing it."""
    module_path = Path(*module.split(".")).with_suffix(".lean")
    external_root = root / "external_refs"
    if not external_root.is_dir():
        return None
    try:
        submodules = sorted(external_root.iterdir(), key=lambda path: path.name)
    except OSError:
        return None
    for submodule in submodules:
        if not submodule.is_dir():
            continue
        try:
            submodule_root = submodule.resolve()
            candidate = (submodule_root / module_path).resolve()
            candidate.relative_to(submodule_root)
        except (OSError, RuntimeError, ValueError):
            continue
        if candidate.is_file():
            try:
                return candidate.relative_to(root.resolve()).as_posix()
            except ValueError:
                continue
    return None


def _manifest_external_import_source(root: Path, module: str) -> dict[str, str] | None:
    """Resolve imports to already-present sources in pinned Lake dependencies."""
    manifest_path = root / "lake-manifest.json"
    if not manifest_path.is_file():
        return None
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    packages_dir = Path(str(manifest.get("packagesDir") or ".lake/packages"))
    module_path = Path(*module.split(".")).with_suffix(".lean")
    for package in manifest.get("packages", []):
        if not isinstance(package, dict) or package.get("type") == "path":
            continue
        package_name = package.get("name")
        if not isinstance(package_name, str):
            continue
        package_root = root / packages_dir / package_name
        if isinstance(package.get("subDir"), str):
            package_root /= package["subDir"]
        config_name = package.get("configFile")
        config_path = package_root / (config_name if isinstance(config_name, str)
                                      else "lakefile.lean")
        source_dir = "."
        if config_path.name.endswith(".lean") and config_path.is_file():
            try:
                config = config_path.read_text(encoding="utf-8", errors="replace")
            except OSError:
                config = ""
            source_dir = _package_source_dir(config, ".")
        candidate = (package_root / source_dir / module_path).resolve()
        if candidate.is_file():
            try:
                relative = candidate.relative_to(root.resolve()).as_posix()
            except ValueError:
                continue
            return {
                "path": relative,
                "packageName": package_name,
                "revision": str(package.get("rev") or package.get("inputRev") or "unknown"),
            }
    return None


def _coarse_group(record: dict[str, Any]) -> str:
    targets = record.get("buildTargets", [])
    if len(targets) == 1:
        return f"lake:{targets[0]}"
    if len(targets) > 1:
        return "lake-multi:" + ",".join(targets)
    directory_parts = Path(record["path"]).parts[:-1]
    if directory_parts:
        return "/".join(directory_parts[:2])
    return record["role"]


def graph_topology(files: list[dict[str, Any]], edges: list[dict[str, Any]],
                   declarations: list[dict[str, Any]]) -> dict[str, Any]:
    """Produce typed subsystem and local / neighborhood structural candidates."""
    records = {row["path"]: row for row in files}
    groups: dict[str, dict[str, Any]] = {}
    module_import_counts: Counter[str] = Counter()
    typed_dependency_counts: dict[str, Counter[str]] = defaultdict(Counter)
    for row in files:
        key = _coarse_group(row)
        group = groups.setdefault(key, {"id": key, "artifactCount": 0,
                                       "roleCounts": Counter(), "internalEdgeCounts": Counter(),
                                       "incomingBoundaryCounts": Counter(),
                                       "outgoingBoundaryCounts": Counter()})
        group["artifactCount"] += 1
        group["roleCounts"][row["role"]] += 1
    for edge in edges:
        source = edge["from"]
        target = edge["to"]
        if source in records and records[source]["role"] == "lean_source" \
                and edge["kind"].startswith("lean_"):
            typed_dependency_counts[source][edge["kind"]] += 1
        # A known repository import remains part of the module's degree even
        # when its destination is outside this selected inventory.
        if source in records and edge["kind"].startswith(("lean_source_import", "python_import")):
            module_import_counts[source] += 1
        if source not in records or target not in records:
            continue
        source_group, target_group = _coarse_group(records[source]), _coarse_group(records[target])
        if source_group == target_group:
            groups[source_group]["internalEdgeCounts"][edge["kind"]] += 1
        else:
            groups[source_group]["outgoingBoundaryCounts"][edge["kind"]] += 1
            groups[target_group]["incomingBoundaryCounts"][edge["kind"]] += 1
    declaration_counts: dict[str, Counter[str]] = defaultdict(Counter)
    for declaration in declarations:
        declaration_counts[declaration["sourcePath"]][declaration["kind"]] += 1
    cohorts: dict[str, list[str]] = defaultdict(list)
    for row in files:
        if row["role"] != "lean_source":
            continue
        profile = {
            "declarationKinds": dict(sorted(declaration_counts[row["path"]].items())),
            "repoImportOutDegree": module_import_counts[row["path"]],
            "typedDependencyCounts": dict(sorted(typed_dependency_counts[row["path"]].items())),
        }
        signature = hashlib.sha256(json.dumps(profile, sort_keys=True).encode()).hexdigest()
        cohorts[signature].append(row["path"])
    cohort_candidates = [
        {"signature": signature, "members": sorted(members),
         "profile": {
             "declarationKinds": dict(sorted(declaration_counts[members[0]].items())),
             "repoImportOutDegree": module_import_counts[members[0]],
             "typedDependencyCounts": dict(sorted(typed_dependency_counts[members[0]].items())),
         },
         "lakeTargetMemberships": {
             member: records[member].get("buildTargets", []) for member in sorted(members)
         },
         "evidence": ["lexical_declaration_kind_counts", "repo_import_out_degree",
                      "typed_dependency_counts"],
         "status": "structural_candidate_requires_owner_review"}
        for signature, members in sorted(cohorts.items()) if len(members) > 1
    ]

    # Relation-labeled directed 1-WL color refinement (Shervashidze et al.,
    # JMLR 12 (2011)) gives one-hop and two-hop candidates. These colors are
    # fingerprints, not complete graph-isomorphism tests. File names and Lake
    # target membership stay outside the color so matches cross those boundaries.
    node_labels = {
        path: hashlib.sha256(json.dumps({
            "role": record["role"],
            "declarationKinds": dict(sorted(declaration_counts[path].items())),
        }, sort_keys=True).encode()).hexdigest()
        for path, record in records.items()
    }
    neighborhood_edges: dict[str, list[tuple[str, str, str | None, str]]] = defaultdict(list)
    for edge in edges:
        source, target, kind = edge["from"], edge["to"], edge["kind"]
        if (source not in records or records[source]["role"] != "lean_source"
                or not kind.startswith("lean_")):
            continue
        dependency_package = edge.get("dependencyPackage")
        imported_module = edge.get("importedModule")
        if isinstance(dependency_package, str):
            boundary_label = f"package:{dependency_package}"
        elif isinstance(imported_module, str) and imported_module:
            boundary_label = f"module-root:{imported_module.split('.', 1)[0]}"
        else:
            boundary_label = f"boundary:{kind}"
        neighborhood_edges[source].append((
            "out", kind, target if target in records else None, boundary_label
        ))
        if target in records:
            neighborhood_edges[target].append(("in", kind, source, boundary_label))

    neighborhood_candidates: list[dict[str, Any]] = []
    colors = node_labels
    for depth in (1, 2):
        refined: dict[str, str] = {}
        for path in records:
            neighborhood: Counter[tuple[str, str, str]] = Counter()
            for direction, kind, neighbor, boundary_label in neighborhood_edges.get(path, []):
                neighbor_color = colors[neighbor] if neighbor is not None else boundary_label
                neighborhood[(direction, kind, neighbor_color)] += 1
            profile = {
                "self": colors[path],
                "typedNeighborhood": [
                    [direction, kind, neighbor_color, count]
                    for (direction, kind, neighbor_color), count
                    in sorted(neighborhood.items())
                ],
            }
            refined[path] = hashlib.sha256(
                json.dumps(profile, sort_keys=True).encode()
            ).hexdigest()
        colors = refined
        color_members: dict[str, list[str]] = defaultdict(list)
        for path, record in records.items():
            if record["role"] == "lean_source":
                color_members[colors[path]].append(path)
        neighborhood_candidates.extend(
            {
                "depth": depth,
                "signature": signature,
                "members": sorted(members),
                "lakeTargetMemberships": {
                    member: records[member].get("buildTargets", [])
                    for member in sorted(members)
                },
                "evidence": ["typed_directed_lean_import_neighborhood",
                             "lexical_declaration_kind_counts"],
                "status": "structural_candidate_requires_owner_review",
            }
            for signature, members in sorted(color_members.items()) if len(members) > 1
        )
    clean_groups = []
    for key, group in sorted(groups.items()):
        clean_groups.append({
            "id": key,
            "artifactCount": group["artifactCount"],
            "roleCounts": dict(sorted(group["roleCounts"].items())),
            "internalEdgeCounts": dict(sorted(group["internalEdgeCounts"].items())),
            "incomingBoundaryCounts": dict(sorted(group["incomingBoundaryCounts"].items())),
            "outgoingBoundaryCounts": dict(sorted(group["outgoingBoundaryCounts"].items())),
            "status": "path_or_lake_target_coarse_grain",
        })
    return {
        "nodeCount": len(files),
        "typedEdgeCounts": dict(sorted(Counter(edge["kind"] for edge in edges).items())),
        "coarseGrainMethod": "Lake target when uniquely assigned; otherwise first two path components",
        "coarseGroups": clean_groups,
        "structuralCohortCandidates": cohort_candidates,
        "structuralCohortStatus": "candidate grouping only; not semantic archetype assignment",
        "neighborhoodCohortCandidates": neighborhood_candidates,
        "neighborhoodCohortStatus": (
            "one-hop and two-hop relation-aware Weisfeiler-Lehman candidates; "
            "not semantic archetype assignment"
        ),
    }


def _python_graph(root: Path, scan_dirs: list[str]) -> Any:
    from tools.infra.python_dag_dependency_oracle import HighSpeedDependencyGraph

    graph = HighSpeedDependencyGraph(root, scan_dirs=scan_dirs)
    graph.analyze_all()
    return graph


def _owner_membership_summary(files: Iterable[dict[str, Any]]) -> dict[str, Any]:
    """Count actual owners without turning overlaps or unresolved sentinels into names."""
    counts: Counter[str] = Counter()
    ambiguous = 0
    unresolved = 0
    for record in files:
        owner = record.get("owner", "unresolved")
        owners = owner if isinstance(owner, list) else [owner]
        real_owners = [str(target) for target in owners
                       if isinstance(target, str)
                       and target != "unresolved"
                       and not target.startswith("unresolved_")
                       and target != "lake_target_pending_resolution"]
        counts.update(real_owners)
        has_unresolved_owner = len(real_owners) != len(owners)
        if record.get("ownerStatus") == "ambiguous_multiple_lake_roots":
            ambiguous += 1
        elif record.get("ownerStatus") in {
                "uncertain_no_root_reachability",
                "uncertain_module_not_in_lake_target_index"} or has_unresolved_owner:
            unresolved += 1
    return {
        "ownerCount": len(counts),
        "largestOwnerGroups": dict(counts.most_common(30)),
        "ownerMembershipCount": sum(counts.values()),
        "ambiguousOwnerArtifactCount": ambiguous,
        "unresolvedOwnerArtifactCount": unresolved,
    }


DECLARATION_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial|opaque)\s+)*"
    r"(theorem|lemma|def|abbrev|opaque|structure|class|inductive|instance)\s+"
    r"([^\s:({]+)"
)


def lean_declaration_candidates(root: Path, paths: Iterable[str]) -> list[dict[str, Any]]:
    """Extract lexical declaration headers; this is navigation, not Lean parsing."""
    declarations: list[dict[str, Any]] = []
    for rel in paths:
        if not rel.startswith("lean/") or not rel.endswith(".lean"):
            continue
        try:
            lines = (root / rel).read_text(encoding="utf-8", errors="replace").splitlines()
        except OSError:
            continue
        namespace: list[str] = []
        for number, line in enumerate(lines, start=1):
            namespace_match = re.match(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$", line)
            if namespace_match:
                namespace.append(namespace_match.group(1))
                continue
            end_match = re.match(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$", line)
            if end_match:
                if namespace and (not end_match.group(1)
                                  or namespace[-1].split(".")[-1] == end_match.group(1).split(".")[-1]):
                    namespace.pop()
                continue
            match = DECLARATION_RE.match(line)
            if match:
                declarations.append({
                    "sourcePath": rel,
                    "line": number,
                    "kind": match.group(1),
                    "name": match.group(2),
                    "namespaceContext": ".".join(namespace),
                    "status": "lexical_candidate_not_lean_parser_output",
                })
    return declarations


def build_refactoring_map(root: Path = ROOT, *, paths: list[str] | None = None,
                          python_scan: bool = True,
                          git_history: bool = False,
                          compiler_meta: Path | None = None,
                          git_path_events_output: Path | None = None,
                          git_path_event_paths: set[str] | None = None) -> dict[str, Any]:
    if git_path_events_output is not None and not git_history:
        raise ValueError("--git-path-events-out requires git_history=True")
    if git_path_event_paths is not None and git_path_events_output is None:
        raise ValueError("Git path-event path filters require --git-path-events-out")
    explicit_path_scope = paths is not None
    paths = paths if paths is not None else tracked_paths(root)
    paths = sorted(set(paths))
    symlink_metadata = {rel: _symlink_metadata(root, rel) for rel in paths}
    watched_paths = set(paths)
    watched_paths.update(
        row["symlinkResolvedPath"] for row in symlink_metadata.values()
        if row.get("symlinkResolvedPath") is not None
    )
    watched_paths = sorted(watched_paths)
    initial_file_state = _worktree_file_state(root, watched_paths)
    scanner_path = Path(__file__).resolve()
    manifest_path = root / "lake-manifest.json"
    scanner_sha_before = _sha256_path(scanner_path)
    manifest_sha_before = _sha256_path(manifest_path)
    lakefile = root / "lakefile.lean"
    targets = _lake_package_targets(root, paths)
    package_src = re.search(r'^\s*srcDir\s*:=\s*"([^"]+)"',
                            (root / "lakefile.lean").read_text(encoding="utf-8"), re.M) \
        if (root / "lakefile.lean").is_file() else None
    package_source_dir = package_src.group(1) if package_src else "lean"
    candidate_module_by_path: dict[str, str] = {}
    candidate_source_root_by_path: dict[str, str] = {}
    module_to_path, lean_imports, lean_import_diagnostics = lean_module_index(
        root, paths, targets, package_source_dir,
        candidate_module_by_path=candidate_module_by_path,
        candidate_source_root_by_path=candidate_source_root_by_path,
    )
    path_to_module = {path: module for module, path in module_to_path.items()}
    module_targets = _target_membership(root, targets, module_to_path, lean_imports)

    python_graph = _python_graph(root, ["tools", "src", "tests"]) if python_scan else None
    files: list[dict[str, Any]] = []
    edges: list[dict[str, Any]] = []
    role_counts: Counter[str] = Counter()
    component_counts: Counter[str] = Counter()
    for rel in paths:
        classification = classify_file(rel)
        if (classification["role"] == "lean_candidate_outside_package_source"
                and rel in path_to_module):
            classification = {
                "role": "lean_source",
                "status": "lake_package_source_observed",
                "owner": "lake_target_pending_resolution",
            }
        record: dict[str, Any] = {"path": rel, **classification}
        record.update(symlink_metadata[rel])
        if rel in candidate_module_by_path and rel not in path_to_module:
            record["moduleCandidate"] = candidate_module_by_path[rel]
            record["moduleCandidateSourceRoot"] = candidate_source_root_by_path[rel]
            record["moduleCandidateStatus"] = "lexical_source_root_candidate_not_lake_indexed"
        if rel in path_to_module:
            module = path_to_module[rel]
            owners = module_targets.get(module, [])
            record["module"] = module
            record["buildTargets"] = owners
            if len(owners) == 1:
                record["owner"] = owners[0]
                record["ownerStatus"] = "lake_import_closure_candidate"
            elif len(owners) > 1:
                record["owner"] = owners
                record["ownerStatus"] = "ambiguous_multiple_lake_roots"
            else:
                record["owner"] = "unresolved_lean_build_owner"
                record["ownerStatus"] = "uncertain_no_root_reachability"
        elif record["role"] == "lean_source":
            record["status"] = "lake_module_index_unresolved"
            record["owner"] = "unresolved_lean_module"
            record["ownerStatus"] = "uncertain_module_not_in_lake_target_index"
        if python_graph is not None and rel in python_graph.records:
            py_record = python_graph.records[rel]
            record["pythonCpgRole"] = py_record.classification
            record["pythonCpgRoleStatus"] = "heuristic_dependency_oracle"
            record["pythonImporters"] = py_record.direct_importers
            record["pythonTestReferences"] = sorted(
                source for source, imported in python_graph.import_graph.items()
                if rel in imported and source.startswith("tests/")
            )
        if not rel.startswith("external_refs/"):
            try:
                raw = (root / rel).read_bytes()
                record["contentSha256"] = hashlib.sha256(raw).hexdigest()
                record["sizeBytes"] = len(raw)
                generated_marker = _generated_source_marker(raw)
                if (generated_marker is not None and Path(rel).suffix.lower() in SOURCE_SUFFIXES
                        and record["role"] in {"lean_source", "lean_candidate_outside_package_source",
                                                "repository_source_candidate", "source_file_unclassified"}):
                    record["role"] = "generated_source_artifact"
                    record["status"] = "content_marker_observed_candidate"
                    record["owner"] = "generated_source_content_marker"
                    record["contentRoleEvidence"] = generated_marker
            except OSError:
                record["contentStatus"] = "unreadable"
        role_counts[record["role"]] += 1
        if isinstance(record.get("component"), str):
            component_counts[record["component"]] += 1
        files.append(record)
    owner_summary = _owner_membership_summary(files)

    history_summary: dict[str, Any] = {
        "status": "not_requested",
        "revision": "HEAD",
        "pathCount": 0,
        "pathsWithEvents": 0,
    }
    if git_history:
        from tools.infra.evolution_extract import aggregate_current_path_lineage
        current_path_set = {row["path"] for row in files}
        event_paths = (set(git_path_event_paths) if git_path_event_paths is not None
                       else current_path_set)
        unknown_event_paths = event_paths - current_path_set
        if unknown_event_paths:
            raise ValueError(f"Git path-event filters are absent from scan: {sorted(unknown_event_paths)[:5]}")
        event_count = 0
        event_stream_digest = hashlib.sha256()
        if git_path_events_output is not None:
            event_path = git_path_events_output.resolve()
            if event_path.exists():
                raise FileExistsError(f"refusing to overwrite Git path event stream: {event_path}")
            event_path.parent.mkdir(parents=True, exist_ok=True)
            temp_path = event_path.with_name(f".{event_path.name}.partial-{os.getpid()}")
            try:
                with temp_path.open("x", encoding="utf-8") as event_stream:
                    def emit_event(event: dict[str, Any]) -> None:
                        nonlocal event_count
                        if event["artifactPath"] not in event_paths:
                            return
                        serialized_event = json.dumps(event, sort_keys=True) + "\n"
                        event_stream.write(serialized_event)
                        event_stream_digest.update(serialized_event.encode("utf-8"))
                        event_count += 1

                    lineage = aggregate_current_path_lineage(
                        root, [row["path"] for row in files], event_callback=emit_event
                    )
                    event_stream.flush()
                    os.fsync(event_stream.fileno())
                temp_path.replace(event_path)
            except BaseException:
                temp_path.unlink(missing_ok=True)
                raise
        else:
            lineage = aggregate_current_path_lineage(root, [row["path"] for row in files])
        for record in files:
            record["gitPathHistory"] = lineage[record["path"]]
        history_summary = {
            "status": "path_history_candidate",
            "revision": next((item.get("historyRevision") for item in lineage.values()), None),
            "pathCount": len(lineage),
            "pathsWithEvents": sum(item["touchCount"] > 0 for item in lineage.values()),
            "eventStreamCount": event_count if git_path_events_output is not None else None,
            "eventStreamSha256": event_stream_digest.hexdigest() if git_path_events_output is not None else None,
            "eventStreamPath": str(git_path_events_output) if git_path_events_output is not None else None,
            "eventStreamScope": (
                {"mode": "all_current_paths"} if git_path_event_paths is None
                else {"mode": "selected_current_paths", "artifactPaths": sorted(event_paths)}
            ) if git_path_events_output is not None else None,
            "authority": "Git name-status events and reverse rename candidates; no source-content identity claim",
        }

    file_record_by_path = {record["path"]: record for record in files}
    unresolved_imports_by_role: Counter[str] = Counter()
    for source_path, imported_modules in lean_imports.items():
        for module in imported_modules:
            target_path = module_to_path.get(module)
            resolution = "source_observed_in_inventory"
            kind = "lean_source_import"
            status = "source_observed"
            external_content_hash: str | None = None
            if target_path is None:
                target_path = _unindexed_import_source(root, module, targets)
                if target_path is not None:
                    if target_path.startswith("external_refs/"):
                        kind = "lean_external_reference_import"
                        status = "external_reference_source_present"
                        resolution = "external_reference_file_observed_by_module_path"
                    else:
                        kind = "lean_source_import_outside_inventory"
                        status = ("repo_source_present_outside_selected_inventory"
                                  if explicit_path_scope else
                                  "repo_source_present_outside_declared_target_module_set")
                        resolution = "repo_source_file_observed_by_module_path"
                else:
                    dependency_source = _manifest_external_import_source(root, module)
                    if dependency_source is not None:
                        target_path = dependency_source["path"]
                        kind = "lean_external_package_import"
                        status = "pinned_dependency_source_present"
                        resolution = "lake_manifest_dependency_source_observed"
                    elif module.split(".", 1)[0] in {"Init", "Lean", "Lake", "Std"}:
                        kind = "lean_toolchain_import"
                        status = "lean_toolchain_module_namespace"
                        resolution = "known_lean_toolchain_namespace"
                    else:
                        external_ref_source = _external_reference_import_source(root, module)
                        if external_ref_source is not None:
                            target_path = external_ref_source
                            kind = "lean_external_reference_import"
                            status = "external_reference_source_present"
                            resolution = "external_submodule_source_observed_by_module_path"
                            external_content_hash = _sha256_path(root / external_ref_source)
                        else:
                            kind = "lean_import_without_repo_source"
                            status = "unresolved_local_module; dependency_or_toolchain_source_not_found"
                            resolution = "no_local_or_cached_dependency_source_resolved"
            edges.append({
                "from": source_path,
                "to": target_path or module,
                "kind": kind,
                "importedModule": module,
                "evidence": "Lean import command",
                "status": status,
                "resolution": resolution,
            })
            if kind == "lean_import_without_repo_source":
                source_record = file_record_by_path.get(source_path, {})
                unresolved_imports_by_role[
                    str(source_record.get("role", "source_missing_from_inventory"))
                ] += 1
            if (kind == "lean_external_reference_import" and target_path is not None
                    and external_content_hash is None):
                external_content_hash = _sha256_path(root / target_path)
            if kind == "lean_external_reference_import" and external_content_hash is not None:
                edges[-1]["contentSha256"] = external_content_hash
            if target_path is not None and kind == "lean_external_package_import":
                edges[-1]["dependencyRevision"] = dependency_source["revision"]
                edges[-1]["dependencyPackage"] = dependency_source["packageName"]
    declarations = lean_declaration_candidates(
        root, (row["path"] for row in files if row["role"] == "lean_source")
    )
    for declaration in declarations:
        source_record = file_record_by_path.get(declaration["sourcePath"], {})
        declaration["module"] = source_record.get("module")
        declaration["buildTargets"] = source_record.get("buildTargets", [])
    if python_graph is not None:
        for source_path, targets_set in python_graph.import_graph.items():
            if source_path not in file_record_by_path:
                continue
            for target_path in sorted(targets_set):
                outside_inventory = target_path not in file_record_by_path
                edges.append({"from": source_path, "to": target_path,
                              "kind": "python_import", "evidence": "Python AST import",
                              "status": ("static_import_candidate_outside_inventory"
                                         if outside_inventory else "static_import_candidate")})
                if source_path.startswith("tests/"):
                    edges.append({"from": source_path, "to": target_path,
                                  "kind": "test_import", "evidence": "Python AST import",
                                  "status": ("static_test_dependency_outside_inventory"
                                             if outside_inventory else "static_test_dependency")})
    path_set = {row["path"] for row in files}
    for row in files:
        alias_target = row.get("symlinkResolvedPath")
        if row.get("filesystemEntry") == "symlink" and alias_target:
            edges.append({
                "from": row["path"],
                "to": alias_target,
                "kind": "filesystem_symlink_alias",
                "evidence": "filesystem symlink target",
                "status": "path_alias" if alias_target in path_set else "target_outside_inventory",
            })
    topology = graph_topology(files, edges, declarations)

    tree = hashlib.sha256()
    filesystem_topology = hashlib.sha256()
    for row in files:
        tree.update(row["path"].encode("utf-8", errors="surrogateescape"))
        tree.update(b"\0")
        tree.update(row.get("contentSha256", "unreadable-or-external").encode())
        tree.update(b"\0")
        if row.get("filesystemEntry") == "symlink":
            filesystem_topology.update(row["path"].encode("utf-8", errors="surrogateescape"))
            filesystem_topology.update(b"\0")
            filesystem_topology.update(str(row.get("symlinkTarget") or "").encode(
                "utf-8", errors="surrogateescape"))
            filesystem_topology.update(b"\0")
            filesystem_topology.update(str(row.get("symlinkResolvedPath") or "").encode(
                "utf-8", errors="surrogateescape"))
            filesystem_topology.update(b"\0")
    git_head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root,
                              check=False, capture_output=True, text=True)
    git_head_value = git_head.stdout.strip() if git_head.returncode == 0 else None
    git_history_head_consistent = (
        not git_history or history_summary.get("revision") in (None, git_head_value)
    )
    if git_history and history_summary.get("revision") is None:
        history_summary["revision"] = git_head_value
    dirty = subprocess.run(["git", "status", "--porcelain"],
                           cwd=root, check=False, capture_output=True, text=True)
    final_inventory_paths = tracked_paths(root) if not explicit_path_scope else paths
    initial_inventory_paths = set(paths)
    final_inventory_path_set = set(final_inventory_paths)
    added_paths = sorted(final_inventory_path_set - initial_inventory_paths)
    removed_paths = sorted(initial_inventory_paths - final_inventory_path_set)
    final_file_state = _worktree_file_state(root, watched_paths)
    scanner_sha_after = _sha256_path(scanner_path)
    manifest_sha_after = _sha256_path(manifest_path)
    initial_state_by_path, final_state_by_path = dict(initial_file_state), dict(final_file_state)
    changed_paths = sorted(set(
        path for path in set(initial_state_by_path) | set(final_state_by_path)
        if initial_state_by_path.get(path) != final_state_by_path.get(path)
    ) | set(added_paths) | set(removed_paths))
    changed_paths_sha256 = hashlib.sha256(json.dumps(
        changed_paths, ensure_ascii=False, separators=(",", ":")
    ).encode("utf-8")).hexdigest()
    worktree_consistent = (initial_file_state == final_file_state
                           and not added_paths and not removed_paths
                           and git_history_head_consistent)
    analysis_inputs_consistent = (
        scanner_sha_before is not None
        and scanner_sha_before == scanner_sha_after
        and manifest_sha_before is not None
        and manifest_sha_before == manifest_sha_after
    )
    if git_history:
        consistency_status = ("stable_path_and_git_revision_during_scan" if worktree_consistent
                              else "paths_or_git_revision_changed_during_scan")
    else:
        consistency_status = ("stable_path_state_during_scan" if worktree_consistent
                              else "paths_changed_during_scan")
    meta_path = compiler_meta or root / "artifacts/dag/index/meta.json"
    compiler_evidence: dict[str, Any]
    if meta_path.is_file():
        try:
            meta = json.loads(meta_path.read_text(encoding="utf-8"))
            try:
                from tools.infra.build import compute_lean_source_hash

                current_source_hash = compute_lean_source_hash(root)
                source_hash_matches = bool(
                    current_source_hash and meta.get("sourceHash") == current_source_hash
                )
                source_check_error = None
            except (OSError, RuntimeError, ValueError) as exc:
                current_source_hash = None
                source_hash_matches = None
                source_check_error = f"{type(exc).__name__}: {exc}"
            if source_hash_matches is False:
                artifact_status = "stale_source_generation"
                join_status = "source_hash_mismatch_do_not_join"
            elif source_hash_matches is True:
                artifact_status = "source_hash_matches_olean_and_rows_unverified"
                join_status = "source_match_only_olean_and_output_integrity_unverified"
            else:
                artifact_status = "source_binding_unavailable"
                join_status = "not_joined_source_hash_check_unavailable"
            compiler_evidence = {
                "status": artifact_status,
                "metadataPath": str(meta_path.relative_to(root)) if meta_path.is_relative_to(root) else str(meta_path),
                "timestamp": meta.get("timestamp"),
                "importRoot": meta.get("importRoot"),
                "sourceHash": meta.get("sourceHash"),
                "currentSourceHash": current_source_hash,
                "sourceHashMatchesCurrent": source_hash_matches,
                "sourceCheckError": source_check_error,
                "oleanHash": meta.get("oleanHash"),
                "nodeCount": meta.get("nodeCount"),
                "edgeCount": meta.get("edgeCount"),
                "joinStatus": join_status,
            }
            fingerprint_evidence, per_file_fingerprints = _compiler_fingerprint_summaries(
                root, meta_path, meta, current_source_hash,
                worktree_consistent and analysis_inputs_consistent
                and source_hash_matches is True,
            )
            compiler_evidence["fingerprintIntegration"] = fingerprint_evidence
            if fingerprint_evidence.get("status") == "source_olean_and_export_hashes_verified":
                compiler_evidence["status"] = "source_olean_and_export_hashes_verified"
                compiler_evidence["joinStatus"] = "verified_fingerprint_rows_joined_by_source_file"
            else:
                compiler_evidence["joinStatus"] = fingerprint_evidence.get(
                    "status", "compiler_fingerprint_join_rejected",
                )
            for file_record in files:
                fingerprint_summary = per_file_fingerprints.get(file_record["path"])
                if fingerprint_summary is not None:
                    file_record["compilerFingerprints"] = fingerprint_summary
                if "gitPathHistory" in file_record:
                    file_record["evolutionaryLineage"] = {
                        "joinKey": file_record["path"],
                        "currentDnaField": (
                            "compilerFingerprints" if fingerprint_summary is not None else None
                        ),
                        "fossilField": "gitPathHistory",
                        "status": (
                            "current_fingerprint_joined_to_path_fossils"
                            if fingerprint_summary is not None
                            else "path_fossils_without_verified_current_fingerprint"
                        ),
                        "relation": "path_continuity_candidate_not_historical_content_identity",
                    }
        except (OSError, json.JSONDecodeError):
            compiler_evidence = {"status": "metadata_unreadable", "joinStatus": "not_joined"}
    else:
        compiler_evidence = {"status": "not_found", "joinStatus": "not_joined"}

    return {
        "schema": "info_geometry.refactoring_map.v1",
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "sourceSnapshot": {
            "inventoryScope": "explicit_path_selection" if explicit_path_scope else "repository_worktree_inventory",
            "gitHead": git_head.stdout.strip() if git_head.returncode == 0 else None,
            "gitHeadConsistentWithPathHistory": git_history_head_consistent,
            "worktreeDirty": bool(dirty.stdout.strip()),
            "worktreeConsistentDuringScan": worktree_consistent,
            "consistencyStatus": consistency_status,
            "changedPathCountDuringScan": len(changed_paths),
            "changedPathSampleDuringScan": changed_paths[:20],
            "changedPathsDuringScan": changed_paths,
            "changedPathSetSha256": changed_paths_sha256,
            "addedPathCountDuringScan": len(added_paths),
            "addedPathSampleDuringScan": added_paths[:20],
            "removedPathCountDuringScan": len(removed_paths),
            "removedPathSampleDuringScan": removed_paths[:20],
            "pathContentManifestSha256": tree.hexdigest(),
            "filesystemTopologySha256": filesystem_topology.hexdigest(),
            "pathCount": len(files),
        },
        "analysisProvenance": {
            "scannerPath": scanner_path.relative_to(root).as_posix()
            if scanner_path.is_relative_to(root) else str(scanner_path),
            "scannerSourceSha256": scanner_sha_after,
            "lakeManifestSha256": manifest_sha_after,
            "analysisInputsConsistentDuringScan": analysis_inputs_consistent,
        },
        "authority": {
            "fileRoles": "path rules plus explicit leading source markers; labels retain evidence status",
            "leanDependencies": "source import commands",
            "pythonDependencies": "existing Python AST dependency oracle",
            "buildOwnership": "Lake root/import-closure candidate, not a successful build receipt",
            "compilerFingerprints": "per-file summaries join only when source, olean, output hashes, schema, and row counts verify; digests remain navigation candidates",
        },
        "summary": {
            "roleCounts": dict(sorted(role_counts.items())),
            "componentCounts": dict(sorted(component_counts.items())),
            **owner_summary,
            "edgeCounts": dict(sorted(Counter(edge["kind"] for edge in edges).items())),
            "leanDeclarationCandidateCount": len(declarations),
            "compilerFingerprintJoinedFileCount": sum(
                "compilerFingerprints" in row for row in files
            ),
            "currentDnaToFossilPathJoinCount": sum(
                row.get("evolutionaryLineage", {}).get("status")
                == "current_fingerprint_joined_to_path_fossils" for row in files
            ),
            "uncertainFileClassificationCount": sum(row["status"] == "uncertain" for row in files),
            "uncertainBuildOwnershipCount": sum(
                row.get("ownerStatus") in {
                    "uncertain_no_root_reachability",
                    "uncertain_module_not_in_lake_target_index",
                } for row in files
            ),
            "missingLakeSourceRootCount": sum(
                target.get("sourceRootStatus") == "declared_source_root_missing"
                for target in targets
            ),
            "missingLakeSourceRoots": [
                {"packageName": target.get("packageName"),
                 "target": target.get("name"),
                 "sourceRoot": target.get("sourceRoot")}
                for target in targets
                if target.get("sourceRootStatus") == "declared_source_root_missing"
            ],
            "unindexedLeanSourceCount": sum(
                row.get("ownerStatus") == "uncertain_module_not_in_lake_target_index"
                for row in files
            ),
            "leanImportsWithoutRepoSource": sum(
                edge["kind"] == "lean_import_without_repo_source" for edge in edges
            ),
            "unresolvedLeanImportsBySourceRole": dict(sorted(unresolved_imports_by_role.items())),
            "leanImportParseDiagnosticCount": len(lean_import_diagnostics),
        },
        "lakeTargets": targets,
        "compilerArtifactEvidence": compiler_evidence,
        "gitPathHistory": history_summary,
        "uncertainty": [
            "Leading generated-source markers are self-declared content evidence, not independent generator provenance.",
            "Python CPG roles are heuristic and the oracle omits some dynamic imports.",
            "Lake target membership is inferred from parsed roots and local import closure; it is not build evidence.",
            "A declared Lake source root can be absent from the checkout; such target source roots are reported explicitly and cannot establish ownership.",
            "A matching source hash alone does not validate the olean hash or declaration-row integrity.",
            "Path-derived owners describe repository organization, not human maintainership.",
        ],
        "files": files,
        "leanDeclarationCandidates": declarations,
        "dependencyEdges": edges,
        "leanImportDiagnostics": lean_import_diagnostics,
        "topology": topology,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("/tmp/refactoring-map.json.gz"))
    parser.add_argument("--no-python-cpg", action="store_true",
                        help="skip the existing Python AST dependency oracle")
    parser.add_argument("--git-history", action="store_true",
                        help="stream HEAD ancestry path/status metadata and attach path-continuity candidates")
    parser.add_argument("--git-path-events-out", type=Path,
                        help="optionally stream every current-path fossil event to a new JSONL file")
    parser.add_argument("--git-path-event-path", action="append", default=None,
                        help="limit --git-path-events-out to a current source path; repeatable")
    parser.add_argument("--compiler-meta", type=Path,
                        help="optional declaration-DAG meta.json; fingerprints join only with verified source, olean, and export hashes")
    parser.add_argument("--path", action="append", default=None,
                        help="restrict scanner to an explicit current path; repeatable, partial inventory only")
    args = parser.parse_args()
    report = build_refactoring_map(
        ROOT, paths=args.path, python_scan=not args.no_python_cpg,
        git_history=args.git_history,
        compiler_meta=args.compiler_meta.resolve() if args.compiler_meta else None,
        git_path_events_output=args.git_path_events_out,
        git_path_event_paths=set(args.git_path_event_path) if args.git_path_event_path is not None else None,
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    serialized = json.dumps(report, separators=(",", ":"), ensure_ascii=False)
    if args.out.suffix == ".gz":
        with gzip.open(args.out, "wt", encoding="utf-8") as stream:
            stream.write(serialized)
    else:
        args.out.write_text(serialized, encoding="utf-8")
    print(json.dumps({"out": str(args.out), "sourceSnapshot": report["sourceSnapshot"],
                      "summary": report["summary"],
                      "compilerArtifactEvidence": report["compilerArtifactEvidence"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
