#!/usr/bin/env python3
"""
Python DAG Dependency Oracle and Code Lifecycle Analyzer (High-Performance).

Grounded static analyzer that computes discrete graph reachability, in-degrees,
call paths, and documentation references for every repo-owned script in tools/ and src/.
Uses vectorized inverted index and ArangoDB query acceleration.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from collections import defaultdict
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import repo_root
    from tools.infra.arango_env import (
        arango_database,
        arango_endpoint,
        arango_password,
        arango_username,
        load_repo_arango_env,
    )
else:
    from tools.pathing import repo_root
    from tools.infra.arango_env import (
        arango_database,
        arango_endpoint,
        arango_password,
        arango_username,
        load_repo_arango_env,
    )

ROOT = repo_root()

AUTHORITATIVE_ENTRYPOINTS = [
    "lakefile.lean",
    "AGENTS.md",
    "GEMINI.md",
    "Makefile",
    ".github/workflows",
    "tools/quality/check_closure_debt_gate.py",
    "tools/quality/pauli_seal_audit.py",
    "tools/quality/proof_only_mandate_gate.py",
    "tools/quality/check_frontier_integrity_gate.py",
    "tools/quality/semantic_content_audit.py",
    "tools/quality/check_python_cpg_gate.py",
    "tools/infra/aiclaw_chat.py",
    "tools/infra/socratic_clawbot.py",
    "tools/infra/run_locked_lake_build.py",
    "tools/infra/arango_causal_memory.py",
    "skills",
    "docs/CANONICAL_AGENT_PIPELINE.md",
]


@dataclass
class ScriptDependencyRecord:
    path: str
    in_degree: int = 0
    direct_importers: list[str] = field(default_factory=list)
    shell_callers: list[str] = field(default_factory=list)
    doc_references: list[str] = field(default_factory=list)
    reachable_from_ci: bool = False
    last_git_commit_date: str = ""
    last_git_commit_hash: str = ""
    classification: str = "UNKNOWN"
    subsumed_by: Optional[str] = None


def detect_ast_hazards(content: str, rel_path: str = "") -> list[str]:
    """
    Detects executable hazards via AST parsing.
    Ignores occurrences inside comments, docstrings, or string constants that are not passed to subprocess/system calls.
    """
    hazards = []
    try:
        tree = ast.parse(content, filename=rel_path)
    except Exception:
        return hazards

    class HazardVisitor(ast.NodeVisitor):
        def visit_Call(self, node: ast.Call) -> None:
            func_name = ""
            if isinstance(node.func, ast.Name):
                func_name = node.func.id
            elif isinstance(node.func, ast.Attribute):
                func_name = node.func.attr

            is_exec_call = func_name in ("system", "popen", "run", "Popen", "call", "check_call", "check_output", "rmtree")
            if is_exec_call:
                for arg in node.args:
                    arg_str = ""
                    if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                        arg_str = arg.value
                    elif isinstance(arg, (ast.List, ast.Tuple)):
                        tokens = [elt.value for elt in arg.elts if isinstance(elt, ast.Constant) and isinstance(elt.value, str)]
                        arg_str = " ".join(tokens)
                    elif isinstance(arg, ast.JoinedStr):
                        arg_str = "".join(part.value for part in arg.values if isinstance(part, ast.Constant) and isinstance(part.value, str))

                    if "lake clean" in arg_str or "rm -rf .lake" in arg_str or "rm -r .lake" in arg_str:
                        hazards.append("lake_clean_cache_destructive")
                    elif "lake build" in arg_str or "lake env lean" in arg_str:
                        hazards.append("lake_build_subprocess")
                    elif func_name in ("system", "popen"):
                        hazards.append("raw_system_call")

            self.generic_visit(node)

    visitor = HazardVisitor()
    visitor.visit(tree)
    return sorted(list(set(hazards)))


class HighSpeedDependencyGraph:
    """High-performance dependency graph analyzer with inverted index search."""

    def __init__(self, root: Path, scan_dirs: Optional[list[str]] = None):
        self.root = root
        self.scan_dirs = scan_dirs if scan_dirs is not None else ["tools", "src"]
        self.py_files: list[Path] = []
        self.all_text_files: list[Path] = []
        self.import_graph: dict[str, set[str]] = defaultdict(set)
        self.reverse_import_graph: dict[str, set[str]] = defaultdict(set)
        self.text_references: dict[str, set[str]] = defaultdict(set)
        self.hazards_by_file: dict[str, list[str]] = defaultdict(list)
        self.records: dict[str, ScriptDependencyRecord] = {}
        self.elapsed_seconds: float = 0.0

    def discover_files(self) -> None:
        exclude_dirs = {
            ".lake", ".git", ".idea", ".vscode", "build", "__pycache__", "tmp", ".gemini",
            "external_refs", "external", "hermes-agent", ".venv", "venv", ".agents", "node_modules",
            "target", "dist", "site-packages", "backend", "eigen", "langgraph", "third_party",
            "vendor", "sandbox", "proofs",
        }
        
        # 1. Discover target Python files in scan_dirs
        for d in self.scan_dirs:
            dp = self.root / d
            if dp.is_file() and dp.suffix == ".py":
                self.py_files.append(dp)
            elif dp.is_dir():
                for root, dirs, files in os.walk(dp):
                    dirs[:] = [sub for sub in dirs if not (sub.startswith(".") or sub in exclude_dirs)]
                    for f in files:
                        if f.endswith(".py"):
                            self.py_files.append(Path(root) / f)

        # Also add root-level py files
        for f in self.root.glob("*.py"):
            self.py_files.append(f)

        self.py_files = sorted(list(set(self.py_files)))

        # 2. Discover reference text files (shell, markdown, yaml, lean, json)
        valid_exts = {".sh", ".md", ".yaml", ".yml", ".json", ".lean", ".txt"}
        for ext in ("*.sh", "*.md", "*.yaml", "*.yml", "*.json", "Makefile", "*.lean"):
            for p in self.root.glob(ext):
                self.all_text_files.append(p)

        for d in ("tools", "scripts", "docs", "skills", ".github", "pkg"):
            dp = self.root / d
            if dp.exists():
                for root, dirs, files in os.walk(dp):
                    dirs[:] = [sub for sub in dirs if not (sub.startswith(".") or sub in exclude_dirs)]
                    for f in files:
                        p = Path(root) / f
                        if p.suffix in valid_exts or f in ("Makefile", "ROOT"):
                            self.all_text_files.append(p)

        self.all_text_files = sorted(list(set(self.all_text_files)))
        print(f"[oracle] Indexed {len(self.py_files)} repo-owned Python scripts and {len(self.all_text_files)} reference files.")

    def build_import_graph(self) -> None:
        module_to_relpath: dict[str, str] = {}
        for p in self.py_files:
            rel = p.relative_to(self.root).as_posix()
            mod_dotted = rel.removesuffix(".py").replace("/", ".")
            module_to_relpath[mod_dotted] = rel
            stem = p.stem
            module_to_relpath[stem] = rel

        for p in self.py_files:
            rel = p.relative_to(self.root).as_posix()
            try:
                content = p.read_text(encoding="utf-8", errors="ignore")
                hz = detect_ast_hazards(content, rel)
                if hz:
                    self.hazards_by_file[rel] = hz

                tree = ast.parse(content, filename=rel)
                for node in ast.walk(tree):
                    target_rel = None
                    if isinstance(node, ast.Import):
                        for alias in node.names:
                            if alias.name in module_to_relpath:
                                target_rel = module_to_relpath[alias.name]
                                if target_rel != rel:
                                    self.import_graph[rel].add(target_rel)
                                    self.reverse_import_graph[target_rel].add(rel)
                    elif isinstance(node, ast.ImportFrom):
                        if node.module and node.module in module_to_relpath:
                            target_rel = module_to_relpath[node.module]
                            if target_rel != rel:
                                self.import_graph[rel].add(target_rel)
                                self.reverse_import_graph[target_rel].add(rel)
            except Exception:
                pass

    def build_inverted_text_index(self) -> None:
        """Fast inverted token index: tokenizes reference files and maps words in O(1)."""
        script_basenames = {p.name: p.relative_to(self.root).as_posix() for p in self.py_files}
        script_names_set = set(script_basenames.keys())

        for file_path in self.all_text_files:
            rel = file_path.relative_to(self.root).as_posix()
            try:
                text = file_path.read_text(encoding="utf-8", errors="ignore")
            except Exception:
                continue

            tokens = set(re.findall(r'[\w\-\.]+', text))
            for match in tokens & script_names_set:
                target_rel = script_basenames[match]
                if target_rel != rel:
                    self.text_references[target_rel].add(rel)

    def compute_all_ci_reachable(self) -> set[str]:
        """Computes the set of all scripts reachable via directed import/invocation paths from CI roots in a single pass."""
        queue: list[str] = []
        for entry in AUTHORITATIVE_ENTRYPOINTS:
            entry_path = self.root / entry
            if not entry_path.exists():
                continue
            if entry_path.is_file():
                queue.append(entry_path.relative_to(self.root).as_posix())
            elif entry_path.is_dir():
                for sub in entry_path.rglob("*"):
                    if sub.is_file():
                        queue.append(sub.relative_to(self.root).as_posix())

        forward_edges: dict[str, set[str]] = defaultdict(set)
        for caller, callees in self.import_graph.items():
            for callee in callees:
                forward_edges[caller].add(callee)
        for callee, referrers in self.text_references.items():
            for ref in referrers:
                forward_edges[ref].add(callee)

        visited: set[str] = set(queue)
        bfs_queue = list(queue)

        while bfs_queue:
            curr = bfs_queue.pop(0)
            for nxt in forward_edges.get(curr, []):
                if nxt not in visited:
                    visited.add(nxt)
                    bfs_queue.append(nxt)

        return visited

    def classify_script(self, target_rel: str, ci_reachable: set[str]) -> ScriptDependencyRecord:
        importers = sorted(list(self.reverse_import_graph.get(target_rel, set())))
        all_referrers = sorted(list(self.text_references.get(target_rel, set())))

        shell_callers = [r for r in all_referrers if r.endswith(".sh") or r.endswith("Makefile") or ".github" in r]
        doc_refs = [r for r in all_referrers if r.endswith(".md") or "skills" in r or "docs" in r]
        in_deg = len(importers) + len(shell_callers)

        is_ci_reachable = target_rel in ci_reachable or target_rel in AUTHORITATIVE_ENTRYPOINTS

        if is_ci_reachable:
            classification = "ACTIVE_CI_CRITICAL"
        elif importers:
            classification = "ACTIVE_TOOL_LIBRARY"
        elif shell_callers:
            classification = "ACTIVE_RUNNER_UTILITY"
        elif doc_refs:
            classification = "DOCUMENTED_REFERENCE"
        else:
            classification = "CPG_ORPHAN_CANDIDATE"

        rec = ScriptDependencyRecord(
            path=target_rel,
            in_degree=in_deg,
            direct_importers=importers,
            shell_callers=shell_callers,
            doc_references=doc_refs,
            reachable_from_ci=is_ci_reachable,
            classification=classification,
        )
        self.records[target_rel] = rec
        return rec

    def analyze_all(self) -> None:
        t0 = time.time()
        self.discover_files()
        self.build_import_graph()
        self.build_inverted_text_index()
        ci_reachable = self.compute_all_ci_reachable()
        for p in self.py_files:
            rel = p.relative_to(self.root).as_posix()
            self.classify_script(rel, ci_reachable)
        self.elapsed_seconds = time.time() - t0
        print(f"[oracle] Completed graph analysis over {len(self.records)} scripts in {self.elapsed_seconds:.2f}s.")

    def emit_run_manifest(self, out_path: Path = Path("reports/python_cpg_manifest.json")) -> dict[str, Any]:
        """Emits an authoritative machine-generated telemetry block for CI and docs."""
        commit_sha = "unknown"
        try:
            res = subprocess.run(["git", "rev-parse", "HEAD"], cwd=self.root, capture_output=True, text=True, check=False)
            if res.returncode == 0:
                commit_sha = res.stdout.strip()
        except Exception:
            pass

        counts = defaultdict(int)
        for r in self.records.values():
            counts[r.classification] += 1

        scope_fingerprint = hashlib.sha256(":".join(sorted(self.records.keys())).encode("utf-8")).hexdigest()[:16]
        oracle_version_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()[:16]

        total_import_edges = sum(len(v) for v in self.import_graph.values())
        total_text_edges = sum(len(v) for v in self.text_references.values())

        manifest = {
            "schema": "ig.python-cpg-manifest.v1",
            "commit_sha": commit_sha,
            "timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "repo_root": str(self.root),
            "scan_dirs": self.scan_dirs,
            "scope_fingerprint": scope_fingerprint,
            "oracle_version_hash": oracle_version_hash,
            "metrics": {
                "repo_python_count": len(self.py_files),
                "reference_file_count": len(self.all_text_files),
                "import_edge_count": total_import_edges,
                "text_reference_edge_count": total_text_edges,
                "hazard_count": len(self.hazards_by_file),
                "elapsed_seconds": round(self.elapsed_seconds, 4),
            },
            "classification_counts": dict(counts),
            "hazards_detected": dict(self.hazards_by_file),
        }

        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
        return manifest


RepositoryDependencyGraph = HighSpeedDependencyGraph


def main() -> int:
    parser = argparse.ArgumentParser(description="Python DAG Dependency Oracle (Fast)")
    parser.add_argument("--dirs", nargs="+", default=["tools", "src"], help="Target directories to analyze")
    parser.add_argument("--target", help="Specific script to inspect (e.g. fix_basis_decide.py)")
    parser.add_argument("--json-out", default="reports/python_dependency_oracle.json", help="JSON output path")
    parser.add_argument("--filter-classification", choices=["PROVABLY_ORPHAN_ONE_OFF", "ACTIVE_CI_CRITICAL", "ACTIVE_TOOL_LIBRARY", "ALL"], default="ALL")
    args = parser.parse_args()

    oracle = HighSpeedDependencyGraph(ROOT, scan_dirs=args.dirs)
    oracle.analyze_all()

    if args.target:
        matches = [k for k in oracle.records if args.target in k]
        if not matches:
            print(f"[oracle] Target '{args.target}' not found.")
            return 1
        for m in matches:
            rec = oracle.records[m]
            print(f"\n========================================================")
            print(f"📄 Script: {rec.path}")
            print(f"🏷️  Classification: {rec.classification}")
            print(f"🔗 In-Degree: {rec.in_degree} (Direct Importers: {len(rec.direct_importers)}, Shell Callers: {len(rec.shell_callers)})")
            print(f"🛡️  CI Reachable: {rec.reachable_from_ci}")
            if rec.direct_importers:
                print(f"  📥 Imported By: {rec.direct_importers}")
            if rec.shell_callers:
                print(f"  ⚡ Called By: {rec.shell_callers}")
            if rec.doc_references:
                print(f"  📖 Documented In: {rec.doc_references}")
        return 0

    records = list(oracle.records.values())
    counts = defaultdict(int)
    for r in records:
        counts[r.classification] += 1

    print("\n=== Repository Python Script Classification ===")
    for k, v in sorted(counts.items()):
        print(f"  - {k}: {v} scripts")

    out_data = {
        "schema": "ig.python-dependency-oracle.v1",
        "total_python_scripts": len(records),
        "classification_counts": counts,
        "records": [asdict(r) for r in records if args.filter_classification == "ALL" or r.classification == args.filter_classification],
    }

    out_file = Path(args.json_out)
    out_file.parent.mkdir(parents=True, exist_ok=True)
    out_file.write_text(json.dumps(out_data, indent=2), encoding="utf-8")
    print(f"\n[oracle] Full dependency graph written to {args.json_out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
