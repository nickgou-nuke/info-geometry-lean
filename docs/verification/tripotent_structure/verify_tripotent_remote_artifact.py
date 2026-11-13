#!/usr/bin/env python3
"""Read-only verification of exact-source remote Lean evidence; no compiler calls."""
from __future__ import annotations

import argparse
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def declarations(text: str) -> list[dict]:
    text = re.sub(r"^\ufeff?\d{4}-\d{2}-\d{2}T\S+Z ", "", text, flags=re.M)
    text = re.sub(r"\x1b\[[0-9;]*m", "", text)
    result = []
    matches = list(re.finditer(r"AUDIT_DECL: ([^\n:]+): ([^\n:]+): (#?\[[\s\S]*?\])", text))
    assert len(matches) == text.count("AUDIT_DECL: ")
    for match in matches:
        owner, name, raw = match.groups()
        raw = raw.strip()
        if raw.startswith("#"):
            raw = raw[1:]
        assert raw.startswith("[") and raw.endswith("]"), raw
        axioms = [x.strip() for x in raw[1:-1].split(",") if x.strip()]
        result.append({"owner": owner, "name": name, "axioms": axioms})
    return result


def main() -> None:
    if not __debug__:
        raise RuntimeError("Verification requires assertions enabled; optimized Python is rejected")
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--snapshot", type=Path, required=True)
    parser.add_argument("--artifact-root", type=Path, required=True)
    parser.add_argument("--job-log", type=Path, required=True)
    parser.add_argument("--repository", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    snapshot = json.loads(args.snapshot.read_text())
    state_path = args.artifact_root / "status.json"
    state = json.loads(state_path.read_text())
    targets = snapshot["targets"]
    assert state["status"] == "passed", state
    assert state["axiom_audit_passed"] is True
    assert state["targets"] == targets
    assert state["toolchain"] == snapshot["toolchain"]
    assert state["mathlib"] == snapshot["mathlib_pin"]
    assert state["source_sha256"] == snapshot["source_sha256"]
    assert [x["module"] for x in state["modules"]] == snapshot["ordered_closure"]
    assert all(x.get("returncode") == 0 for x in state["modules"])
    assert not state.get("failed_modules")
    for name, expected in snapshot["source_sha256"].items():
        path = args.artifact_root / "src" / (name.replace(".", "/") + ".lean")
        assert digest(path) == expected, name
    checker_paths = [
        "tools/quality/check_tripotent_structure.py",
        "tools/quality/check_perjes_klein.py",
        "tools/quality/check_peirce_reflection.py",
        "tools/quality/check_reviewed_prs.py",
    ]
    for path in checker_paths:
        assert digest(args.repository / path) == snapshot["tool_sha256"][path], path
    generator_path = args.repository / "tools/quality/check_peirce_reflection.py"
    generator_ast = ast.parse(generator_path.read_text())
    functions = [n for n in generator_ast.body
                 if isinstance(n, ast.FunctionDef) and n.name == "audit_source"]
    assert len(functions) == 1
    # Execute only this hash-bound self-contained generator function. Importing
    # the whole mutable checkout would execute unrelated transitive modules.
    namespace = {}
    exec(compile(ast.Module(body=functions, type_ignores=[]), str(generator_path), "exec"), namespace)
    expected_audit = namespace["audit_source"](targets).encode()
    audit_source_path = args.artifact_root / "src" / "PerjesKleinKernelAudit.lean"
    assert audit_source_path.read_bytes() == expected_audit
    audit_path = args.artifact_root / "audit.log"
    audit_text = audit_path.read_text()
    records = declarations(audit_text)
    counts = Counter(r["owner"] for r in records)
    assert set(counts) == set(targets)
    assert all(counts[x] > 0 for x in targets)
    assert len({(r["owner"], r["name"]) for r in records}) == len(records)
    assert len({r["name"] for r in records}) == len(records)
    markers = re.findall(r"AUDIT_COUNT: (\d+)", audit_text)
    assert markers == [str(len(records))], markers
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    observed = sorted({a for r in records for a in r["axioms"]})
    assert set(observed) <= allowed, observed
    assert "AUDIT_AXIOMS:" in audit_text
    raw_job_log = args.job_log.read_text()
    assert declarations(raw_job_log) == records
    checks = []
    for line in raw_job_log.splitlines():
        line = re.sub(r"^\ufeff?\d{4}-\d{2}-\d{2}T\S+Z ", "", line)
        match = re.fullmatch(r"CHECK (\S+) (\d+)", line.strip())
        if match:
            checks.append({"module": match.group(1), "returncode": int(match.group(2))})
    assert checks == state["modules"], checks
    log_hashes = {}
    for name in snapshot["ordered_closure"]:
        path = args.artifact_root / (name + ".log")
        log_hashes[name] = digest(path)
    version_path = args.artifact_root / "lean-version.txt"
    version_text = version_path.read_text().strip()
    pinned_version = snapshot["toolchain"].rsplit(":", 1)[1].removeprefix("v")
    assert version_text.startswith("Lean (version " + pinned_version + ", "), version_text
    assert (args.artifact_root / "src" / "lean-toolchain").read_text().strip() == snapshot["toolchain"]
    result = {
        "schema_version": 1,
        "verifier": "verify_tripotent_remote_artifact.py",
        "verifier_sha256": digest(Path(__file__)),
        "verdict": "remote_artifact_matches_exact_frozen_source_and_complete_owned_declaration_audit",
        "repository_source_modified": False,
        "local_lean_or_lake_invoked": False,
        "source_snapshot_sha256": digest(args.snapshot),
        "checked_revision": state["revision"],
        "required_source_tree": snapshot["local_tree"],
        "tree_correspondence": "Must also be established with immutable GitHub commit metadata; not inferred from this artifact.",
        "scope": state["scope"],
        "toolchain": state["toolchain"],
        "mathlib": state["mathlib"],
        "lean_version": version_text,
        "actual_lean_version_matches_toolchain_pin": True,
        "compiled_repository_modules": len(state["modules"]),
        "compiled_modules_in_job_log_match_status": True,
        "all_copied_source_hashes_match_snapshot": True,
        "native_audit_source_matches_reviewed_generator": True,
        "reviewed_checker_hashes_match_frozen_snapshot": True,
        "audit_generator_sha256": digest(generator_path),
        "optimized_python_rejected": True,
        "owned_declaration_count": len(records),
        "owned_declaration_counts": dict(sorted(counts.items())),
        "axiom_allowlist": sorted(allowed),
        "observed_axioms": observed,
        "status_sha256": digest(state_path),
        "audit_source_sha256": digest(audit_source_path),
        "audit_log_sha256": digest(audit_path),
        "lean_version_sha256": digest(version_path),
        "job_log_sha256": digest(args.job_log),
        "module_log_sha256": log_hashes,
        "owned_declarations": records,
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items()
                      if k not in {"owned_declarations", "module_log_sha256"}}, indent=2))
    print("EVIDENCE_SHA256", digest(args.output))


if __name__ == "__main__":
    main()
