#!/usr/bin/env python3
"""Run the focused checks under check.py's shared lock and retain exact evidence.

This driver records executed checks. Independent QA must separately inspect
and rerun the frozen workflow before treating its output as acceptance.
"""

from __future__ import annotations

from collections import Counter
from datetime import datetime, timezone
import fcntl
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import tomllib

PROJECT = Path(__file__).resolve().parent
ROOT = PROJECT.parents[1]
LOGS = PROJECT / "logs"
BASE = "c143c264bc18bbf41d692be4e270b5b7f7405702"
MATH = [
    "InfoGeometry/OperatorAlgebra/OrderedHomotope",
    "InfoGeometry/Algebra/TwoModeCountRecurrence",
    "InfoGeometry/Twistor/ConstituentWittGram",
    "InfoGeometry/Twistor/ConstituentCayleyGram",
    "InfoGeometry/Twistor/ConstituentInvariantIndependence",
    "InfoGeometry/Twistor/MomentHomotopeWitness",
]
OWNERS = {p.replace("/", ".") for p in MATH}
EXPECTED_NAMED_COUNTS = dict(zip(
    [p.replace("/", ".") for p in MATH], [15, 14, 22, 16, 2, 1], strict=True))
PATHS = ["lean/" + p + ".lean" for p in MATH]
AUDIT = "lean/InfoGeometry/Twistor/TwistorHomotopeAudit.lean"
PROTECTED = PATHS + [AUDIT] + [
    "verification/twistor-homotope/" + p for p in
    [".gitignore", "check.py", "verify.py", "lakefile.toml", "lake-manifest.json",
     "lean-toolchain", "README.md", "VACUITY_REVIEW.json"]
] + [
    ".github/workflows/twistor-homotope.yml",
    "docs/TWISTOR_HOMOTOPE_INVARIANTS_CONTRACT.md",
    "docs/intake/TWISTOR_HOMOTOPE_STREAM_2026_11_11.txt",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
CONTROLS = [
    "AGENTS.md", ".githooks/pre-commit", ".githooks/pre-push",
    "lean-toolchain", "lake-manifest.json", "lakefile.lean", "lakefile.toml",
    "pyproject.toml", "tools/build_lock.py", "tools/infra/build.py",
    "tools/infra/opengauss_screener.py", "tools/infra/opengauss_cli.py",
    "tools/infra/opengauss_ground_truth_contract.py",
    "tools/quality/proof_proxy_staged_gate.py", "scripts/vacuity-linter.py",
]


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def git(*args: str, cwd: Path = ROOT) -> str:
    return subprocess.check_output(["git", *args], cwd=cwd, text=True).strip()


def fingerprints() -> dict:
    return {p: digest((ROOT / p).read_bytes()) for p in PROTECTED}


def committed_bytes(revision: str, path: str) -> bytes:
    return subprocess.check_output(["git", "show", revision + ":" + path], cwd=ROOT)


def verify_committed_sources() -> None:
    for path in PROTECTED:
        require((ROOT / path).read_bytes() == committed_bytes("HEAD", path),
                "Protected file differs from committed source: " + path)


def control_fingerprints() -> dict:
    hashes = {}
    for path in CONTROLS:
        current = (ROOT / path).read_bytes()
        require(current == committed_bytes("HEAD", path) == committed_bytes(BASE, path),
                "Root control differs from implementation base: " + path)
        hashes[path] = digest(current)
    return hashes


def mask_lean_comments_and_strings(source: str) -> str:
    """Preserve lines while removing nested comments and string literal bodies."""
    output, index, depth, in_string = [], 0, 0, False
    while index < len(source):
        char, pair = source[index], source[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                output.append("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                output.append("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif in_string:
            if char == "\\" and index + 1 < len(source):
                output.extend("\n" if c == "\n" else " " for c in source[index:index + 2])
                index += 2
            else:
                in_string = char != '"'
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif pair == "/-":
            depth = 1
            output.append("  ")
            index += 2
        elif pair == "--":
            end = source.find("\n", index)
            end = len(source) if end == -1 else end
            output.append(" " * (end - index))
            index = end
        elif char == '"':
            in_string = True
            output.append(" ")
            index += 1
        else:
            output.append(char)
            index += 1
    require(depth == 0 and not in_string, "Unterminated Lean comment or string")
    return "".join(output)


def main() -> None:
    LOGS.mkdir(exist_ok=True)
    os.environ["GIT_OPTIONAL_LOCKS"] = "0"
    os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
    lock_path = Path("/tmp/info-geometry-build.lock")
    lock = json.loads(lock_path.read_text())
    require(str(lock.get("owner", "")).startswith("twistor-homotope:"),
            "Run through check.py env python3 verify.py")
    with lock_path.open() as handle:
        try:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            pass
        else:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
            raise RuntimeError("The outer shared build lock is not held")

    before = fingerprints()
    head = git("rev-parse", "HEAD")
    require(not git("diff", "--name-only", "HEAD", "--"), "Tracked worktree differs from HEAD")
    verify_committed_sources()
    controls_before = control_fingerprints()
    report = {
        "schema": "twistor-homotope-executed-checks-v1",
        "disposition": "RUNNING", "independent_qa_acceptance": False,
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "git_head": head, "git_tree": git("rev-parse", "HEAD^{tree}"),
        "implementation_base": BASE, "source_sha256": before,
        "python_version": sys.version,
        "unchanged_root_control_sha256": controls_before,
        "workflow_run_id": os.environ.get("GITHUB_RUN_ID"),
        "workflow_run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
        "shared_lock": lock, "commands": [],
        "scope_exclusions": ["root integration and unrelated workflows",
                             "physical or group classification",
                             "Clifford-space dimension identification"],
    }

    def checkpoint() -> None:
        (LOGS / "checks.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(label: str, argv: list[str]) -> str:
        print("CHECK_START", label, flush=True)
        start = time.monotonic()
        completed = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
        stdout, stderr = completed.stdout, completed.stderr
        out_path, err_path = LOGS / (label + ".stdout.log"), LOGS / (label + ".stderr.log")
        out_path.write_text(stdout)
        err_path.write_text(stderr)
        report["commands"].append({
            "label": label, "argv": argv, "exit_code": completed.returncode,
            "duration_seconds": round(time.monotonic() - start, 3),
            "stdout_sha256": digest(out_path.read_bytes()),
            "stderr_sha256": digest(err_path.read_bytes()),
        })
        checkpoint()
        if completed.returncode:
            print(stdout[-30000:] + stderr[-30000:], flush=True)
        print("CHECK_END", label, completed.returncode, flush=True)
        require(completed.returncode == 0, label + " failed")
        return stdout

    try:
        root_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        root_pins = {p["name"]: p["rev"] for p in root_manifest["packages"] if p["type"] == "git"}
        focused = json.loads((PROJECT / "lake-manifest.json").read_text())
        dependencies = []
        for package in focused["packages"]:
            name, revision = package["name"], package["rev"]
            path = PROJECT / focused["packagesDir"] / name
            require(root_pins[name] == revision == git("rev-parse", "HEAD", cwd=path),
                    "Dependency revision mismatch: " + name)
            require(not git("status", "--porcelain=v1", "--untracked-files=no", cwd=path),
                    "Tracked dependency changes: " + name)
            dependencies.append({"name": name, "revision": revision,
                                 "status_before": git("status", "--porcelain=v1", "--untracked-files=all", cwd=path)})
        report["dependencies"] = dependencies
        require((PROJECT / "lean-toolchain").read_bytes() == (ROOT / "lean-toolchain").read_bytes(),
                "Toolchain differs from root")
        python_requirements = tomllib.loads((ROOT / "pyproject.toml").read_text())["project"]["dependencies"]
        require("jsonschema==4.23.0" in python_requirements, "Source-gate pin differs from root")
        jsonschema_version = importlib.metadata.version("jsonschema")
        require(jsonschema_version == "4.23.0", "Unexpected jsonschema version")
        report["python_dependencies"] = {"jsonschema": jsonschema_version}
        report["lean_version"] = run("lean-version", ["lean", "--version"]).strip()
        report["lake_version"] = run("lake-version", ["lake", "--version"]).strip()
        run("build", ["lake", "-d", str(PROJECT), "build"])
        audit = run("fresh-audit", ["lake", "-d", str(PROJECT), "env", "lean", str(ROOT / AUDIT)])
        finals = re.findall(r"TWISTOR_HOMOTOPE_AUDIT_PASS: (\d+) declarations, (\d+) theorem declarations", audit)
        require(len(finals) == 1, "Fresh audit must emit exactly one success marker")
        declarations = []
        for owner, name, raw in re.findall(r"TWISTOR_HOMOTOPE_DECL: (\S+): ([^:\n]+): (#?\[[^\]]*\])", audit):
            axioms = [a.strip().lstrip("`") for a in raw.lstrip("#")[1:-1].split(",") if a.strip()]
            require(set(axioms) <= ALLOWED, "Unexpected axiom dependency")
            declarations.append({"owner": owner, "name": name.strip(), "axioms": axioms})
        count, theorem_count = map(int, finals[0])
        require(count == len(declarations) == len({d["name"] for d in declarations}),
                "Incomplete declaration enumeration")
        owner_counts = dict(Counter(d["owner"] for d in declarations))
        markers = {o: int(n) for o, n in re.findall(r"TWISTOR_HOMOTOPE_OWNER: (\S+): (\d+)", audit)}
        require(set(owner_counts) == OWNERS and markers == owner_counts, "Owner inventory mismatch")
        membership = []
        for path, owner in zip(PATHS, [p.replace("/", ".") for p in MATH]):
            source = mask_lean_comments_and_strings((ROOT / path).read_text())
            named = re.findall(r"(?m)^\s*(?:@\[[^\n]*\]\s*)?(private\s+)?(?:theorem|lemma)\s+([^\s(:]+)", source)
            require(len(named) == EXPECTED_NAMED_COUNTS[owner], "Reviewed source inventory changed: " + owner)
            for private, name in named:
                expected = owner + "." + name
                matches = [d for d in declarations if d["owner"] == owner and
                           (d["name"] == expected or (private and d["name"].endswith("." + expected)))]
                require(len(matches) == 1, "Source theorem missing from audit: " + expected)
                membership.append(matches[0])
        report["audit"] = {
            "declaration_count": count, "theorem_declaration_count": theorem_count,
            "named_source_theorem_count": len(membership), "source_theorem_membership": membership,
            "reviewed_named_theorem_counts": EXPECTED_NAMED_COUNTS,
            "owner_counts": owner_counts, "declarations": declarations,
            "axiom_usage_counts": dict(Counter(a for d in declarations for a in d["axioms"])),
        }
        screen = json.loads(run("strict-screen", ["python3", "tools/infra/opengauss_screener.py", "--strict", "--json", *PATHS]))
        require(not screen["violations"], "Strict screen has findings")
        refute = json.loads(run("strict-refute", ["python3", "tools/infra/opengauss_cli.py", "refute", *PATHS, "--strict", "--json"]))
        require(len(refute) == len(PATHS) and all(r["verdict"] == "PASS" and r["clean"] for r in refute),
                "Strict refute has findings")
        gate = json.loads(run("gate4-static", ["python3", "tools/infra/opengauss_cli.py", "review", *PATHS, AUDIT, "--gate", "GATE_4", "--json"]))
        require(len(gate) == len(PATHS) + 1 and all(not r["trap_violations"] and not r["scope_inflation_warnings"] and not r["kernel_checked"] for r in gate),
                "Static Gate4 has findings or mislabels kernel execution")
        vacuity_review = json.loads((PROJECT / "VACUITY_REVIEW.json").read_text())
        require(digest((ROOT / "scripts/vacuity-linter.py").read_bytes()) ==
                vacuity_review["linter_sha256"], "Reviewed vacuity linter changed")
        require(set(vacuity_review["cases"]) <= set(PATHS), "Unknown vacuity review owner")
        require(all(f["name"] == "no_hyp_use" and f["severity"] == 0.3
                    for case in vacuity_review["cases"].values()
                    for f in case["expected_findings"]),
                "Only the reviewed textual parameter-occurrence heuristic is eligible")
        report["vacuity"] = []
        unreviewed = []
        for path in PATHS + [AUDIT]:
            result = json.loads(run("vacuity-" + Path(path).stem,
                                    ["python3", "scripts/vacuity-linter.py", path, "--json"]))
            entry = {"path": path, "raw_result": result, "classification": "NO_FINDINGS"}
            if result["findings"]:
                review = vacuity_review["cases"].get(path)
                if review and before[path] == review["source_sha256"] and \
                        result["findings"] == review["expected_findings"]:
                    entry["classification"] = "SOURCE_REVIEWED_FALSE_POSITIVE"
                    entry["review"] = review
                else:
                    entry["classification"] = "UNREVIEWED"
                    unreviewed.append(path)
            report["vacuity"].append(entry)
        checkpoint()
        run("whitespace", ["git", "diff", "--check", BASE, "HEAD", "--", *PROTECTED])
        artifacts = {}
        for stem in MATH + ["InfoGeometry/Twistor/TwistorHomotopeAudit"]:
            for suffix in [".olean", ".ilean"]:
                path = PROJECT / ".lake/build/lib/lean" / (stem + suffix)
                artifacts[str(path.relative_to(ROOT))] = digest(path.read_bytes())
        report["compiled_artifact_sha256"] = artifacts
        require(before == fingerprints() and head == git("rev-parse", "HEAD"),
                "Source or HEAD changed during verification")
        require(not git("diff", "--name-only", "HEAD", "--"), "Tracked worktree changed during verification")
        verify_committed_sources()
        require(controls_before == control_fingerprints(), "Root controls changed during verification")
        for dependency in dependencies:
            path = PROJECT / focused["packagesDir"] / dependency["name"]
            require(git("rev-parse", "HEAD", cwd=path) == dependency["revision"] and
                    not git("status", "--porcelain=v1", "--untracked-files=no", cwd=path),
                    "Dependency changed during verification: " + dependency["name"])
            dependency["status_after"] = git("status", "--porcelain=v1", "--untracked-files=all", cwd=path)
            require(dependency["status_before"] == dependency["status_after"],
                    "Dependency worktree status changed: " + dependency["name"])
        report["dependency_invariance"] = True
        report["source_invariance"] = True
        require(not unreviewed, "Vacuity heuristic needs manual classification: " + ", ".join(unreviewed))
        report["disposition"] = "CHECKS_PASSED"
        print("TWISTOR_HOMOTOPE_CHECKS_PASSED", count, theorem_count, len(membership), flush=True)
    except Exception as error:
        report["disposition"] = "CHECKS_FAILED"
        report["failure"] = str(error)
        raise
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        checkpoint()


if __name__ == "__main__":
    main()
