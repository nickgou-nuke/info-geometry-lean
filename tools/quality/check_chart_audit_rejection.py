#!/usr/bin/env python3
"""One bounded namespace-rejection probe after a passing chart-closure build.

Example (pass the resolved Lean executable, not the elan launcher):
  python3 tools/quality/check_chart_audit_rejection.py --repo project \
    --work-dir verification --mathlib pinned-mathlib \
    --lean /path/to/toolchain/bin/lean

The positive directory must contain the maintained selected checker's PASS
result, snapshots, logs, and oleans. Nothing in that evidence is rewritten.
Evidence for this single invocation is placed in a new namespace-rejection/
subdirectory. An existing probe directory is refused, not cleaned or reused.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from typing import Any


VI = "InfoGeometry.Canonical.StreamVIDeclarationAudit"
VII = "InfoGeometry.Canonical.IdempotentChartDeclarationAudit"
NEGATIVE = "InfoGeometry.Canonical.IdempotentChartAuditNamespaceNegative"
OWNERS = [
    "InfoGeometry.OperatorAlgebra.ResolventChartDifferential",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentChartResolvent",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentChartDifferential",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.ChartSignCounterexample",
]
CERTIFICATES = [
    "declarationNames", "dependencyEdges", "dependencyEdges_forward",
    "declarationNames_size", "dependencyEdges_bounded", "declarationPartialOrder",
    "declarationPartialOrder_le_iff",
]
RECORD_KINDS = {"declaration", "graph_certificate", "summary"}
FORWARD_COMMAND = (
    "  elabLiteralCommand\n"
    '    "theorem dependencyEdges_forward : ∀ e ∈ dependencyEdges, e.1 < e.2 := by decide"'
)
VI_INVOCATION = "run_cmd auditOwners owners addedInverseDeclarations anchors"


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def digest(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def git(root: Path, *args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=root, stderr=subprocess.PIPE)


def relative_source(module: str) -> Path:
    parts = module.split(".")
    require(all(p and "/" not in p and "\\" not in p for p in parts), "Invalid module name")
    prefix = Path("lib/InfoGeometryCore") if module.startswith("InfoGeometryCore.") else Path("lean")
    return prefix.joinpath(*parts).with_suffix(".lean")


def records(text: str) -> list[dict[str, Any]]:
    result = []
    for line in text.splitlines():
        if line.lstrip().startswith("{"):
            try:
                value = json.loads(line)
            except json.JSONDecodeError:
                # Lean diagnostics can contain brace-prefixed pretty-printed terms.
                # Required record counts and exact comparisons below still fail
                # if an expected audit record is absent or malformed.
                continue
            if isinstance(value, dict) and value.get("record") in RECORD_KINDS:
                result.append(value)
    return result


def certificate_names(namespace: str) -> list[str]:
    return [VI + ".partialOrderOfRankedEdges", *[namespace + "." + n for n in CERTIFICATES]]


def positive_audit(log: Path, namespace: str) -> list[dict[str, Any]]:
    data = records(log.read_text(encoding="utf-8"))
    summaries = [r for r in data if r["record"] == "summary"]
    declarations = [r for r in data if r["record"] == "declaration"]
    certificates = [r for r in data if r["record"] == "graph_certificate"]
    require(len(summaries) == 1 and data[-1] == summaries[0], f"Missing unique final summary: {namespace}")
    summary = summaries[0]
    require(summary.get("status") == "PASS", f"Positive audit did not pass: {namespace}")
    require(summary["declarations"] == len(declarations), "Declaration count mismatch")
    require(summary["theorems"] == sum(r["kind"] == "theorem" for r in declarations), "Theorem count mismatch")
    require(set(summary["seeds"]) == {r["name"] for r in declarations if r["seed"]}, "Seed mismatch")
    require(summary["project_dependency_edges"] == len(summary["dependency_edges"]), "Edge count mismatch")
    expected = certificate_names(namespace)
    require([r["name"] for r in certificates] == expected, "Wrong certificate namespace or count")
    require(summary["graph_certificate_declarations"] == expected, "Certificate summary mismatch")
    require(all(r["axioms"] == [] for r in certificates), "Nonempty graph-certificate axiom list")
    if namespace == VII:
        require(summary["modules"] == OWNERS, "Chart owner set differs from this bounded probe")
        require(summary["added_seed_declarations"] == [] and summary["named_existing_anchors"] == [],
                "Unexpected additional chart seeds")
    return data


def fingerprint(repo: Path, work: Path, mathlib: Path, lean: Path) -> dict[str, Any]:
    manifest = read_json(work / "source-manifest.json")
    require(read_json(work / "result.json") == {"status": "PASS", **manifest}, "No matching positive PASS result")
    require(read_json(work / "checked-hashes.json") == manifest["sources"], "Incomplete checked-source map")
    require(manifest["compile_order"][-1] == VII, "Wrong positive build target")
    require(len(manifest["compile_order"]) == len(set(manifest["compile_order"])) == len(manifest["sources"]),
            "Invalid compile order")
    require(set(manifest["compile_order"]) == set(manifest["sources"]), "Compile-order/source mismatch")
    require((repo / "lean-toolchain").read_text().strip() == manifest["toolchain"], "Toolchain changed")
    pin = next(p["rev"] for p in read_json(repo / "lake-manifest.json")["packages"] if p["name"] == "mathlib")
    require(pin == manifest["mathlib"] == git(mathlib, "rev-parse", "HEAD").decode().strip(), "Mathlib pin mismatch")
    require(not git(mathlib, "status", "--porcelain", "--untracked-files=no").strip(), "Dirty Mathlib sources")
    packages = {}
    for package in read_json(mathlib / "lake-manifest.json")["packages"]:
        require(package["type"] == "git", "Unpinned native dependency")
        path = mathlib / ".lake/packages" / package["name"]
        revision = git(path, "rev-parse", "HEAD").decode().strip()
        require(revision == package["rev"], "Native dependency pin mismatch: " + package["name"])
        require(not git(path, "status", "--porcelain", "--untracked-files=no").strip(), "Dirty native dependency")
        packages[package["name"]] = revision
    require(packages == manifest["mathlib_package_pins"], "Native dependency set changed")
    source_hashes = {}
    for module, expected in manifest["sources"].items():
        relative = relative_source(module)
        snapshot = work / "lean" / Path(*module.split(".")).with_suffix(".lean")
        actual = {
            "live": digest(repo / relative), "snapshot": digest(snapshot),
            "index": hashlib.sha256(git(repo, "show", ":" + relative.as_posix())).hexdigest(),
        }
        require(all(value == expected for value in actual.values()), "Stale source: " + module)
        source_hashes[module] = actual
    tool_hashes = {}
    for name, expected in manifest["verification_tool_sha256"].items():
        path = Path(name).resolve()
        require(path.is_relative_to(repo), "Verification tool belongs to another checkout")
        tool_hashes[name] = digest(path)
        require(tool_hashes[name] == expected, "Verification tool changed: " + name)
    objects = {}
    require(not (work / "oleans").is_symlink(), "Symlinked positive project artifact root")
    for path in sorted((work / "oleans").rglob("*")):
        require(not path.is_symlink(), "Symlink in positive project artifacts")
        if path.is_file():
            objects[path.relative_to(work / "oleans").as_posix()] = digest(path)
    expected_objects = {Path(*m.split(".")).with_suffix(".olean").as_posix() for m in manifest["sources"]}
    observed_oleans = {name: value for name, value in objects.items() if name.endswith(".olean")}
    require(set(observed_oleans) == expected_objects, "Missing or extra positive project oleans")
    if (work / "object-manifest.json").exists():
        require(read_json(work / "object-manifest.json") == observed_oleans, "Positive object manifest mismatch")
    evidence = ["source-manifest.json", "result.json", "checked-hashes.json", "compiler-version.txt"]
    evidence += [module + ".log" for module in manifest["compile_order"]]
    evidence += [name for name in ["object-manifest.json", "ci-fingerprint.json", "selected-build.log"]
                 if (work / name).exists()]
    head = git(repo, "rev-parse", "HEAD").decode().strip()
    if (work / "ci-fingerprint.json").exists():
        ci = read_json(work / "ci-fingerprint.json")
        require(ci["source_commit"] == head == manifest["repository_head"], "CI source revision mismatch")
        require(ci["toolchain"] == manifest["toolchain"], "CI toolchain mismatch")
        require(ci["binaries"]["lean"]["sha256"] == digest(lean), "Lean differs from CI fingerprint")
    return {"source_sha256": source_hashes, "project_artifact_sha256": objects,
            "positive_evidence_sha256": {name: digest(work / name) for name in evidence},
            "verification_tool_sha256": tool_hashes, "lean_sha256": digest(lean),
            "git_head": head, "build_repository_head": manifest["repository_head"],
            "toolchain": manifest["toolchain"], "mathlib": pin, "package_pins": packages}


def make_probe(source: str) -> str:
    require(source.count(FORWARD_COMMAND) == 1, "Forward-certificate source shape changed")
    require(source.count(VI_INVOCATION) == 1, "Original VI invocation is not unique")
    replacement = (
        "  elabLiteralCommand\n"
        f"    (if certificateNamespace == `{NEGATIVE} then\n"
        '      "theorem dependencyEdges_forward : ∀ e ∈ dependencyEdges, e.1 < e.2 := (0 : Nat)"\n'
        "     else\n"
        '      "theorem dependencyEdges_forward : ∀ e ∈ dependencyEdges, e.1 < e.2 := by decide")'
    )
    imports = "".join("import " + owner + "\n" for owner in OWNERS)
    owner_literals = ",\n    ".join("`" + owner for owner in OWNERS)
    invoke = (
        f"\nnamespace {NEGATIVE}\n"
        "set_option maxRecDepth 100000 in\nset_option maxHeartbeats 2000000 in\n"
        f"run_cmd {VI}.auditOwners\n  #[{owner_literals}]\n  #[] #[]\n"
        f"end {NEGATIVE}\n"
    )
    return imports + source.replace(FORWARD_COMMAND, replacement, 1) + invoke


def reject_active_compilers() -> None:
    for proc in Path("/proc").iterdir():
        try:
            if proc.name.isdigit() and (proc / "comm").read_text().strip() in {"lean", "lake", "leanc"}:
                if (proc / "stat").read_text().split(") ", 1)[1].split()[0] != "Z":
                    raise RuntimeError("Compiler active after shared-lock acquisition: " + proc.name)
        except (FileNotFoundError, PermissionError, ProcessLookupError):
            pass


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True, help="Passing selected-closure verification directory")
    parser.add_argument("--mathlib", type=Path, required=True)
    parser.add_argument("--lean", type=Path, required=True, help="Resolved pinned Lean executable (not elan)")
    parser.add_argument("--timeout-seconds", type=int, default=900)
    args = parser.parse_args()
    repo, work, mathlib, lean = (p.resolve(strict=True) for p in
                               (args.repo, args.work_dir, args.mathlib, args.lean))
    require(args.timeout_seconds > 0, "Timeout must be positive")
    output = work / "namespace-rejection"
    output.mkdir(exist_ok=False)
    report: dict[str, Any] = {
        "schema": "idempotent_chart.namespace_rejection.v1", "status": "RUNNING",
        "started_utc": now(), "repo": str(repo), "positive_work_dir": str(work),
        "mathlib": str(mathlib), "lean": str(lean), "runner_sha256": digest(Path(__file__)),
        "target_certificate": NEGATIVE + ".dependencyEdges_forward",
        "probe_invocations": 0, "timeout_seconds": args.timeout_seconds,
        "scope": "Single negative caller-namespace case; not a root-package build or extra mathematical theorem",
    }
    lock = None
    exit_code = 2
    try:
        # Use the maintained lock implementation, after checking its positive-build hash.
        manifest = read_json(work / "source-manifest.json")
        lock_source = repo / "tools/build_lock.py"
        require(manifest["verification_tool_sha256"].get(str(lock_source)) == digest(lock_source),
                "Unverified shared-lock implementation")
        spec = importlib.util.spec_from_file_location("chart_probe_build_lock", lock_source)
        require(spec is not None and spec.loader is not None, "Cannot load maintained shared lock")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        (output / "result.json").write_text(json.dumps(report, indent=2) + "\n")
        print("Waiting for the shared repository build lock", flush=True)
        lock = module.acquire_build_lock(None, f"chart-audit-rejection:{os.getpid()}", block=True)
        report["lock_acquired_utc"] = now()
        reject_active_compilers()
        report["positive_before"] = fingerprint(repo, work, mathlib, lean)
        vi = positive_audit(work / (VI + ".log"), VI)
        vii = positive_audit(work / (VII + ".log"), VII)
        shared_source = work / "lean" / Path(*VI.split(".")).with_suffix(".lean")
        source = make_probe(shared_source.read_text(encoding="utf-8"))
        scratch_root = output / "lean"
        scratch = scratch_root / Path(*NEGATIVE.split(".")).with_suffix(".lean")
        scratch.parent.mkdir(parents=True)
        scratch.write_text(source, encoding="utf-8")
        report["probe_source"] = str(scratch)
        report["probe_source_sha256"] = digest(scratch)
        report["shared_source_sha256"] = digest(shared_source)
        libraries = [work / "oleans", mathlib / ".lake/build/lib/lean"]
        libraries += [mathlib / ".lake/packages" / name / ".lake/build/lib/lean"
                      for name in sorted(manifest["mathlib_package_pins"])]
        require(all(path.is_dir() for path in libraries), "Missing compiled native dependency directory")
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, libraries)))
        command = [str(lean), "--root=" + str(scratch_root), str(scratch)]
        report["command"] = command
        report["cwd"] = str(repo)
        report["compiler_environment"] = {key: env[key] for key in
            ["LEAN_PATH", "LEAN_SYSROOT", "LD_PRELOAD", "LD_LIBRARY_PATH"] if key in env}
        log = output / "negative-certificate.log"
        report["probe_invocations"] = 1
        report["compiler_started_utc"] = now()
        timed_out = False
        with log.open("wb") as handle:
            try:
                result = subprocess.run(command, cwd=repo, env=env, stdout=handle, stderr=subprocess.STDOUT,
                                        timeout=args.timeout_seconds, pass_fds=(lock.fileno(),))
                report["compiler_exit_code"] = result.returncode
            except subprocess.TimeoutExpired:
                timed_out = True
                report["compiler_exit_code"] = None
        report["compiler_finished_utc"] = now()
        report["timed_out"] = timed_out
        report["stdout_log"] = str(log)
        report["stdout_sha256"] = digest(log)
        report["positive_after"] = fingerprint(repo, work, mathlib, lean)
        unchanged = report["positive_before"] == report["positive_after"]
        text = log.read_text(encoding="utf-8", errors="replace")
        observed = records(text)
        preserved = observed[:len(vi)] == vi
        rest = observed[len(vi):]
        new_declarations = [r for r in rest if r["record"] == "declaration"]
        expected_declarations = [r for r in vii if r["record"] == "declaration"]
        new_certificates = [r for r in rest if r["record"] == "graph_certificate"]
        target = report["target_certificate"]
        named_rejection = ("Rejected axiom sorryAx in declaration " + target) in text
        type_error = bool(re.search(r"type mismatch", text, re.IGNORECASE)) and bool(re.search(r"\bNat\b", text))
        criteria = {
            "one_invocation": report["probe_invocations"] == 1,
            "not_timed_out": not timed_out,
            "compiler_rejected": isinstance(report["compiler_exit_code"], int) and report["compiler_exit_code"] > 0,
            "valid_VI_records_preserved": preserved,
            "new_owner_declaration_records_match_positive": new_declarations == expected_declarations,
            "no_new_summary": not any(r["record"] == "summary" for r in rest),
            "only_new_namespace_certificates_after_VI": all(r["name"] in certificate_names(NEGATIVE) for r in new_certificates),
            "ill_typed_certificate_rejected": type_error and
                not any(r["name"] == target for r in new_certificates),
            "positive_sources_index_snapshots_objects_tools_unchanged": unchanged,
            "probe_source_unchanged": digest(scratch) == report["probe_source_sha256"],
            "runner_unchanged": digest(Path(__file__)) == report["runner_sha256"],
        }
        report["criteria"] = criteria
        report["observed_rejection_route"] = (
            "checked forbidden-axiom guard names the invalid new-namespace certificate" if named_rejection else
            "ill-typed Nat certificate; no specific immediate diagnostic route required"
        )
        report["new_certificate_records_before_rejection"] = new_certificates
        report["status"] = "PASS" if all(criteria.values()) else "FAIL"
        exit_code = 0 if report["status"] == "PASS" else 1
    except Exception as error:
        report["status"] = "FAIL" if report["probe_invocations"] else "BLOCKED"
        report["error"] = f"{type(error).__name__}: {error}"
        exit_code = 1 if report["probe_invocations"] else 2
    finally:
        if lock is not None:
            lock.release()
        report["finished_utc"] = now()
        destination = output / "result.json"
        destination.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        (output / "result.sha256").write_text(digest(destination) + "  result.json\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "result": str(output / "result.json"),
                      "compiler_exit_code": report.get("compiler_exit_code"),
                      "criteria": report.get("criteria"), "error": report.get("error")}), flush=True)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
