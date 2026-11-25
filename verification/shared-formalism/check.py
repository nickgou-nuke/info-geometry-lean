#!/usr/bin/env python3
"""Verify the shared-formalism owners in one locked focused transaction.

Install this reconstructed runner as ``verification/shared-formalism/check.py``.
It reuses the existing focused package; it does not certify the root package,
change dependency pins, clean caches, or replace independent semantic review.
"""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
FOCUSED = ROOT / "verification/real-matrix-split"
OWNERS = (
    "InfoGeometry.Canonical.PhaseSpaceBFieldCompatibility",
    "InfoGeometry.Canonical.GeneralizedMetricPositivity",
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
sys.path.insert(0, str(ROOT))

from tools.build_lock import acquire_build_lock  # noqa: E402
from tools.infra.build import (  # noqa: E402
    _interrupt_child_and_wait,
    _validate_lake_workspace_integrity,
)
from tools.quality.reviewed_audit_source import (  # noqa: E402
    audit_source,
    parse_audit_output,
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def input_hashes() -> dict[str, str]:
    paths = [ROOT / "lean" / (m.replace(".", "/") + ".lean") for m in OWNERS]
    paths += [
        ROOT / "lean-toolchain",
        ROOT / "lake-manifest.json",
        ROOT / "lakefile.lean",
        FOCUSED / "lean-toolchain",
        FOCUSED / "lake-manifest.json",
        FOCUSED / "lakefile.toml",
        ROOT / "tools/build_lock.py",
        ROOT / "tools/infra/build.py",
        ROOT / "tools/quality/reviewed_audit_source.py",
        Path(__file__).resolve(),
    ]
    return {str(path.relative_to(ROOT)): sha256(path) for path in paths}


def git_packages(manifest: dict) -> dict[str, dict]:
    result = {}
    for package in manifest["packages"]:
        if package["type"] != "git":
            continue
        name = package["name"].strip("«»")
        require(name not in result, f"Duplicate Git package: {name}")
        require(bool(re.fullmatch(r"[0-9a-f]{40}", package["rev"])),
                f"Non-immutable dependency revision: {name}")
        result[name] = package
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=ROOT / "artifacts/verification/shared-formalism")
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    run_id = f"run-{time.time_ns()}-{os.getpid()}"
    logs = output / run_id
    logs.mkdir(exist_ok=False)
    receipt_path = output / "verification.json"
    report = {
        "status": "queued",
        "run_id": run_id,
        "started_at": datetime.now(timezone.utc).isoformat(),
        "scope": "Focused owner build, fresh source checks, and complete owned-declaration audit",
        "root_package_build_verified": False,
        "semantic_review_verified_by_this_runner": False,
        "root": str(ROOT),
        "focused_package": str(FOCUSED),
        "owners": list(OWNERS),
        "log_directory": str(logs),
        "commands": [],
    }

    def write_receipt() -> None:
        temporary = output / f"verification.{run_id}.tmp"
        temporary.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        temporary.replace(receipt_path)

    # Invalidate a previous receipt before waiting; no old success represents
    # this invocation. Source/pin snapshots are taken only after acquiring lock.
    write_receipt()
    lock = None
    child_env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        child_env.pop(key, None)

    def run(label: str, argv: list[str], *, cwd: Path = ROOT) -> str:
        require(lock is not None, "Commands require the shared build lock")
        log = logs / f"{len(report['commands']):02d}-{label}.log"
        row = {"label": label, "argv": argv, "cwd": str(cwd),
               "log": str(log), "exit_code": None, "status": "launching"}
        report["commands"].append(row)
        write_receipt()
        process = None
        started = time.monotonic()
        try:
            with log.open("w", encoding="utf-8") as stream:
                try:
                    process = subprocess.Popen(
                        argv, cwd=cwd, env=child_env, stdin=subprocess.DEVNULL,
                        stdout=stream, stderr=subprocess.STDOUT,
                        start_new_session=(os.name == "posix"),
                        pass_fds=(lock.fileno(),) if os.name == "posix" else (),
                    )
                    row.update(status="running", pid=process.pid)
                    write_receipt()
                    process.wait()
                finally:
                    # Keep both the log and the lock alive through cleanup.
                    if process is not None and process.poll() is None:
                        _interrupt_child_and_wait(process)
            row["status"] = "exited"
        except BaseException:
            row["status"] = "interrupted" if process is not None else "launch_failed"
            raise
        finally:
            row["exit_code"] = process.returncode if process is not None else None
            row["elapsed_seconds"] = round(time.monotonic() - started, 3)
            write_receipt()
        require(row["exit_code"] == 0,
                f"{label} exited {row['exit_code']}; inspect {log}")
        return log.read_text(encoding="utf-8", errors="replace")

    def stop_requested(signum: int, _frame: object) -> None:
        raise KeyboardInterrupt(f"received signal {signum}")

    previous_term_handler = signal.signal(signal.SIGTERM, stop_requested)
    try:
        print("[shared-formalism] waiting for the shared build lock", flush=True)
        lock = acquire_build_lock(None, f"shared-formalism:{os.getpid()}", block=True)
        report["status"] = "running"
        report["lock_acquired_at"] = datetime.now(timezone.utc).isoformat()
        write_receipt()
        print("[shared-formalism] acquired lock; validating focused owners", flush=True)
        for directory in (ROOT, FOCUSED):
            error = _validate_lake_workspace_integrity(directory)
            require(error is None, error or "Invalid workspace")

        processes = run("processes", ["ps", "-eo", "pid=,comm="])
        active = [line.strip() for line in processes.splitlines()
                  if len(line.split()) == 2 and line.split()[1] in {"lean", "lake"}]
        require(not active, f"Compiler processes active outside this lock: {active}")
        before = input_hashes()
        report["input_sha256_before"] = before
        report["source_sha256"] = {
            p: digest for p, digest in before.items() if p.startswith("lean/")
        }
        report["git_head"] = run("repository-head", ["git", "rev-parse", "HEAD"]).strip()
        root_toolchain = (ROOT / "lean-toolchain").read_text().strip()
        focused_toolchain = (FOCUSED / "lean-toolchain").read_text().strip()
        require(root_toolchain == focused_toolchain, "Root/focused toolchain mismatch")
        version_match = re.fullmatch(r"leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+)",
                                    root_toolchain)
        require(version_match is not None, "Expected an exact released Lean toolchain pin")
        pinned_version = version_match.group(1)
        child_env["ELAN_TOOLCHAIN"] = root_toolchain
        report["toolchain"] = root_toolchain
        root_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        focused_manifest = json.loads((FOCUSED / "lake-manifest.json").read_text())
        root_packages = git_packages(root_manifest)
        focused_packages = git_packages(focused_manifest)
        require(len(focused_packages) == len(focused_manifest["packages"]),
                "The focused verifier requires only pinned Git dependencies")
        require("mathlib" in root_packages and "mathlib" in focused_packages,
                "Missing Mathlib pin")
        dependencies = {}
        for name, package in focused_packages.items():
            require(name in root_packages and package["rev"] == root_packages[name]["rev"],
                    f"Root/focused dependency revision mismatch: {name}")
            relative = package.get("dir") or str(Path(focused_manifest["packagesDir"]) / name)
            package_root = (FOCUSED / relative).resolve()
            require(package_root.is_dir(), f"Provision the pinned dependency first: {package_root}")
            dependencies[name] = (package_root, package["rev"])

        def check_dependencies(prefix: str) -> dict[str, str]:
            actual = {}
            for name, (directory, revision) in dependencies.items():
                head = run(f"{prefix}-{name}-head", ["git", "rev-parse", "HEAD"],
                           cwd=directory).strip()
                require(head == revision, f"Actual dependency revision mismatch: {name}")
                run(f"{prefix}-{name}-tracked-clean", ["git", "diff", "--exit-code", "HEAD", "--"],
                    cwd=directory)
                actual[name] = head
            return actual

        report["dependency_heads_before"] = check_dependencies("before")
        report["mathlib_revision"] = focused_packages["mathlib"]["rev"]
        require((dependencies["mathlib"][0] / "lean-toolchain").read_text().strip()
                == root_toolchain, "Mathlib/toolchain pin mismatch")
        lake = ["lake", "-d", str(FOCUSED)]
        report["lake_version"] = run("lake-version", ["lake", "--version"]).strip()
        for label, argv in (
            ("lean-version", ["lean", "--version"]),
            ("focused-lean-version", lake + ["env", "lean", "--version"]),
        ):
            banner = run(label, argv).strip()
            require(bool(re.search(r"\bversion\s+" + re.escape(pinned_version) + r"(?=[,\s)])", banner)),
                    f"Actual compiler does not match {root_toolchain}: {banner}")
            report[label.replace("-", "_")] = banner

        for module in OWNERS:
            run("owner-build-" + module.rsplit(".", 1)[1], lake + ["build", module])
        for module in OWNERS:
            source = ROOT / "lean" / (module.replace(".", "/") + ".lean")
            run("fresh-" + module.rsplit(".", 1)[1],
                lake + ["env", "lean", "-DwarningAsError=true", str(source)])
        audit = logs / "SharedFormalismAudit.lean"
        audit.write_text(audit_source(OWNERS), encoding="utf-8")
        report["audit_source_sha256"] = sha256(audit)
        evidence = run("owned-declarations", lake + ["env", "lean", "-DwarningAsError=true", str(audit)])
        counts = parse_audit_output(evidence, OWNERS)
        declarations = re.findall(r"^AUDIT_DECL: (\S+): (.+)$", evidence, re.MULTILINE)
        require(len(declarations) == len(set(declarations)), "Duplicate audit declaration marker")
        require(dict(Counter(owner for owner, _ in declarations)) == counts,
                "Declaration rows do not reconcile with owner counts")
        axiom_markers = re.findall(r"^AUDIT_AXIOMS: (.+)$", evidence, re.MULTILINE)
        require(len(axiom_markers) == 1, "Missing or duplicate axiom-union marker")
        axioms = set(re.findall(r"[A-Za-z_][A-Za-z0-9_.]*", axiom_markers[0]))
        require(axioms <= ALLOWED_AXIOMS, f"Unexpected axiom-union output: {sorted(axioms)}")
        report["audit"] = {
            "module_counts": counts,
            "declaration_count": sum(counts.values()),
            "axioms": sorted(axioms),
            "allowed_axioms": sorted(ALLOWED_AXIOMS),
            "declarations": {m: [name for owner, name in declarations if owner == m] for m in OWNERS},
        }
        report["dependency_heads_after"] = check_dependencies("after")
        after = input_hashes()
        report["input_sha256_after"] = after
        require(before == after, "Source, runner, helper, or package configuration changed during verification")
        require(run("repository-head-after", ["git", "rev-parse", "HEAD"]).strip()
                == report["git_head"], "Repository HEAD changed during verification")
        report["status"] = "passed"
        print("[shared-formalism] focused build, fresh sources, and complete ownership audit passed", flush=True)
        return 0
    except BaseException as error:
        report["status"] = "failed"
        report["error"] = f"{type(error).__name__}: {error}"
        print(f"[shared-formalism] {report['error']}", file=sys.stderr, flush=True)
        return 130 if isinstance(error, KeyboardInterrupt) else 1
    finally:
        report["finished_at"] = datetime.now(timezone.utc).isoformat()
        try:
            write_receipt()
        finally:
            if lock is not None:
                lock.release()
            signal.signal(signal.SIGTERM, previous_term_handler)


if __name__ == "__main__":
    raise SystemExit(main())
