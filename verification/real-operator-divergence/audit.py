#!/usr/bin/env python3
"""Build and audit seven selected owners with the existing same-pin harness.

Run this driver directly, never through check.py: every child check.py call
already acquires the repository's shared build lock. No manifests, package
configuration, source owners, or root gates are modified by this driver.
The generated native audit is a fresh runtime file in the output directory.

Recovery note: the pin and audit-output parsers were reconstructed from the
original contract and the maintained helpers at base fea96b564201654cd4693008585039a56f66adf3.
This file is not claimed to be a byte-for-byte recovery of the earlier runner.
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
import tomllib
from typing import Callable


TARGETS = (
    "InfoGeometry.Architecture.MatrixSymmetricConeFisherRao",
    "InfoGeometry.Jordan.SPD",
    "InfoGeometry.Jordan.BurgStein",
    "InfoGeometry.Geometry.DualFlatKreinLegendreGraph",
    "InfoGeometry.OperatorAlgebra.RealMatrixSplit",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicGaloisNilpotentSylvesterSynthesis",
    "InfoGeometry.Algebra.CyclotomicRealCounterexamples",
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FOCUSED = Path("verification/real-matrix-split")
INFRASTRUCTURE = (
    "lean-toolchain", "lake-manifest.json", "lakefile.lean",
    "tools/build_lock.py", "tools/infra/build.py",
    "tools/quality/reviewed_audit_source.py",
    *(str(FOCUSED / name) for name in
      ("check.py", "lean-toolchain", "lake-manifest.json", "lakefile.toml")),
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", *args], cwd=repo, text=True, stderr=subprocess.PIPE
    ).strip()


def snapshot(repo: Path) -> dict[str, str]:
    paths = ["lean/" + target.replace(".", "/") + ".lean" for target in TARGETS]
    paths.extend(INFRASTRUCTURE)
    return {relative: sha256(repo / relative) for relative in paths}


def check_pins(repo: Path) -> dict:
    project = repo / FOCUSED
    toolchain = (repo / "lean-toolchain").read_bytes()
    require((project / "lean-toolchain").read_bytes() == toolchain,
            "Focused and root Lean toolchains differ")
    root_manifest = json.loads((repo / "lake-manifest.json").read_text())
    manifest = json.loads((project / "lake-manifest.json").read_text())
    config = tomllib.loads((project / "lakefile.toml").read_text())
    require(manifest["name"] == config["name"], "Focused package names differ")
    root_entries = [p for p in root_manifest["packages"] if p["type"] == "git"]
    root_git = {p["name"]: p for p in root_entries}
    require(len(root_git) == len(root_entries), "Duplicate root Git dependency")
    focused = manifest["packages"]
    require(all(p["type"] == "git" for p in focused),
            "Focused dependencies must all be pinned Git packages")
    names = [p["name"] for p in focused]
    require(len(names) == len(set(names)), "Duplicate focused dependency")
    require("mathlib" in names and "mathlib" in root_git, "Missing pinned Mathlib")

    def pin(package: dict) -> tuple:
        return package.get("url"), package.get("rev"), package.get("subDir")

    requirements = config.get("require", [])
    require(len(requirements) == 1 and requirements[0].get("name") == "mathlib",
            "Focused package must require exactly the root-pinned Mathlib")
    requirement = requirements[0]
    require((requirement.get("git"), requirement.get("rev"), requirement.get("subDir"))
            == pin(root_git["mathlib"]), "Focused lakefile Mathlib pin differs")
    packages = (repo / ".lake/packages").resolve()
    require((project / config["packagesDir"]).resolve() == packages and
            (project / manifest["packagesDir"]).resolve() == packages,
            "Focused package cache differs from the maintained shared cache")
    require((project / config["srcDir"]).resolve() == (repo / "lean").resolve(),
            "Focused package must build canonical lean/ sources")
    require((packages / "mathlib/lean-toolchain").read_bytes() == toolchain,
            "Pinned Mathlib and root Lean toolchains differ")

    mathlib_manifest = json.loads((packages / "mathlib/lake-manifest.json").read_text())
    transitive = mathlib_manifest["packages"]
    require(all(p["type"] == "git" for p in transitive),
            "Pinned Mathlib dependencies must be Git packages")
    inherited = {p["name"]: p for p in transitive}
    require(len(inherited) == len(transitive) and "mathlib" not in inherited,
            "Malformed Mathlib dependency inventory")
    require(set(names) == set(inherited) | {"mathlib"},
            "Focused dependency inventory differs from pinned Mathlib's closure")
    records = {}
    for package in focused:
        name = package["name"]
        require(name in root_git and pin(package) == pin(root_git[name]),
                f"Focused dependency differs from root pin: {name}")
        if name != "mathlib":
            require(pin(package) == pin(inherited[name]),
                    f"Focused dependency differs from pinned Mathlib: {name}")
        checkout = packages / name
        require(Path(git(checkout, "rev-parse", "--show-toplevel")).resolve()
                == checkout.resolve(), f"Dependency is not its own Git checkout: {name}")
        head = git(checkout, "rev-parse", "HEAD")
        require(head == package["rev"], f"Dependency checkout differs from pin: {name}")
        require(not git(checkout, "status", "--porcelain=v1", "--untracked-files=no"),
                f"Tracked dependency sources are modified: {name}")
        records[name] = {"url": package["url"], "rev": head,
                         "subDir": package.get("subDir")}
    return {"toolchain": toolchain.decode("utf-8").strip(),
            "packages": {name: records[name] for name in sorted(records)}}


def parse_native_audit(raw: str, targets: tuple[str, ...],
                       parse_counts: Callable) -> dict:
    counts = parse_counts(raw, targets)
    declarations = []
    for line in raw.splitlines():
        if not line.startswith("AUDIT_DECL:"):
            continue
        match = re.fullmatch(r"AUDIT_DECL: (\S+): (.+)", line)
        require(match is not None, f"Malformed native declaration marker: {line}")
        owner, name = match.groups()
        require(owner in counts and bool(name.strip()), "Unexpected declaration owner or name")
        declarations.append({"owner": owner, "name": name})
    require(Counter(row["owner"] for row in declarations) == Counter(counts),
            "Native declaration rows do not reconcile with module counts")
    require(len({row["name"] for row in declarations}) == len(declarations),
            "Duplicate native declaration name")
    axiom_lines = [line for line in raw.splitlines() if line.startswith("AUDIT_AXIOMS:")]
    require(len(axiom_lines) == 1, "Missing or duplicate native axiom marker")
    axiom_match = re.fullmatch(r"AUDIT_AXIOMS: #?\[(.*)\]", axiom_lines[0])
    require(axiom_match is not None, "Malformed native axiom marker")
    group = axiom_match.group(1).strip()
    axioms = [name.strip() for name in group.split(",")] if group else []
    require(len(axioms) == len(set(axioms)) and set(axioms) <= ALLOWED_AXIOMS,
            "Duplicate or disallowed transitive axiom in native audit")
    return {"module_counts": counts, "declaration_count": len(declarations),
            "axioms": sorted(axioms),
            "declarations": sorted(declarations, key=lambda row: (row["owner"], row["name"]))}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd(), help="Repository checkout root")
    parser.add_argument("--output", type=Path, required=True,
                        help="New output directory; existing directories are not overwritten")
    parser.add_argument("--runtime-bin", type=Path,
                        help="Optional pinned Lean/Lake bin directory to prepend to PATH")
    parser.add_argument("--prepare-only", action="store_true",
                        help="Check sources/pins and generate audit; run no Lean/Lake commands")
    args = parser.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    if output.exists():
        parser.error("--output must name a new directory to prevent stale-log reuse")
    output.mkdir(parents=True)
    env = os.environ.copy()
    if args.runtime_bin:
        env["PATH"] = str(args.runtime_bin.resolve()) + os.pathsep + env.get("PATH", "")
    sys.path.insert(0, str(repo))
    report = {
        "schema": "operator-information-selected-owner-audit-v1", "status": "RUNNING",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "targets": list(TARGETS), "commands": [],
        "scope": "Seven selected owners: focused builds and native all-owned-declaration audit; "
                 "transitive axiom dependencies checked for every inventoried declaration",
        "exclusions": ["whole-repository build", "semantic acceptance", "publication approval"],
    }

    def run(label: str, arguments: list[str]) -> str:
        command = [sys.executable, str(repo / FOCUSED / "check.py"), *arguments]
        log = output / (label + ".log")
        record = {"label": label, "argv": command, "log": str(log)}
        report["commands"].append(record)
        print("CHECK_START", label, flush=True)
        started = time.monotonic()
        try:
            with log.open("wb") as stream:
                process = subprocess.Popen(command, cwd=repo, env=env, stdout=stream,
                                           stderr=subprocess.STDOUT, start_new_session=True)
                try:
                    record["exit_code"] = process.wait()
                except KeyboardInterrupt:
                    # Ask the maintained wrapper to stop its own child and release its lock.
                    process.send_signal(signal.SIGINT)
                    record["exit_code"] = process.wait()
                    raise
        finally:
            record["duration_seconds"] = round(time.monotonic() - started, 3)
            if log.exists():
                record["log_sha256"] = sha256(log)
        require(record["exit_code"] == 0, f"{label} failed; inspect {log}")
        print("CHECK_END", label, "0", flush=True)
        return log.read_text(encoding="utf-8")

    exit_code = 1
    try:
        from tools.quality.reviewed_audit_source import (
            audit_source, check_command_sources, parse_audit_output, validate_targets,
        )
        validate_targets(TARGETS)
        require(Path(git(repo, "rev-parse", "--show-toplevel")).resolve() == repo,
                "--repo is not the repository root")
        report["git_head_before"] = git(repo, "rev-parse", "HEAD")
        report["working_tree_status_before"] = git(repo, "status", "--porcelain=v1")
        report["runner_sha256"] = sha256(Path(__file__))
        report["source_sha256_before"] = snapshot(repo)
        report["pins_before"] = check_pins(repo)
        check_command_sources(repo / "lean", TARGETS)
        generated = audit_source(TARGETS)
        audit = output / "OperatorInformationDeclarationAudit.lean"
        audit.write_text(generated, encoding="utf-8")
        report["audit_source"] = str(audit)
        report["audit_source_sha256"] = sha256(audit)
        if args.prepare_only:
            report["status"] = "PREPARED_NOT_EXECUTED"
            exit_code = 0
        else:
            version = run("lean-version", ["env", "lean", "--version"])
            expected = report["pins_before"]["toolchain"].rsplit(":v", 1)[-1]
            require(f"Lean (version {expected}," in version,
                    "Executing compiler differs from the pinned Lean version")
            report["lean_version_output"] = version
            report["lake_version_output"] = run("lake-version", ["env", "lake", "--version"])
            run("selected-owner-build", ["build", *TARGETS])
            require(snapshot(repo) == report["source_sha256_before"],
                    "Selected sources or infrastructure changed during builds")
            require(audit.read_text(encoding="utf-8") == audit_source(TARGETS) == generated,
                    "Runtime audit source or maintained generator changed")
            raw = run("fresh-native-audit", ["env", "lean", "-DwarningAsError=true", str(audit)])
            report["audit"] = parse_native_audit(raw, TARGETS, parse_audit_output)
            report["source_sha256_after"] = snapshot(repo)
            report["pins_after"] = check_pins(repo)
            check_command_sources(repo / "lean", TARGETS)
            report["git_head_after"] = git(repo, "rev-parse", "HEAD")
            require(report["source_sha256_before"] == report["source_sha256_after"] and
                    report["pins_before"] == report["pins_after"] and
                    report["git_head_before"] == report["git_head_after"] and
                    sha256(Path(__file__)) == report["runner_sha256"] and
                    sha256(audit) == report["audit_source_sha256"],
                    "Selected sources, dependencies, HEAD, runner, or audit changed during validation")
            report["status"] = "PASSED_SELECTED_OWNERS"
            exit_code = 0
    except (Exception, KeyboardInterrupt) as error:
        report["status"] = "FAILED"
        report["failure"] = type(error).__name__ + ": " + str(error)
        print(report["failure"], file=sys.stderr, flush=True)
        if isinstance(error, KeyboardInterrupt):
            exit_code = 130
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    receipt = output / "validation.json"
    receipt.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(report["status"], receipt, flush=True)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
