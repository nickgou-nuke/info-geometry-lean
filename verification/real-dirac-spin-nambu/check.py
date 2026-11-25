#!/usr/bin/env python3
"""Fresh, bounded verification of the real Dirac/spin/Nambu packet.

Requires Python 3.11+, the pinned Lean runtime, and existing pinned package
sources. Usage: python3 check.py --repo /absolute/repo --output /new/report/path

The output directory must be new and outside the Lean source directories.
Every Lake invocation uses the existing focused package's shared-lock wrapper;
all targets are explicit. This runner does not install dependencies, invoke an
update command, read old acceptance results, or run the old package defaults.
Exit codes: 0 passed, 1 failed, 2 blocked, 130 interrupted.
"""

from __future__ import annotations

import argparse
from collections import Counter
from contextlib import redirect_stdout
from datetime import datetime, timezone
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tomllib

TARGETS = (
    "InfoGeometry.Canonical.RealPauliPfaffianKernel",
    "InfoGeometry.Algebra.AssociativeNambuOperators",
    "InfoGeometry.Canonical.RealDiracLinearLift",
    "InfoGeometry.Canonical.RealDiracSpinCasimir",
    "InfoGeometry.Canonical.RealDiracNambuChecks",
)
OWNERS = TARGETS[:-1]
REUSED = (
    "InfoGeometry.Canonical.RealPauliPfaffianKernel.diracVector_sq",
    "InfoGeometry.Canonical.RealPauliPfaffianKernel.diracVector_anticomm",
    "InfoGeometry.Canonical.RealPauliPfaffianKernel.diracVolume_eq_phase",
    "InfoGeometry.Clifford.GullDoranPseudoscalarBridge.realPhaseAxis_sq",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.cyclicCommutatorTriple_eq_right_contraction",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.alternatingProduct3_swap_left",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.alternatingProduct3_swap_right",
    "InfoGeometry.Algebra.NonAssocDerivation.derivations",
    "InfoGeometry.Core.PeirceDecomposition.peirce10_mul_peirce10_eq_zero",
    "InfoGeometry.Core.PeirceDecomposition.mem_range_component10Linear",
)
REUSED_OWNERS = (
    "InfoGeometry.Clifford.GullDoranPseudoscalarBridge",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.AlternatingCornerTriple",
    "InfoGeometry.Algebra.NonAssocDerivation",
    "InfoGeometry.Core.PeirceDecomposition",
    "InfoGeometry.Core.PeirceMatrixPerfectPairing",
)


class Blocked(RuntimeError):
    """A required execution resource is unavailable."""


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def hashes(paths: dict[str, Path]) -> dict[str, str | None]:
    return {name: sha256(path) if path.is_file() else None for name, path in paths.items()}


def source_path(root: Path, module: str) -> Path:
    return root / "lean" / (module.replace(".", "/") + ".lean")


def audit_call(function, *args):
    try:
        return function(*args)
    except SystemExit as error:
        raise RuntimeError(f"{function.__name__}: {error}") from error


def run_command(report, output: Path, root: Path, label: str, argv: list[str],
                *, runtime_probe: bool = False) -> str:
    log = output / f"{len(report['commands']) + 1:02d}-{label}.log"
    record = {"stage": label, "argv": argv, "cwd": str(root),
              "started_at": now(), "exit_code": None, "log": str(log)}
    report["commands"].append(record)
    print(f"[{label}] {' '.join(argv)}", flush=True)
    try:
        with log.open("w", encoding="utf-8") as stream:
            result = subprocess.run(argv, cwd=root, stdout=stream,
                                    stderr=subprocess.STDOUT, check=False)
        record["exit_code"] = result.returncode
    except OSError as error:
        record["launch_error"] = str(error)
        raise Blocked(f"Cannot launch {label}: {error}") from error
    finally:
        record["finished_at"] = now()
        if log.is_file():
            record["log_sha256"] = sha256(log)
    if record["exit_code"] != 0:
        exception = Blocked if runtime_probe else RuntimeError
        raise exception(f"{label} exited {record['exit_code']}; see {log}")
    return log.read_text(encoding="utf-8", errors="replace")


def main(*, targets: tuple[str, ...] = TARGETS,
         owners: tuple[str, ...] = OWNERS,
         reused: tuple[str, ...] = REUSED,
         reused_owners: tuple[str, ...] = REUSED_OWNERS,
         probe_name: str = "RealDiracSpinNambuAxioms.lean",
         entrypoint: Path | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    root, output = args.repo.resolve(), args.output.resolve()
    try:
        if any(output.is_relative_to(root / name) for name in ("lean", "src")):
            raise Blocked("Output must be outside the repository Lean source directories")
        output.mkdir(parents=True, exist_ok=False)
    except (OSError, Blocked) as error:
        print(json.dumps({"status": "blocked", "passed": False, "exit_code": 2,
                          "compilation": "not_run", "error": str(error)}))
        return 2

    runtime = root / "verification/real-matrix-split"
    helper, locked_runner = runtime / "audit.py", runtime / "check.py"
    sources = {module: source_path(root, module) for module in (*targets, *reused_owners)}
    controls = {
        "runner": Path(__file__).resolve(), "audit_helper": helper,
        "locked_runner": locked_runner, "root_toolchain": root / "lean-toolchain",
        "root_manifest": root / "lake-manifest.json",
        "focused_toolchain": runtime / "lean-toolchain",
        "focused_manifest": runtime / "lake-manifest.json",
        "focused_config": runtime / "lakefile.toml",
    }
    if entrypoint is not None:
        controls["entrypoint"] = entrypoint.resolve()
    report = {
        "schema_version": 1, "started_at": now(), "repo": str(root),
        "runtime": str(runtime), "output": str(output), "targets": list(targets),
        "owner_modules": list(owners), "reused_declarations": list(reused),
        "status": "blocked", "passed": False, "compilation": "not_run",
        "commands": [], "fresh_file_checks": [], "axiom_audit": "not_run", "errors": [],
        "source_paths": {key: str(path) for key, path in sources.items()},
        "control_paths": {key: str(path) for key, path in controls.items()},
        "source_sha256_before": {}, "source_sha256_after": {},
        "control_sha256_before": {}, "control_sha256_after": {},
        "source_stability": "not_checked", "control_stability": "not_checked",
    }
    probe = output / probe_name
    probe_hash = None
    exit_code = 2
    try:
        report["source_sha256_before"] = hashes(sources)
        report["control_sha256_before"] = hashes(controls)
        missing = [str(path) for path in (*sources.values(), *controls.values())
                   if not path.is_file()]
        if missing:
            raise Blocked("Required sources or verification runtime files missing: " + "; ".join(missing))
        sys.dont_write_bytecode = True
        spec = importlib.util.spec_from_file_location("real_dirac_reused_audit", helper)
        if spec is None or spec.loader is None:
            raise Blocked(f"Cannot load audit helper: {helper}")
        audit = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(audit)
        if audit.ROOT.resolve() != root:
            raise RuntimeError("Audit helper resolves a different repository")
        audit_call(audit.check_pins, runtime)
        report["pins"] = "focused manifest and toolchain match root pins"

        inventory = {}
        for module in targets:
            stripped = audit_call(audit.strip_comments, sources[module].read_text(encoding="utf-8"))
            forbidden = audit.FORBIDDEN.findall(stripped)
            if forbidden:
                raise RuntimeError(f"Forbidden proof constructs in {module}: {forbidden}")
            if module in owners:
                inventory[module] = audit_call(audit.owner_declarations, module)
            else:
                count = len(re.findall(r"^\s*example\s*:", stripped, re.MULTILINE))
                report["regression_example_count"] = count
                if count != 6:
                    raise RuntimeError(f"Expected six regression examples, found {count}")
        owner_heads = [name for heads in inventory.values() for name in heads]
        duplicates = [name for name, count in Counter(owner_heads).items() if count != 1]
        if duplicates:
            raise RuntimeError(f"Duplicate public declaration heads: {duplicates}")
        expected = set(owner_heads).union(reused)
        report["owner_head_count"] = len(owner_heads)
        report["deduplicated_reused_heads"] = sorted(set(owner_heads).intersection(reused))
        report["expected_axiom_records"] = len(expected)
        (output / "inventory.json").write_text(json.dumps(
            {"owners": inventory, "reused": list(reused), "expected": sorted(expected)},
            indent=2) + "\n", encoding="utf-8")
        probe.write_text(
            "/-\nCopyright (c) 2026 InfoGeometry Authors. All rights reserved.\n"
            "Released under Apache 2.0 license as described in the file LICENSE.\n"
            "Authors: InfoGeometry Engine Contributors\n-/\n\n"
            + "".join(f"import {module}\n" for module in owners)
            + "\n-- Fresh, bounded public-head and reused-declaration axiom probe.\n"
            + "".join(f"#print axioms {name}\n" for name in sorted(expected)),
            encoding="utf-8")
        probe_hash = sha256(probe)
        report["axiom_probe"] = {"path": str(probe), "sha256": probe_hash}

        config = tomllib.loads((runtime / "lakefile.toml").read_text(encoding="utf-8"))
        if (runtime / config["srcDir"]).resolve() != root / "lean":
            raise RuntimeError("Focused package srcDir does not resolve to the repository Lean source")
        package_root = (runtime / config["packagesDir"]).resolve()
        manifest = json.loads((runtime / "lake-manifest.json").read_text(encoding="utf-8"))
        missing_packages = [package["name"] for package in manifest["packages"]
                            if not (package_root / package["name"] / package["configFile"]).is_file()]
        blockers = []
        if shutil.which("lake") is None:
            blockers.append("lake executable is absent from PATH")
        if missing_packages:
            blockers.append("pinned package sources unavailable: " + ", ".join(missing_packages))
        if blockers:
            raise Blocked("; ".join(blockers))

        prefix = [sys.executable, str(locked_runner)]
        version_log = run_command(report, output, root, "runtime",
                                  prefix + ["env", "lean", "--version"], runtime_probe=True)
        version = (root / "lean-toolchain").read_text().strip().rsplit(":", 1)[-1].removeprefix("v")
        if not re.search(r"\bversion\s+" + re.escape(version) + r"(?:[,\s)])", version_log):
            raise Blocked(f"Lean runtime does not report the pinned version {version}")
        report["compilation"] = "started"
        run_command(report, output, root, "build", prefix + ["build", *targets])
        for index, module in enumerate(targets, 1):
            run_command(report, output, root, f"fresh-{index}",
                        prefix + ["env", "lean", "-DwarningAsError=true", str(sources[module])])
            report["fresh_file_checks"].append(module)
        report["compilation"] = f"{len(targets)} fresh warning-as-error file checks passed"
        axiom_log = run_command(report, output, root, "axioms",
                                prefix + ["env", "lean", "-DwarningAsError=true", str(probe)])
        diagnostic = io.StringIO()
        with redirect_stdout(diagnostic):
            audit_call(audit.check_axioms, axiom_log, expected)
        (output / "axiom-check.txt").write_text(diagnostic.getvalue(), encoding="utf-8")
        report["axiom_audit"] = "passed"
        audit_call(audit.check_pins, runtime)
        report["status"], exit_code = "passed", 0
    except Blocked as error:
        report["status"], exit_code = "blocked", 2
        report["errors"].append(str(error))
    except KeyboardInterrupt:
        report["status"], exit_code = "interrupted", 130
        report["errors"].append("Interrupted; no acceptance claimed")
    except Exception as error:
        report["status"], exit_code = "failed", 1
        report["errors"].append(f"{type(error).__name__}: {error}")
    finally:
        try:
            for category, paths in (("source", sources), ("control", controls)):
                after = hashes(paths)
                report[f"{category}_sha256_after"] = after
                before = report[f"{category}_sha256_before"]
                if before:
                    stable = before == after
                    report[f"{category}_stability"] = "unchanged" if stable else "changed"
                    if not stable:
                        report["status"], exit_code = "failed", 1
                        report["errors"].append(f"{category.capitalize()} hashes changed during run")
            if probe_hash is not None and (not probe.is_file() or sha256(probe) != probe_hash):
                report["status"], exit_code = "failed", 1
                report["errors"].append("Axiom probe changed during run")
        except OSError as error:
            report["status"], exit_code = "failed", 1
            report["errors"].append(f"Final fingerprint failure: {error}")
        report["passed"] = report["status"] == "passed" and exit_code == 0
        report["exit_code"], report["finished_at"] = exit_code, now()
        summary = output / "summary.json"
        summary.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(json.dumps({key: report[key] for key in
                          ("status", "passed", "compilation", "exit_code", "errors")}
                         | {"summary": str(summary)}))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
