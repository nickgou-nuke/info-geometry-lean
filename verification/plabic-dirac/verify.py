#!/usr/bin/env python3
"""Compile the exact plabic/Dirac source closure against a pinned Mathlib checkout.

This isolated source check is separate from the root Lake package. It preserves
all repository/dependency pins, uses the maintained shared build lock, compiles
unchanged dependencies in full, and checks new owners with warnings as errors.
An explicit resume reuses only successful source/import/artifact-hash receipts.
Legacy adoption is separately requested and records its hashes after failure.
It never removes caches or substitutes imports. The supplied Mathlib checkout
must already have its normal dependency artifacts available.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.build_lock import BuildLock, DEFAULT_BUILD_LOCK_PATH
from review_plabic_audit import OWNERS, reconcile

AGGREGATE = "InfoGeometry.Geometry.PlabicDiracCourantUnification"
AUDIT_SOURCE = ROOT / "lean/InfoGeometry/Geometry/PlabicDeclarationAudit.lean"
PIN = "d13f23b723b8a846827a245b89c10fc7d3f11612"
TOOLCHAIN = "leanprover/lean4:v4.34.1"
IMPORT = re.compile(r"^(?:public\s+)?import\s+([A-Za-z0-9_.]+)", re.MULTILINE)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def output(argv: list[str], cwd: Path) -> str:
    return subprocess.check_output(argv, cwd=cwd, text=True).strip()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)



# The one legacy transaction format did hash artifacts in memory after success,
# but persisted them only after the entire build. Adoption is explicitly limited
# to its three completed prerequisites; it never asserts a persisted old hash.
LEGACY_RUNNER_SHA256 = "c1cd28e50ac4ae4382cda372c9341855dc70533ae9c04c4d5b22d30fcc1a816d"
LEGACY_COMPLETED = (
    "InfoGeometry.Algebra.FiniteSpinAlgebra",
    "InfoGeometry.Meta.Architecture",
    "InfoGeometry.Clifford.NeutralPhaseSpaceCore",
)


def atomic_json(path: Path, value: dict) -> None:
    temporary = path.with_name(path.name + f".{os.getpid()}.tmp")
    with temporary.open("w") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def artifact_hashes(artifact: Path) -> dict[str, str]:
    paths = sorted(p for p in artifact.parent.glob(artifact.name + "*") if p.is_file())
    require(not any(p.is_symlink() for p in paths), "Symlinked compiler artifact")
    return {str(p): sha(p) for p in paths}


def archive_previous(work: Path) -> dict:
    checkpoint = work / "checkpoint.json"
    previous_path = checkpoint if checkpoint.is_file() else work / "validation.json"
    require(previous_path.is_file(), "No previous verification transaction to resume")
    digest = sha(previous_path)
    previous = json.loads(previous_path.read_text())
    history = work / "history" / digest
    history.mkdir(parents=True, exist_ok=True)
    archived = history / "report.json"
    if not archived.exists():
        shutil.copy2(previous_path, archived)
    require(sha(archived) == digest, "Archived report changed")
    previous["archived_report"] = {"path": str(archived), "sha256": digest,
                                   "mtime_ns": previous_path.stat().st_mtime_ns}
    # Preserve all original command output before the next invocation reuses log names.
    for index, command in enumerate(previous.get("commands", [])):
        log = Path(command["log"])
        require(log.is_file() and sha(log) == command["log_sha256"], f"Prior log changed: {log}")
        destination = history / f"{index:03d}-{log.name}"
        if not destination.exists():
            shutil.copy2(log, destination)
        require(sha(destination) == command["log_sha256"], f"Archived log changed: {destination}")
        command["log"] = str(destination)
    for receipt in previous.get("compiled_artifacts", {}).values():
        old = receipt.get("compile_command", {})
        matches = [c for c in previous.get("commands", [])
                   if c.get("argv") == old.get("argv") and c.get("cwd") == old.get("cwd")
                   and c.get("exit_code") == 0 and c.get("log_sha256") == old.get("log_sha256")]
        if len(matches) == 1:
            receipt["compile_command"] = dict(matches[0])
    return previous


def adopt_legacy(previous: dict, sources: Path, build: Path, lean: str) -> dict:
    runner = str(ROOT / "verification/plabic-dirac/verify.py")
    require(previous.get("configs", {}).get(runner) == LEGACY_RUNNER_SHA256,
            "Legacy adoption requires the inspected predecessor verifier")
    require(previous.get("status") == "FAIL" and
            previous.get("error") == "RuntimeError('InfoGeometry.Geometry.SkewGraphNeutralPairing: exit 1')",
            "Legacy adoption is limited to the recorded SkewGraphNeutralPairing failure")
    require(previous.get("source_order", [])[:3] == list(LEGACY_COMPLETED),
            "Unexpected legacy prerequisite order")
    adopted = {}
    commands = previous["commands"]
    for module in LEGACY_COMPLETED:
        relative = Path(module.replace(".", "/") + ".lean")
        source, owner = sources / relative, ROOT / "lean" / relative
        expected_source = previous["source_hashes"][module]
        require(sha(source) == expected_source == sha(owner), f"Legacy source changed: {module}")
        artifact = build / relative.with_suffix(".olean")
        argv = [lean, str(relative), "-o", str(artifact)]
        matches = [(i, c) for i, c in enumerate(commands) if c.get("argv") == argv]
        require(len(matches) == 1, f"No unique prior compiler receipt: {module}")
        index, command = matches[0]
        require(command["exit_code"] == 0 and command["cwd"] == str(sources),
                f"Unsuccessful or mismatched prior compile: {module}")
        require(index + 1 < len(commands), f"No subsequent command timestamp: {module}")
        lower = Path(command["log"]).stat().st_mtime_ns
        upper = Path(commands[index + 1]["log"]).stat().st_mtime_ns
        require(source.stat().st_mtime_ns <= lower, f"Legacy source copy was rewritten: {module}")
        artifacts = artifact_hashes(artifact)
        require(str(artifact) in artifacts, f"Missing prior compiler artifact: {module}")
        metadata = {}
        for name in artifacts:
            stat = Path(name).stat()
            require(lower <= stat.st_mtime_ns == stat.st_ctime_ns <= upper,
                    f"Artifact lacks the original compile-window metadata: {name}")
            metadata[name] = {"size": stat.st_size, "mtime_ns": stat.st_mtime_ns,
                              "ctime_ns": stat.st_ctime_ns}
        deps = [m for m in IMPORT.findall(source.read_text()) if m in previous["source_hashes"]]
        require(all(dep in adopted for dep in deps), f"Unadopted legacy import: {module}")
        adopted[module] = {
            "source_sha256": expected_source, "artifacts": artifacts,
            "imports": {dep: adopted[dep]["artifacts"] for dep in deps},
            "warnings_as_errors": False, "compile_command": command,
            "provenance": {"method": "post-failure-adoption", "hash_sampled_at_ns": time.time_ns(),
                           "artifact_metadata": metadata, "compile_window_ns": [lower, upper],
                           "previous_report": previous["archived_report"],
                           "note": "Hashes sampled now; original per-module hashes were not persisted."},
        }
    return adopted


def main() -> None:
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--mathlib", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--wait", action="store_true")
    resumption = parser.add_mutually_exclusive_group()
    resumption.add_argument("--resume", action="store_true",
                            help="Reuse successful persisted source/import/artifact-hash checkpoints")
    resumption.add_argument("--adopt-completed", action="store_true",
                            help="Explicitly adopt the three completed prerequisites from the inspected legacy failure")
    args = parser.parse_args()
    mathlib, work = args.mathlib.resolve(), args.work.resolve()
    if work == ROOT or work.is_relative_to(ROOT / "lean"):
        raise ValueError("Verification output must be separate from owner sources")
    sources, build, logs = work / "sources", work / "build", work / "logs"
    for directory in (sources, build, logs):
        directory.mkdir(parents=True, exist_ok=True)
    report = {"status": "FAIL", "scope": "isolated exact-pin source closure", "commands": []}
    receipts = {}
    report.update({"checkpoint_format": 1, "compiled_artifacts": receipts,
                   "compiled_modules": [], "reused_modules": []})
    previous = None
    prior_receipts = {}
    lock = BuildLock(DEFAULT_BUILD_LOCK_PATH, "plabic-dirac-verification", block=args.wait)

    def run(argv: list[str], label: str, cwd: Path, env: dict | None = None) -> str:
        log = logs / f"{label}.log"
        print(f"RUN {label}", flush=True)
        started_ns = time.time_ns()
        with log.open("w") as stream:
            result = subprocess.run(argv, cwd=cwd, env=env, stdout=stream, stderr=subprocess.STDOUT,
                                    pass_fds=(lock.fileno(),))
        report["commands"].append({"argv": argv, "cwd": str(cwd), "exit_code": result.returncode,
                                   "log": str(log), "log_sha256": sha(log),
                                   "started_ns": started_ns, "finished_ns": time.time_ns()})
        if result.returncode:
            print(log.read_text(), flush=True)
            raise RuntimeError(f"{label}: exit {result.returncode}")
        return log.read_text()

    try:
        require(not os.environ.get("LAKE_PACKAGE_OVERRIDES"), "Unexpected Lake package overrides")
        with lock:
            if args.resume or args.adopt_completed:
                previous = archive_previous(work)
                report["resumed_from"] = previous["archived_report"]
            require((ROOT / "lean-toolchain").read_text().strip() == TOOLCHAIN, "Root toolchain mismatch")
            manifest = json.loads((ROOT / "lake-manifest.json").read_text())
            root_pins = {p["name"]: p.get("rev") for p in manifest["packages"]}
            require(root_pins["mathlib"] == PIN, "Root Mathlib pin mismatch")
            require(output(["git", "rev-parse", "HEAD"], mathlib) == PIN, "Mathlib revision mismatch")
            require(not output(["git", "status", "--porcelain", "--untracked-files=all"], mathlib),
                    "Mathlib source checkout is not clean")
            require((mathlib / "lean-toolchain").read_text().strip() == TOOLCHAIN, "Mathlib toolchain mismatch")
            for checkout in (ROOT, mathlib):
                require((checkout / ".git").is_dir(), f"Expected an independent Git checkout: {checkout}")
                require(not (checkout / ".lake").is_symlink(), f"Symlinked Lake root: {checkout}")
                require(not (checkout / ".lake/packages").is_symlink(), f"Symlinked package root: {checkout}")
            verification_controls = {
                ROOT / "verification/plabic-dirac/verify.py", AUDIT_SOURCE,
                ROOT / "verification/plabic-dirac/review_plabic_audit.py",
            }
            controls = [ROOT / p for p in (
                "lean-toolchain", "lake-manifest.json", "lakefile.lean", "tools/build_lock.py")]
            controls += sorted(verification_controls)
            controls += [mathlib / p for p in ("lean-toolchain", "lake-manifest.json", "lakefile.lean")]
            dependency_pins = {}
            for package in json.loads((mathlib / "lake-manifest.json").read_text())["packages"]:
                location = mathlib / ".lake/packages" / package["name"]
                actual = output(["git", "rev-parse", "HEAD"], location)
                require(actual == package["rev"] == root_pins[package["name"]],
                        f"Dependency revision mismatch: {package['name']}")
                require(not output(["git", "status", "--porcelain", "--untracked-files=all"], location),
                        f"Dependency source checkout is not clean: {package['name']}")
                dependency_pins[package["name"]] = actual

            probe = "import os,shutil,json; print(json.dumps({'lean':shutil.which('lean'),'path':os.environ.get('LEAN_PATH','')}))"
            lean_env = json.loads(run([args.lake, "env", "python3", "-c", probe], "environment", mathlib))
            lean = lean_env["lean"]
            require(isinstance(lean, str) and bool(lean), "Lake did not resolve a Lean executable")
            lake_reported_lean = lean
            # Preserve the caller's lexical toolchain path after relocation, but
            # only when its sibling compiler is byte-identical to Lake's result.
            # Both the actual resolution and chosen invocation are recorded.
            requested_lake = Path(args.lake)
            if requested_lake.is_absolute():
                sibling_lean = requested_lake.with_name("lean")
                require(sibling_lean.is_file(), "Explicit Lake path has no sibling Lean executable")
                require(sha(sibling_lean) == sha(Path(lake_reported_lean)),
                        "Explicit Lake sibling differs from the compiler resolved by Lake")
                lean = str(sibling_lean)
            report["compiler_resolution"] = {
                "lake_reported_lean": lake_reported_lean, "invoked_lean": lean,
                "matching_binary_sha256": sha(Path(lean)),
            }
            version = run([lean, "--version"], "lean-version", mathlib).strip()
            require("version 4.34.1," in version, "Compiler version mismatch: " + version)
            controls.append(Path(lean))
            configs = {str(p): sha(p) for p in controls}
            search_roots = [(mathlib / p).resolve() for p in lean_env["path"].split(os.pathsep) if p]
            expected_roots = {(mathlib / ".lake/build/lib/lean").resolve(),
                              (Path(lean).resolve().parents[1] / "lib/lean").resolve()}
            expected_roots.update((mathlib / ".lake/packages" / name / ".lake/build/lib/lean").resolve()
                                  for name in dependency_pins)
            require(set(search_roots) <= expected_roots, "Unreviewed Lean search path: " + str(search_roots))
            require((mathlib / ".lake/build/lib/lean").resolve() in search_roots, "Missing Mathlib search path")
            search = [str(build)] + list(map(str, search_roots))
            env = dict(os.environ, LEAN_PATH=os.pathsep.join(search))

            if previous is not None:
                require(previous.get("mathlib") == PIN and previous.get("toolchain") == TOOLCHAIN,
                        "Resume toolchain or Mathlib identity changed")
                require(previous.get("dependency_pins") == dependency_pins and
                        previous.get("lean_binary_sha256") == sha(Path(lean)),
                        "Resume dependency/compiler identity changed")
                for path, digest in configs.items():
                    # The audit and reconciliation run afresh after compilation.
                    # Environment controls must match even for legacy adoption;
                    # normal receipt resumption additionally pins this runner below.
                    if Path(path) not in verification_controls:
                        require(previous.get("configs", {}).get(path) == digest,
                                f"Resume compiler configuration changed: {path}")
                if args.adopt_completed:
                    prior_receipts = adopt_legacy(previous, sources, build, lean)
                    report["adoption_policy"] = "post-failure hashes, source/command/log/metadata provenance"
                else:
                    runner = str(Path(__file__).resolve())
                    require(previous.get("configs", {}).get(runner) == configs[runner],
                            "Resume verifier implementation changed")
                    require(previous.get("checkpoint_format") == 1 and
                            bool(previous.get("compiled_artifacts")),
                            "No persisted per-module hash receipts; explicit legacy adoption is separate")
                    prior_receipts = previous["compiled_artifacts"]

            order, imports, hashes = [], {}, {}

            def visit(module: str) -> None:
                if module in imports:
                    return
                path = ROOT / "lean" / (module.replace(".", "/") + ".lean")
                data = path.read_bytes()
                # Follow every reachable repo-owned module in the canonical source lane,
                # including a non-InfoGeometry namespace if a retained owner imports one.
                imported = IMPORT.findall(data.decode("utf-8"))
                deps = []
                for imported_module in imported:
                    owner_path = ROOT / "lean" / (imported_module.replace(".", "/") + ".lean")
                    if owner_path.is_file():
                        deps.append(imported_module)
                    elif imported_module.startswith("InfoGeometry."):
                        raise FileNotFoundError(f"Missing repository dependency: {imported_module}")
                imports[module] = deps
                for dep in deps:
                    visit(dep)
                hashes[module] = hashlib.sha256(data).hexdigest()
                target = sources / path.relative_to(ROOT / "lean")
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
                require(sha(target) == hashes[module], f"Source copy mismatch: {module}")
                order.append(module)

            visit(AGGREGATE)
            require(set(OWNERS) <= set(order), "Aggregate source closure omits an audited owner")
            report.update({"root_head": output(["git", "rev-parse", "HEAD"], ROOT),
                           "toolchain": TOOLCHAIN, "lean_version": version,
                           "lean_binary_sha256": sha(Path(lean)), "mathlib": PIN,
                           "dependency_pins": dependency_pins, "configs": configs,
                           "source_hashes": hashes, "source_order": order})
            for module in order:
                for dep in imports[module]:
                    require(receipts.get(dep, {}).get("source_sha256") == hashes[dep], f"Stale imported source: {dep}")
                    for path, digest in receipts[dep]["artifacts"].items():
                        require(sha(Path(path)) == digest, f"Imported artifact changed: {path}")
                relative = Path(module.replace(".", "/") + ".lean")
                artifact = build / relative.with_suffix(".olean")
                artifact.parent.mkdir(parents=True, exist_ok=True)
                command = [lean]
                if module in OWNERS or module == AGGREGATE:
                    command.append("-DwarningAsError=true")
                command.extend([str(relative), "-o", str(artifact)])
                dependencies = {dep: receipts[dep]["artifacts"] for dep in imports[module]}
                prior = prior_receipts.get(module)
                prior_command = prior.get("compile_command", {}) if prior else {}
                prior_log = Path(prior_command.get("log", ""))
                if (prior and prior.get("source_sha256") == hashes[module]
                        and prior.get("imports") == dependencies
                        and prior.get("warnings_as_errors") == (module in OWNERS or module == AGGREGATE)
                        and prior_command.get("argv") == command
                        and prior_command.get("cwd") == str(sources)
                        and prior_command.get("exit_code") == 0
                        and prior_log.is_file() and sha(prior_log) == prior_command.get("log_sha256")
                        and prior.get("artifacts") == artifact_hashes(artifact)
                        and str(artifact) in prior["artifacts"]):
                    receipts[module] = prior
                    report["reused_modules"].append(module)
                    print(f"REUSE {module}", flush=True)
                else:
                    run(command, module, sources, env)
                    artifacts = artifact_hashes(artifact)
                    require(str(artifact) in artifacts, f"Missing compiler artifact: {module}")
                    receipts[module] = {"source_sha256": hashes[module], "artifacts": artifacts,
                                        "imports": dependencies,
                                        "warnings_as_errors": module in OWNERS or module == AGGREGATE,
                                        "compile_command": dict(report["commands"][-1]),
                                        "provenance": {"method": "compiled",
                                                       "hash_sampled_at_ns": time.time_ns()}}
                    report["compiled_modules"].append(module)
                # Persist each successful module before starting the next one.
                atomic_json(work / "checkpoint.json", report)

            audit = AUDIT_SOURCE
            audit_data = audit.read_bytes()
            (sources / audit.name).write_bytes(audit_data)
            report["audit_source_sha256"] = hashlib.sha256(audit_data).hexdigest()
            require(sha(sources / audit.name) == report["audit_source_sha256"], "Audit source copy mismatch")
            run([lean, "-DwarningAsError=true", audit.name], "declaration-audit", sources, env)
            report["native_audit"] = reconcile(logs / "declaration-audit.log")

            require(configs == {str(p): sha(p) for p in controls}, "Verification controls changed")
            for module, digest in hashes.items():
                relative = Path(module.replace(".", "/") + ".lean")
                require(sha(ROOT / "lean" / relative) == digest == sha(sources / relative),
                        f"Compiled source changed: {module}")
                for path, artifact_hash in receipts[module]["artifacts"].items():
                    require(sha(Path(path)) == artifact_hash, f"Compiled artifact changed: {path}")
            require(sha(sources / audit.name) == report["audit_source_sha256"], "Compiled audit changed")
            require(output(["git", "rev-parse", "HEAD"], mathlib) == PIN, "Mathlib revision changed")
            require(not output(["git", "status", "--porcelain", "--untracked-files=all"], mathlib), "Mathlib source changed")
            for name, pin in dependency_pins.items():
                location = mathlib / ".lake/packages" / name
                require(output(["git", "rev-parse", "HEAD"], location) == pin, f"Dependency revision changed: {name}")
                require(not output(["git", "status", "--porcelain", "--untracked-files=all"], location),
                        f"Dependency source changed: {name}")
            report["compiled_artifacts"] = receipts
            report["status"] = "PASS"
            print(json.dumps({"status": "PASS", "source_closure": order,
                              "compiled": report["compiled_modules"], "reused": report["reused_modules"],
                              "audit_count": report["native_audit"]["declarations"]}), flush=True)
    except BaseException as error:
        report["error"] = repr(error)
        raise
    finally:
        # A failed lock acquisition or failed archival must not overwrite the
        # only existing legacy evidence that the requested resume still needs.
        filename = ("resume-attempt.json" if (args.resume or args.adopt_completed)
                    and previous is None else "validation.json")
        atomic_json(work / filename, report)


if __name__ == "__main__":
    main()
