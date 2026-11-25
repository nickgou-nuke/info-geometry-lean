#!/usr/bin/env python3
"""Compile the exact capstone source closure against a pinned Mathlib checkout.

This isolated source check is separate from the root Lake package. It preserves
all repository/dependency pins, uses the maintained shared build lock, compiles
unchanged dependencies in full, and checks new owners with warnings as errors.
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
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.build_lock import BuildLock, DEFAULT_BUILD_LOCK_PATH
from review_capstone_audit import OWNERS, reconcile

AGGREGATE = "InfoGeometry.Geometry.CourantDrinfeldDiracCapstone"
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


def main(existing_lock: BuildLock | None = None) -> None:
    """Run every acceptance check, optionally inside a caller-held build lock.

    This in-process composition hook does not expose a command-line lock bypass.
    """
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--mathlib", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--wait", action="store_true")
    args = parser.parse_args()
    mathlib, work = args.mathlib.resolve(), args.work.resolve()
    if work == ROOT or work.is_relative_to(ROOT / "lean"):
        raise ValueError("Verification output must be separate from owner sources")
    sources, build, logs = work / "sources", work / "build", work / "logs"
    for directory in (sources, build, logs):
        directory.mkdir(parents=True, exist_ok=True)
    report = {"status": "FAIL", "scope": "isolated exact-pin source closure", "commands": []}
    receipts = {}
    lock = (BuildLock(DEFAULT_BUILD_LOCK_PATH, "courant-dirac-verification", block=args.wait)
            if existing_lock is None else existing_lock)

    def run(argv: list[str], label: str, cwd: Path, env: dict | None = None) -> str:
        log = logs / f"{label}.log"
        print(f"RUN {label}", flush=True)
        with log.open("w") as stream:
            result = subprocess.run(argv, cwd=cwd, env=env, stdout=stream, stderr=subprocess.STDOUT,
                                    pass_fds=(lock.fileno(),))
        report["commands"].append({"argv": argv, "cwd": str(cwd), "exit_code": result.returncode,
                                   "log": str(log), "log_sha256": sha(log)})
        if result.returncode:
            print(log.read_text(), flush=True)
            raise RuntimeError(f"{label}: exit {result.returncode}")
        return log.read_text()

    try:
        if existing_lock is not None:
            require(type(lock) is BuildLock, "Expected the maintained BuildLock type")
            require(lock.lock_path.resolve() == DEFAULT_BUILD_LOCK_PATH.resolve(),
                    "Existing lock is not the canonical shared build lock")
            require(not lock.shared, "Existing build lock must be exclusive")
            # fileno() rejects an unacquired/released BuildLock. Verify that its
            # live descriptor still refers to the canonical lock-file inode.
            held = os.fstat(lock.fileno())
            canonical = DEFAULT_BUILD_LOCK_PATH.stat()
            require((held.st_dev, held.st_ino) == (canonical.st_dev, canonical.st_ino),
                    "Existing lock descriptor is not the canonical lock file")
        # The maintained BuildLock is reference-counted. Re-entering a held
        # instance adds one reference; this context releases exactly that one
        # reference on success or failure, leaving the caller's lock held.
        require(not os.environ.get("LAKE_PACKAGE_OVERRIDES"), "Unexpected Lake package overrides")
        with lock:
            require((ROOT / "lean-toolchain").read_text().strip() == TOOLCHAIN, "Root toolchain mismatch")
            manifest = json.loads((ROOT / "lake-manifest.json").read_text())
            root_pins = {p["name"]: p.get("rev") for p in manifest["packages"]}
            require(root_pins["mathlib"] == PIN, "Root Mathlib pin mismatch")
            require(output(["git", "rev-parse", "HEAD"], mathlib) == PIN, "Mathlib revision mismatch")
            require(not output(["git", "status", "--porcelain", "--untracked-files=all"], mathlib),
                    "Mathlib source checkout is not clean")
            require((mathlib / "lean-toolchain").read_text().strip() == TOOLCHAIN, "Mathlib toolchain mismatch")
            controls = [ROOT / p for p in (
                "lean-toolchain", "lake-manifest.json", "lakefile.lean", "tools/build_lock.py",
                "verification/courant-dirac/verify.py", "verification/courant-dirac/CapstoneDeclarationAudit.lean",
                "verification/courant-dirac/review_capstone_audit.py")]
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

            order, imports, hashes = [], {}, {}

            def visit(module: str) -> None:
                if module in imports:
                    return
                path = ROOT / "lean" / (module.replace(".", "/") + ".lean")
                data = path.read_bytes()
                deps = [m for m in IMPORT.findall(data.decode("utf-8")) if m.startswith("InfoGeometry.")]
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
                run(command, module, sources, env)
                artifacts = {str(p): sha(p) for p in artifact.parent.glob(artifact.name + "*") if p.is_file()}
                require(str(artifact) in artifacts, f"Missing compiler artifact: {module}")
                receipts[module] = {"source_sha256": hashes[module], "artifacts": artifacts,
                                    "imports": {dep: receipts[dep]["artifacts"] for dep in imports[module]},
                                    "warnings_as_errors": module in OWNERS or module == AGGREGATE}

            audit = ROOT / "verification/courant-dirac/CapstoneDeclarationAudit.lean"
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
            print(json.dumps({"status": "PASS", "compiled": order,
                              "audit_count": report["native_audit"]["declarations"]}), flush=True)
    except BaseException as error:
        report["error"] = repr(error)
        raise
    finally:
        (work / "validation.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
