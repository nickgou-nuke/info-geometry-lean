#!/usr/bin/env python3
"""Rebuild the canonical statistical-geometry boundary proof closure against unchanged Mathlib pins.

This focused, shared-lock check follows scripts/quality/check-rectangular-peirce.sh.
It does not certify the full root Lake package or replace pre-commit/pre-push gates.
It never resolves root optional packages, changes pins, or deletes build caches.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO))

from tools.build_lock import acquire_build_lock
from tools.infra.build import _validate_lake_workspace_integrity
from tools.infra.build_changed_lean import _strip_lean_comments

TARGET = "InfoGeometry.Geometry.StatisticalGeometryBoundariesAudit"
AUDITED_OWNERS = {
    "InfoGeometry.Geometry.Statistical.StatisticalWeylRigidity",
    "InfoGeometry.Geometry.Statistical.StatisticalWeylDualConnections",
    "InfoGeometry.Geometry.DivergenceMixedHessianCounterexample",
    "InfoGeometry.Modular.AmariChentsovDualConnections",
}
SOURCE_ROOT = REPO / "lean"
MATHLIB = REPO / ".lake/packages/mathlib"
IMPORT_RE = re.compile(r"^\s*(?:public\s+|private\s+)?import\s+(.+)$", re.M)
LOCK_FDS: tuple[int, ...] = ()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def output(command: list[str], *, cwd: Path = REPO, env=None) -> str:
    return subprocess.check_output(command, cwd=cwd, env=env, text=True,
                                   pass_fds=LOCK_FDS).strip()


def canonical_closure(module: str) -> list[tuple[str, Path]]:
    """Read canonical local imports in dependency order; reject unknown packages."""
    result: list[tuple[str, Path]] = []
    active: set[str] = set()
    done: set[str] = set()

    def visit(name: str) -> None:
        if name in done:
            return
        if name in active:
            raise RuntimeError(f"Cyclic local import: {name}")
        path = SOURCE_ROOT.joinpath(*name.split(".")).with_suffix(".lean")
        if not path.is_file():
            # These are the only external roots in this finite proof closure.
            if name.split(".")[0] in {"Mathlib", "Lean", "Init", "Std", "Batteries"}:
                return
            raise RuntimeError(f"Missing canonical source or unapproved import: {name}")
        if path.is_symlink():
            raise RuntimeError(f"Refusing symlinked source: {path}")
        active.add(name)
        text = _strip_lean_comments(path.read_text())
        for raw in IMPORT_RE.findall(text):
            for imported in raw.split():
                if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", imported):
                    raise RuntimeError(f"Unsupported import syntax in {path}: {raw}")
                visit(imported)
        active.remove(name)
        done.add(name)
        result.append((name, path))

    visit(module)
    return result


def check_checkout(path: Path, revision: str) -> dict:
    issue = _validate_lake_workspace_integrity(path)
    if issue:
        raise RuntimeError(issue)
    actual = output(["git", "rev-parse", "HEAD"], cwd=path)
    if actual != revision:
        raise RuntimeError(f"Dependency revision mismatch in {path}: {actual} != {revision}")
    dirty = output(["git", "status", "--porcelain", "--untracked-files=normal"], cwd=path)
    if dirty:
        raise RuntimeError(f"Dependency checkout is not clean: {path}\n{dirty}")
    return {"path": str(path), "revision": actual, "clean": True}


def main() -> int:
    global LOCK_FDS
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="Lake from the pinned toolchain")
    parser.add_argument("--output-parent", type=Path,
                        default=REPO / ".artifacts/statistical-geometry-boundaries")
    args = parser.parse_args()
    lake = shutil.which(args.lake)
    if lake is None:
        raise RuntimeError(f"Lake executable not found: {args.lake}")
    args.output_parent.mkdir(parents=True, exist_ok=True)
    # A new directory prevents stale local artifacts from entering this check.
    run = Path(tempfile.mkdtemp(prefix="check-", dir=args.output_parent))
    receipt = {"scope": "canonical statistical-geometry boundary closure only",
               "root_package_verified": False,
               "started_utc": datetime.now(timezone.utc).isoformat(),
               "artifact_directory": str(run), "status": "running", "checks": []}
    print(f"Evidence directory: {run}", flush=True)
    print("Waiting for the repository's shared build lock.", flush=True)
    lock = acquire_build_lock(None, "statistical-geometry-boundaries-qa", block=True)
    # Compiler children retain the lock if this Python process is interrupted.
    LOCK_FDS = (lock.fileno(),)
    try:
        for workspace in (REPO, MATHLIB):
            issue = _validate_lake_workspace_integrity(workspace)
            if issue:
                raise RuntimeError(issue)
        closure = canonical_closure(TARGET)
        if {module for module, _ in closure} != AUDITED_OWNERS | {TARGET}:
            raise RuntimeError("Canonical closure differs from reviewed audit owners")
        pin_files = [REPO / "lean-toolchain", REPO / "lake-manifest.json",
                     MATHLIB / "lean-toolchain", MATHLIB / "lake-manifest.json"]
        source_files = [path for _, path in closure]
        infrastructure = [Path(__file__).resolve(), REPO / "tools/build_lock.py",
                          REPO / "tools/infra/build.py",
                          REPO / "tools/infra/build_changed_lean.py"]
        snapshot = {str(path): sha256(path) for path in pin_files + source_files + infrastructure}
        receipt["source_and_pin_sha256"] = snapshot
        receipt["git_head"] = output(["git", "rev-parse", "HEAD"])
        receipt["git_status"] = output(["git", "status", "--short"])
        toolchain = (REPO / "lean-toolchain").read_text().strip()
        if (MATHLIB / "lean-toolchain").read_text().strip() != toolchain:
            raise RuntimeError("Root and Mathlib toolchains differ")
        receipt["lean_toolchain"] = toolchain
        root_packages = {p["name"]: p for p in json.loads(pin_files[1].read_text())["packages"]}
        mathlib_packages = json.loads(pin_files[3].read_text())["packages"]
        receipt["dependencies"] = [check_checkout(MATHLIB, root_packages["mathlib"]["rev"])]
        for package in mathlib_packages:
            if package["type"] != "git":
                raise RuntimeError(f"Unsupported Mathlib dependency kind: {package['name']}")
            root_package = root_packages.get(package["name"])
            if root_package is not None and root_package.get("rev") != package["rev"]:
                raise RuntimeError(f"Root/Mathlib dependency pins differ: {package['name']}")
            path = MATHLIB / ".lake/packages" / package["name"]
            receipt["dependencies"].append(check_checkout(path, package["rev"]))
        env = os.environ.copy()
        # Lake resolves the pinned Mathlib environment; root optional path packages
        # are deliberately not in this focused dependency graph.
        lean = output([lake, "env", "which", "lean"], cwd=MATHLIB, env=env)
        version = output([lean, "--version"], cwd=MATHLIB, env=env)
        match = re.search(r"version ([^, ]+)", version)
        if match is None or toolchain != "leanprover/lean4:v" + match.group(1):
            raise RuntimeError(f"Running Lean does not match {toolchain}: {version}")
        receipt["lean_version"] = version
        receipt["lake_version"] = output([lake, "--version"], cwd=MATHLIB, env=env)
        lean_path = output([lake, "env", "printenv", "LEAN_PATH"], cwd=MATHLIB, env=env)
        sysroot = Path(output([lean, "--print-prefix"], cwd=MATHLIB, env=env)).resolve()
        paths = []
        for raw in lean_path.split(os.pathsep):
            path = Path(raw)
            path = (path if path.is_absolute() else MATHLIB / path).resolve()
            if not path.is_relative_to(MATHLIB.resolve()) and path != sysroot / "lib/lean":
                raise RuntimeError(f"Unexpected imported artifact path: {path}")
            paths.append(str(path))
        # The root checkout may already own the same pinned package revisions
        # and their compiled artifacts.  Mathlib's standalone environment does
        # not list those root paths, but using them is safe after the revision
        # checks above and avoids requiring a second package build tree.
        root_package_paths = []
        for package in mathlib_packages:
            root_path = REPO / ".lake/packages" / package["name"] / ".lake/build/lib/lean"
            if root_path.is_dir():
                root_package_paths.append(str(root_path.resolve()))
        oleans = run / "oleans"
        oleans.mkdir()
        env["LEAN_PATH"] = os.pathsep.join([str(oleans), *root_package_paths, *paths])
        receipt["lean_path"] = env["LEAN_PATH"]
        for module, source in closure:
            target = oleans.joinpath(*module.split(".")).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            command = [lean, "--root=" + str(SOURCE_ROOT), str(source), "-o", str(target)]
            print(f"Checking {module}", flush=True)
            started = time.monotonic()
            proc = subprocess.run(command, cwd=REPO, env=env, text=True,
                                  capture_output=True, pass_fds=LOCK_FDS)
            log = run / (module + ".log")
            log.write_text(proc.stdout + proc.stderr)
            receipt["checks"].append({"module": module, "source": str(source),
                                      "command": command, "exit_code": proc.returncode,
                                      "seconds": time.monotonic() - started,
                                      "log": str(log)})
            if proc.returncode:
                print(proc.stdout + proc.stderr, end="", flush=True)
                raise RuntimeError(f"Lean failed for {module}; no later module was checked")
            if module == TARGET:
                if f"AUDIT_SUCCESS: {len(AUDITED_OWNERS)} owners" not in proc.stdout:
                    raise RuntimeError("Declaration-complete audit success marker missing")
                owner_counts = {name: int(count) for name, count in re.findall(
                    r"AUDIT_OWNER: ([A-Za-z_0-9.]+): (\d+)", proc.stdout)}
                if set(owner_counts) != AUDITED_OWNERS or not all(owner_counts.values()):
                    raise RuntimeError("Audited declaration owners differ from source closure")
                receipt["owner_declaration_counts"] = owner_counts
                receipt["declaration_audit"] = proc.stdout.strip()
                print(proc.stdout, end="", flush=True)
            receipt["checks"][-1]["olean_sha256"] = sha256(target)
        after = {path: sha256(Path(path)) for path in snapshot}
        if after != snapshot:
            raise RuntimeError("A checked source, pin, or verifier changed during validation")
        if output(["git", "rev-parse", "HEAD"]) != receipt["git_head"]:
            raise RuntimeError("Repository HEAD changed during validation")
        for dependency in receipt["dependencies"]:
            check_checkout(Path(dependency["path"]), dependency["revision"])
        receipt["pins_and_sources_unchanged"] = True
        receipt["status"] = "pass"
        print("FOCUSED_CHECK_PASS (full root package and publication gates are separate)", flush=True)
        return 0
    except Exception as exc:
        receipt["status"] = "fail"
        receipt["error"] = str(exc)
        print(f"FOCUSED_CHECK_FAILED: {exc}", file=sys.stderr, flush=True)
        return 1
    finally:
        receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
        (run / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        LOCK_FDS = ()
        lock.release()


if __name__ == "__main__":
    raise SystemExit(main())
