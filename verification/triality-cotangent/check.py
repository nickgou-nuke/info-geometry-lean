#!/usr/bin/env python3
"""Run the focused checks with pinned inputs and the maintained shared lock.

Existing exact dependency checkouts may be selected through Lake's native
package-location override. Generated dependency artifacts remain writable.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import tomllib

PROJECT = Path(__file__).resolve().parent
ROOT = PROJECT.parents[1]
sys.path.insert(0, str(ROOT))

from tools.build_lock import BuildLock, BuildLockBusyError, acquire_build_lock  # noqa: E402
from tools.infra.build import (  # noqa: E402
    _interrupt_child_and_wait,
    _validate_lake_workspace_integrity,
)
from tools.infra.opengauss_screener import _strip_lean_comments_and_strings  # noqa: E402

EXPECTED_PACKAGES = {
    "mathlib", "plausible", "LeanSearchClient", "importGraph",
    "proofwidgets", "aesop", "Qq", "batteries", "Cli",
}
TARGETS = (
    "InfoGeometry.Geometry.CotangentActionGroupoid",
    "InfoGeometry.Geometry.CotangentLieForm",
    "InfoGeometry.Geometry.FiniteCotangentInvariants",
    "InfoGeometry.Geometry.CotangentFixedShear",
    "InfoGeometry.Lie.CartanTriality",
    "InfoGeometry.Lie.CartanTrialityRepresentation",
    "InfoGeometry.Lie.CartanTrialityCotangent",
    "InfoGeometry.Geometry.TrialityCotangentAudit",
)

CONFIG_NAMES = ("lakefile.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json")
IMPORTS = re.compile(
    r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+([^\n]+)", re.M)


def check_pins() -> list[dict]:
    if (ROOT / "lean-toolchain").read_bytes() != (PROJECT / "lean-toolchain").read_bytes():
        raise RuntimeError("Focused and root Lean toolchains differ")
    root = json.loads((ROOT / "lake-manifest.json").read_text())
    focused = json.loads((PROJECT / "lake-manifest.json").read_text())
    config = tomllib.loads((PROJECT / "lakefile.toml").read_text())
    if focused["name"] != config["name"]:
        raise RuntimeError("Focused manifest and package names differ")
    if (PROJECT / config["srcDir"]).resolve() != ROOT / "lean":
        raise RuntimeError("Focused sources must be the canonical lean directory")
    if (PROJECT / config.get("buildDir", ".lake/build")).resolve() != PROJECT / ".lake/build":
        raise RuntimeError("Focused build outputs must stay in the focused package")
    if (config.get("packagesDir") != "../../.lake/packages"
            or focused.get("packagesDir") != config["packagesDir"]):
        raise RuntimeError("Unexpected focused package directory")
    if focused.get("lakeDir") != ".lake" or focused.get("fixedToolchain") is not True:
        raise RuntimeError("Unexpected focused Lake/toolchain configuration")
    if tuple(config.get("defaultTargets", [])) != TARGETS:
        raise RuntimeError("Unexpected focused validation targets")
    pins = {p["name"]: (p["url"], p["rev"], p.get("subDir"))
            for p in root["packages"] if p["type"] == "git"}
    packages = focused["packages"]
    names = [p["name"] for p in packages]
    if len(names) != len(set(names)) or set(names) != EXPECTED_PACKAGES:
        raise RuntimeError("Unexpected focused dependency inventory")
    for package in packages:
        if package["type"] != "git":
            raise RuntimeError("Focused dependencies must retain Git pins")
        if (package["url"], package["rev"], package.get("subDir")) != pins.get(package["name"]):
            raise RuntimeError(f"Dependency pin differs: {package['name']}")
        if package.get("subDir"):
            raise RuntimeError("This focused package expects whole-checkout dependencies")
    reqs = config.get("require", [])
    if len(reqs) != 1 or reqs[0]["name"] != "mathlib":
        raise RuntimeError("Focused package must require exactly Mathlib")
    if (reqs[0].get("git"), reqs[0].get("rev"), reqs[0].get("subDir")) != pins["mathlib"]:
        raise RuntimeError("Focused Mathlib requirement differs")
    return packages


def check_workspace(path: Path) -> None:
    error = _validate_lake_workspace_integrity(path)
    if error:
        raise RuntimeError(error)
    override = path / ".lake/package-overrides.json"
    if override.exists() or override.is_symlink():
        raise RuntimeError(f"Unrecorded Lake package override: {override}")


def check_dependency_directory(path: Path) -> None:
    # Check the lexical path before resolving it; executable symlinks are unrelated.
    for part in (path, *path.parents):
        if part.is_symlink():
            raise RuntimeError(f"Dependency directory uses a symlink: {part}")


def git_output(path: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "--no-optional-locks", "-C", str(path), *args], text=True).strip()


def dependency_locations(packages: list[dict], directory: Path,
                         *, require_all: bool) -> list[dict]:
    check_dependency_directory(directory)
    entries = []
    for package in packages:
        path = directory / package["name"]
        if not path.exists() and not path.is_symlink() and not require_all:
            continue  # Native Lake may materialize a missing pinned checkout.
        if not path.is_dir() or path.is_symlink():
            raise RuntimeError(f"Dependency must be an existing ordinary directory: {path}")
        check_workspace(path)
        if Path(git_output(path, "rev-parse", "--show-toplevel")).resolve() != path.resolve():
            raise RuntimeError(f"Dependency is not its own Git checkout: {path}")
        if git_output(path, "rev-parse", "HEAD") != package["rev"]:
            raise RuntimeError(f"Dependency revision mismatch: {package['name']}")
        if git_output(path, "status", "--porcelain", "--untracked-files=no"):
            raise RuntimeError(f"Dependency has tracked source changes: {package['name']}")
        untracked = git_output(path, "ls-files", "--others", "--exclude-standard", "-z")
        for name in untracked.split("\0"):
            rel = Path(name)
            if name and not {".lake", "artifacts"}.intersection(rel.parts):
                if rel.suffix == ".lean" or rel.name in CONFIG_NAMES:
                    raise RuntimeError(f"Untracked dependency source/configuration: {path / rel}")
        entries.append({
            "name": package["name"], "scope": package.get("scope", ""),
            "type": "path", "dir": str(path.resolve()),
            "inherited": package["inherited"], "configFile": package["configFile"],
            "manifestFile": package.get("manifestFile", "lake-manifest.json"),
        })
    return entries


def capture(command: list[str], lock: BuildLock, env: dict[str, str]) -> str:
    """Capture a metadata probe without releasing the lock on interruption."""
    proc = subprocess.Popen(
        command, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, start_new_session=(os.name == "posix"),
        pass_fds=(lock.fileno(),))
    try:
        out, err = proc.communicate()
    except BaseException:
        _interrupt_child_and_wait(proc)
        raise
    if proc.returncode:
        # `lake env` includes optional cache credentials: never echo that output.
        raise RuntimeError(f"Metadata probe failed ({proc.returncode}): {shlex.join(command)}")
    return out.strip()


def runtime_identity(lake: str, lock: BuildLock, env: dict[str, str], probe: Path) -> dict:
    toolchain = (PROJECT / "lean-toolchain").read_text().strip()
    match = re.fullmatch(r"leanprover/lean4:v(\d+\.\d+\.\d+(?:-[\w.]+)?)", toolchain)
    if not match:
        raise RuntimeError(f"Unsupported release toolchain specification: {toolchain}")
    expected = match.group(1)
    lake_version = capture([lake, "--version"], lock, env)
    if f"(Lean version {expected})" not in lake_version:
        raise RuntimeError(f"Selected Lake has the wrong Lean version: {lake_version}")
    # This native command checks the actual Lean/Lake Git revisions agree.
    capture([lake, "self-check"], lock, env)
    settings = dict(line.split("=", 1) for line in
                    capture([lake, "-d", str(probe), "env"], lock, env).splitlines()
                    if "=" in line)
    if not all(settings.get(k) for k in ("LEAN", "LAKE", "LEAN_SYSROOT")):
        raise RuntimeError("Lake did not report its actual Lean/Lake installation")
    lean = Path(settings["LEAN"]).resolve()
    actual_lake = Path(settings["LAKE"]).resolve()
    prefix = Path(settings["LEAN_SYSROOT"]).resolve()
    if lean != (prefix / "bin/lean").resolve() or actual_lake != (prefix / "bin/lake").resolve():
        raise RuntimeError("Selected Lean and Lake do not belong to the same runtime")
    lean_version = capture([str(lean), "--version"], lock, env)
    found = re.search(r"\bversion ([^,\s)]+)", lean_version)
    if found is None or found.group(1) != expected:
        raise RuntimeError(f"Selected Lean version differs: {lean_version}")
    if Path(capture([str(lean), "--print-prefix"], lock, env)).resolve() != prefix:
        raise RuntimeError("Lean's actual prefix differs from Lake's installation")
    return {
        "requested_lake": lake, "lake": str(actual_lake), "lean": str(lean),
        "toolchain": toolchain, "lake_version": lake_version, "lean_version": lean_version,
        "lake_sha256": hashlib.sha256(actual_lake.read_bytes()).hexdigest(),
        "lean_sha256": hashlib.sha256(lean.read_bytes()).hexdigest(),
    }


def source_snapshot(extra_sources: list[Path], dependencies: list[dict]) -> dict[str, str]:
    """Hash canonical owners, repository imports, and verification controls."""
    pending = [ROOT / "lean" / (m.replace(".", "/") + ".lean") for m in TARGETS]
    pending.extend(extra_sources)
    paths: set[Path] = set()
    while pending:
        path = pending.pop().resolve()
        if path in paths:
            continue
        if not path.is_relative_to(ROOT / "lean") or not path.is_file():
            raise RuntimeError(f"Expected canonical Lean source: {path}")
        paths.add(path)
        source = _strip_lean_comments_and_strings(path.read_text())
        for line in IMPORTS.findall(source):
            for module in line.split():
                imported = ROOT / "lean" / (module.replace(".", "/") + ".lean")
                if imported.is_file():
                    pending.append(imported)
                elif module.startswith(("InfoGeometry.", "DAG.")):
                    raise RuntimeError(f"Unresolved repository import in {path}: {module}")
    for directory in (ROOT, PROJECT):
        paths.update(directory / name for name in CONFIG_NAMES if (directory / name).is_file())
    paths.update(PROJECT / name for name in ("check.py", "audit.py"))
    paths.update(ROOT / name for name in (
        "tools/build_lock.py", "tools/infra/build.py", "tools/pathing.py",
        "tools/infra/opengauss_screener.py", ".github/workflows/triality-cotangent.yml"))
    result = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
              for path in sorted(paths)}
    for dependency in dependencies:
        directory = Path(dependency["dir"])
        for name in CONFIG_NAMES:
            path = directory / name
            if path.is_file():
                result[f"dependencies/{dependency['name']}/{name}"] = hashlib.sha256(
                    path.read_bytes()).hexdigest()
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dependency-root", type=Path)
    parser.add_argument("--no-wait", action="store_true")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("lake_args", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    lake_args = args.lake_args or ["build"]
    if lake_args[0] == "--":
        lake_args = lake_args[1:] or ["build"]
    check_pins()  # Fast preflight; repeated after a possibly long lock wait.
    for directory in (ROOT, PROJECT):
        check_workspace(directory)
    selected = shutil.which(args.lake)
    if selected is None:
        raise RuntimeError(f"Lake executable not found: {args.lake}")
    # Keep the shim basename: resolving ~/.elan/bin/lake can select `elan` instead.
    lake = str(Path(selected).absolute())
    env = dict(os.environ)
    dependency_root = (args.dependency_root or ROOT / ".lake/packages").absolute()
    print("[triality-cotangent] requesting shared build lock", flush=True)
    lock = acquire_build_lock(None, f"triality-cotangent:{os.getpid()}", block=not args.no_wait)
    process = None
    try:
        print("[triality-cotangent] acquired shared build lock", flush=True)
        packages = check_pins()
        for directory in (ROOT, PROJECT):
            check_workspace(directory)
        entries = dependency_locations(packages, dependency_root,
                                       require_all=args.dependency_root is not None)
        extra_sources = []
        if lake_args[0] == "build":
            extra_sources = [ROOT / "lean" / (m.replace(".", "/") + ".lean")
                             for m in lake_args[1:] if m.startswith(("InfoGeometry.", "DAG."))]
        elif lake_args[:2] == ["env", "lean"]:
            extra_sources = [Path(p).absolute() for p in lake_args[2:] if p.endswith(".lean")]
        before = source_snapshot(extra_sources, entries)
        print("[triality-cotangent] input snapshot " + json.dumps({
            "files": len(before),
            "sha256": hashlib.sha256(json.dumps(before, sort_keys=True).encode()).hexdigest(),
        }), flush=True)
        with tempfile.TemporaryDirectory(prefix="triality-package-locations-") as temp:
            probe = Path(temp) / "runtime"
            probe.mkdir()
            runtime = runtime_identity(lake, lock, env, probe)
            print("[triality-cotangent] runtime " + json.dumps(runtime, sort_keys=True), flush=True)
            command = [lake]
            if args.dependency_root is not None:
                override = Path(temp) / "locations.json"
                override.write_text(json.dumps({"version": "1.2.0", "packages": entries}))
                command.extend(["--packages", str(override)])
            command.extend(["-d", str(PROJECT), *lake_args])
            print("[triality-cotangent] " + shlex.join(command), flush=True)
            process = subprocess.Popen(command, cwd=ROOT, env=env,
                                       start_new_session=(os.name == "posix"),
                                       pass_fds=(lock.fileno(),))
            try:
                result = process.wait()
            except KeyboardInterrupt:
                _interrupt_child_and_wait(process)
                return 130
            print(f"[triality-cotangent] Lake exited with code {result}", flush=True)
            for directory in (ROOT, PROJECT):
                check_workspace(directory)
            # A successful cold-cache command must have materialized all dependencies.
            dependency_locations(packages, dependency_root,
                                 require_all=args.dependency_root is not None or result == 0)
            check_pins()
            after = source_snapshot(extra_sources, entries)
            if after != before:
                changed = sorted(p for p in set(before) | set(after) if before.get(p) != after.get(p))
                raise RuntimeError(f"Source/configuration changed during validation: {changed}")
            if runtime_identity(lake, lock, env, probe) != runtime:
                raise RuntimeError("Selected runtime changed during validation")
            print("[triality-cotangent] source/configuration/runtime stability passed", flush=True)
            return result
    finally:
        if process is not None and process.poll() is None:
            _interrupt_child_and_wait(process)
        lock.release()
        print("[triality-cotangent] released shared build lock", flush=True)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        raise SystemExit(130)
    except (RuntimeError, OSError, subprocess.CalledProcessError, BuildLockBusyError) as error:
        print(f"[triality-cotangent] {error}", file=sys.stderr)
        raise SystemExit(2)
