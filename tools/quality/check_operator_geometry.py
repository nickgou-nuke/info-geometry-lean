#!/usr/bin/env python3
"""Check an exact, isolated source closure using the repository build lock.

This checker reuses an existing Mathlib checkout at the repository pin. It
never updates dependencies, deletes a cache, or substitutes source imports.
--overlay supports review of new source files before integration into a clone.
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
import sys
import tempfile

OWNERS = [
    "InfoGeometry.OperatorAlgebra.MatrixTraceGeometry",
    "InfoGeometry.OperatorAlgebra.PeirceTraceGeometry",
    "InfoGeometry.OperatorAlgebra.PeirceKrausGeometry",
    "InfoGeometry.OperatorAlgebra.OperatorGeometryExamples",
]
IMPORT = re.compile(r"^\s*(?:public\s+)?import\s+([^\n]+)", re.MULTILINE)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--overlay", type=Path)
    parser.add_argument("--mathlib", type=Path)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--work-dir", type=Path)
    parser.add_argument("--target", action="append")
    parser.add_argument("--audit", action="store_true")
    parser.add_argument("--incremental", action="store_true")
    parser.add_argument("--base-ref", help="Require unchanged dependency sources to match this Git ref")
    args = parser.parse_args()
    root = args.repo.resolve()
    overlay = (args.overlay or root).resolve()
    mathlib = (args.mathlib or root / ".lake/packages/mathlib").resolve()
    work = (args.work_dir or Path(tempfile.mkdtemp(prefix="operator-geometry-"))).resolve()
    work.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((root / "lake-manifest.json").read_text())
    pin = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=mathlib, text=True).strip()
    if actual != pin:
        raise RuntimeError(f"Mathlib checkout {actual} differs from pin {pin}")
    if subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"],
                               cwd=mathlib, text=True).strip():
        raise RuntimeError("Mathlib has tracked source changes")
    toolchain = (root / "lean-toolchain").read_text().strip()
    package_pins = {}
    for package in json.loads((mathlib / "lake-manifest.json").read_text())["packages"]:
        if package.get("type") != "git":
            raise RuntimeError("Only pinned Git Mathlib dependencies are supported")
        package_dir = mathlib / ".lake/packages" / package["name"]
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"],
                                           cwd=package_dir, text=True).strip()
        if revision != package["rev"]:
            raise RuntimeError("Dependency pin mismatch: " + package["name"])
        if subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"],
                                   cwd=package_dir, text=True).strip():
            raise RuntimeError("Dependency has tracked changes: " + package["name"])
        package_pins[package["name"]] = revision
    paths: dict[str, Path] = {}
    hashes: dict[str, str] = {}
    baseline_blobs: dict[str, str] = {}
    order: list[str] = []
    active: set[str] = set()

    def stage(module: str) -> None:
        if module in active:
            raise RuntimeError(f"Import cycle at {module}")
        if module in paths:
            return
        relative = Path("lean", *module.split(".")).with_suffix(".lean")
        source = overlay / relative
        if not source.is_file():
            source = root / relative
        data = source.read_bytes()
        if args.base_ref and module not in OWNERS:
            expected = subprocess.check_output(["git", "rev-parse", f"{args.base_ref}:{relative}"],
                                               cwd=root, text=True).strip()
            actual_blob = subprocess.check_output(["git", "hash-object", "--stdin"],
                                                  cwd=root, input=data).decode().strip()
            if actual_blob != expected:
                raise RuntimeError("Dependency differs from baseline: " + module)
            baseline_blobs[module] = expected
        paths[module] = source
        hashes[module] = hashlib.sha256(data).hexdigest()
        target = work / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        active.add(module)
        for line in IMPORT.findall(data.decode()):
            for dep in line.split("--", 1)[0].split():
                if dep.startswith(("InfoGeometry.", "DAG.")):
                    stage(dep)
                elif dep.split(".")[0] not in {"Mathlib", "Lean", "Std", "Init", "Batteries", "Aesop", "Qq"}:
                    raise RuntimeError(f"Unsupported import {dep}; no stub will be generated")
        active.remove(module)
        order.append(module)

    targets = args.target or OWNERS
    for module in targets:
        stage(module)
    audit_source = overlay / "tools/quality/OperatorGeometryDeclarationAudit.lean"
    if args.audit:
        for module in OWNERS:
            stage(module)
        shutil.copyfile(audit_source, work / "lean/OperatorGeometryDeclarationAudit.lean")
    tool_paths = [Path(__file__).resolve()]
    if args.audit:
        tool_paths.append(audit_source)
    tool_hashes = {str(path): digest(path) for path in tool_paths}
    source_record = {
        "toolchain": toolchain, "mathlib": pin, "sources": hashes,
        "compile_order": order, "owners": OWNERS,
        "mathlib_package_pins": package_pins,
        "baseline_ref": args.base_ref, "baseline_git_blobs": baseline_blobs,
        "verification_tool_sha256": tool_hashes,
        "scope": "complete selected source closure, not a whole-repository build",
    }
    (work / "source-manifest.json").write_text(json.dumps(source_record, indent=2) + "\n")
    output = work / "oleans"
    output.mkdir(exist_ok=True)
    package_dirs = [mathlib / ".lake/build/lib/lean"]
    package_dirs += sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean"))
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [output, *package_dirs])))
    sys.path.insert(0, str(root))
    from tools.build_lock import acquire_build_lock

    print(f"Source snapshot: {len(order)} modules at {work}", flush=True)
    print("Waiting for the shared repository build lock", flush=True)
    lock = acquire_build_lock(None, f"operator-geometry:{os.getpid()}", block=True)
    checked_file = work / "checked-hashes.json"
    checked = json.loads(checked_file.read_text()) if args.incremental and checked_file.exists() else {}
    checked_now: dict[str, str] = {}
    try:
        for proc in Path("/proc").iterdir():
            try:
                if proc.name.isdigit() and (proc / "comm").read_text().strip() in {"lean", "lake", "leanc"}:
                    state = (proc / "stat").read_text().split(") ", 1)[1].split()[0]
                    if state != "Z":
                        raise RuntimeError(f"Compiler {proc.name} active after lock acquisition")
            except (FileNotFoundError, PermissionError, ProcessLookupError):
                pass
        version = subprocess.check_output([args.lean, "--version"], cwd=root, env=env,
                                          text=True).strip()
        expected_version = toolchain.split(":v", 1)[1]
        if f"version {expected_version}" not in version:
            raise RuntimeError(f"Compiler mismatch: {version}")
        print(version, flush=True)
        (work / "compiler-version.txt").write_text(version + "\n")
        changed = False
        for module in order:
            relative = Path(*module.split("."))
            out = output / relative.with_suffix(".olean")
            if checked.get(module) != hashes[module] or not out.exists():
                changed = True
            if args.incremental and not changed:
                checked_now[module] = hashes[module]
                continue
            out.parent.mkdir(parents=True, exist_ok=True)
            command = [args.lean, "--root=" + str(work / "lean"), "-o", str(out),
                       str(work / "lean" / relative.with_suffix(".lean"))]
            print("CHECK " + module, flush=True)
            result = subprocess.run(command, cwd=root, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (work / (module + ".log")).write_text(result.stdout)
            print(result.stdout, end="", flush=True)
            if result.returncode:
                raise RuntimeError(f"Lean failed: {module}")
            checked_now[module] = hashes[module]
            checked_file.write_text(json.dumps(checked_now, indent=2) + "\n")
        if args.audit:
            command = [args.lean, "--root=" + str(work / "lean"),
                       str(work / "lean/OperatorGeometryDeclarationAudit.lean")]
            result = subprocess.run(command, cwd=root, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (work / "declaration-audit.jsonl").write_text(result.stdout)
            result.check_returncode()
            summaries = [json.loads(s) for s in result.stdout.splitlines() if s.startswith("{")]
            if not summaries or summaries[-1].get("status") != "PASS":
                raise RuntimeError("Missing passing declaration-audit summary")
            print(json.dumps(summaries[-1]), flush=True)
        for module, source in paths.items():
            if digest(source) != hashes[module]:
                raise RuntimeError(f"Source changed while checking: {module}")
        for path, expected_hash in tool_hashes.items():
            if digest(Path(path)) != expected_hash:
                raise RuntimeError("Verification tool changed during the run: " + path)
        (work / "result.json").write_text(json.dumps({"status": "PASS", **source_record}, indent=2) + "\n")
        print("PASS: exact selected source closure", flush=True)
    finally:
        checked_file.write_text(json.dumps(checked_now, indent=2) + "\n")
        lock.release()


if __name__ == "__main__":
    main()
