#!/usr/bin/env python3
"""Check the exact owner closure with the root's Lean/Mathlib pins in isolation.

The root package includes workstation-only submodule URLs. This checker leaves
that package, its manifests, and its dependency cache untouched. It copies the
reachable Lean sources byte-for-byte to a fresh workspace, records their hashes,
and acquires the repository's existing build lock before invoking Lake.
This is a narrow source-closure check, not a repository-wide integration build.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.build_lock import acquire_build_lock  # noqa: E402

TARGET = "InfoGeometry.Krein.TransitionWeakValueAudit"
SOURCE_IMPORT = re.compile(r"^\s*import\s+([^\n]+)", re.MULTILINE)
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def main() -> None:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    if mathlib["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", mathlib["rev"]):
        raise RuntimeError("The repository must have an exact Git Mathlib pin")
    toolchain = (ROOT / "lean-toolchain").read_text()
    work = Path(tempfile.mkdtemp(prefix="weak-value-lean-", dir=os.environ.get("RUNNER_TEMP")))
    # This immutable Mathlib revision advertises 4.28.0 whereas the repository
    # checks sources with 4.28.1. Fetch its official cache in a temporary 4.28.0
    # workspace, then restore the repository pin for every owner-source check.
    # Normal Lean import/version checks remain enabled; incompatibility is fatal.
    cache_toolchain = toolchain
    if (mathlib["rev"] == "8f9d9cff6bd728b17a24e163c9402775d9e6a365"
            and toolchain.strip() == "leanprover/lean4:v4.28.1"):
        cache_toolchain = "leanprover/lean4:v4.28.0\n"
    (work / "lean-toolchain").write_text(cache_toolchain)
    (work / "lakefile.toml").write_text(
        'name = "weak_value_narrow"\n'
        '[[require]]\nname = "mathlib"\n'
        f'git = {json.dumps(mathlib["url"])}\nrev = {json.dumps(mathlib["rev"])}\n'
        '[[lean_lib]]\nname = "InfoGeometry"\nsrcDir = "lean"\n'
    )
    hashes: dict[str, str] = {}
    compile_order: list[str] = []

    def stage(module: str) -> None:
        if module in hashes:
            return
        relative = Path("lean", *module.split(".")).with_suffix(".lean")
        source = ROOT / relative
        if not source.is_file():
            raise FileNotFoundError(f"Missing owner {source}; no replacement will be generated")
        data = source.read_bytes()
        hashes[module] = hashlib.sha256(data).hexdigest()
        target = work / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        for line in SOURCE_IMPORT.findall(data.decode()):
            for dependency in line.split("--", 1)[0].split():
                if dependency.startswith("InfoGeometry."):
                    stage(dependency)
                elif dependency.split(".")[0] not in {"Mathlib", "Lean", "Std", "Init", "Batteries", "Aesop", "Qq"}:
                    raise RuntimeError(f"Unprovisioned dependency {dependency}; refusing to stub it")
        compile_order.append(module)

    stage(TARGET)
    (ROOT / "weak-value-source-hashes.json").write_text(json.dumps({
        "toolchain": toolchain.strip(), "cache_toolchain": cache_toolchain.strip(),
        "mathlib_rev": mathlib["rev"],
        "target": TARGET, "source_sha256": hashes,
        "scope": "byte-identical narrow source closure; not a full root-package build"
    }, indent=2) + "\n")
    print(f"Narrow workspace: {work}\nMathlib: {mathlib['rev']}\nSources: {len(hashes)}", flush=True)
    for executable in ("lean", "lake"):
        if subprocess.run(["pgrep", "-x", executable], stdout=subprocess.DEVNULL).returncode == 0:
            raise RuntimeError(f"Another {executable} process is active; refusing concurrent compilation")
    lock = acquire_build_lock(None, f"weak-value-narrow:{os.getpid()}", block=True)
    try:
        # The temporary package resolves only Mathlib and the dependencies locked
        # by that exact Mathlib commit. The root manifests are never rewritten.
        subprocess.run(["lake", "exe", "cache", "get"], cwd=work, check=True)
        lean_path = subprocess.run(
            ["lake", "env", "printenv", "LEAN_PATH"], cwd=work,
            text=True, stdout=subprocess.PIPE, check=True,
        ).stdout.strip()
        (work / "lean-toolchain").write_text(toolchain)
        subprocess.run(["lean", "--version"], cwd=work, check=True)
        output = work / ".lake/build/lib/lean"
        env = dict(os.environ, LEAN_PATH=str(output) + os.pathsep + lean_path)
        for module in compile_order:
            relative = Path(*module.split("."))
            target = output / relative.with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            print(f"Checking {module} with {toolchain.strip()}", flush=True)
            result = subprocess.run(
                ["lean", "--root=lean", "-o", str(target),
                 str(Path("lean") / relative.with_suffix(".lean"))],
                cwd=work, env=env, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            )
            print(result.stdout, end="", flush=True)
            if module == TARGET:
                (ROOT / "weak-value-axioms.log").write_text(result.stdout)
            result.check_returncode()
        if "sorryAx" in result.stdout:
            raise RuntimeError("The axiom closure contains sorryAx")
        for block in re.findall(r"depends on axioms:\s*\[([^]]*)\]", result.stdout):
            unexpected = {name.strip() for name in block.split(",") if name.strip()} - ALLOWED_AXIOMS
            if unexpected:
                raise RuntimeError(f"Unexpected axioms: {sorted(unexpected)}")
        for module, digest in hashes.items():
            relative = Path("lean", *module.split(".")).with_suffix(".lean")
            if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != digest:
                raise RuntimeError(f"Source changed during verification: {module}")
        subprocess.run(["git", "diff", "--exit-code", "--", "lean-toolchain", "lake-manifest.json", "lakefile.lean"], cwd=ROOT, check=True)
    finally:
        lock.release()
    print("Pinned narrow owner closure and axiom checks passed.", flush=True)


if __name__ == "__main__":
    main()
