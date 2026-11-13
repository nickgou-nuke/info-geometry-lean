#!/usr/bin/env python3
"""Compile the exact selected source closure and audit every owned declaration.

This is a focused compiler surface. Root Lake and quality gates remain separate.
The maintained closure resolver and native owned-declaration auditor are reused.
"""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.quality.check_reviewed_prs import closure, run
from tools.quality.reviewed_audit_source import audit_source, parse_audit_output

TARGETS = [
    "InfoGeometry.Clifford.Cl11GradedAdjoint",
    "InfoGeometry.Clifford.GradedTensorCutRank",
    "InfoGeometry.Clifford.Cl11UntwistCutRank",
    "InfoGeometry.Clifford.Cl11GradedProjectorDefects",
    "InfoGeometry.LinearAlgebra.FiniteRealAnticommutation",
    "InfoGeometry.Clifford.GradedUnrollingCounterexamples",
]


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--mathlib-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    mathlib, output = args.mathlib_root.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    state = {"status": "pending", "targets": TARGETS, "modules": [],
             "scope": "exact source closure; root gates reported separately",
             "axiom_audit_passed": False}
    try:
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        pin = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
        toolchain = (ROOT / "lean-toolchain").read_text().strip()
        state.update(revision=run(["git", "rev-parse", "HEAD"], ROOT).strip(),
                     tree=run(["git", "rev-parse", "HEAD^{tree}"], ROOT).strip(),
                     mathlib=pin, toolchain=toolchain)
        if run(["git", "rev-parse", "HEAD"], mathlib).strip() != pin:
            raise RuntimeError("Mathlib revision mismatch")
        if (mathlib / "lean-toolchain").read_text().strip() != toolchain:
            raise RuntimeError("Toolchain mismatch")
        ordered, dependencies, native = closure(ROOT, TARGETS)
        source, library = output / "src", output / "lib"
        source.mkdir()
        library.mkdir()
        (source / "lean-toolchain").write_text(toolchain + "\n")
        hashes = {}
        for module in ordered:
            relative = Path(module.replace(".", "/") + ".lean")
            data = (ROOT / "lean" / relative).read_bytes()
            dest = source / relative
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
            hashes[module] = hashlib.sha256(data).hexdigest()
        state["source_sha256"] = hashes
        with open("/tmp/info-geometry-build.lock", "a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            pass_fds = (lock.fileno(),)
            active = run(["ps", "-eo", "comm="], ROOT, pass_fds=pass_fds).splitlines()
            if any(name.strip() in {"lean", "lake", "leanc"} for name in active):
                raise RuntimeError("Another Lean/Lake compiler is active")
            (output / "cache.log").write_text(run(
                ["lake", "exe", "cache", "get", *sorted(native)], mathlib,
                pass_fds=pass_fds))
            env = os.environ.copy()
            path = run(["lake", "env", "printenv", "LEAN_PATH"], mathlib,
                       pass_fds=pass_fds).strip()
            search = [str((mathlib / p).resolve()) if not Path(p).is_absolute() else p
                      for p in path.split(os.pathsep) if p]
            env["LEAN_PATH"] = os.pathsep.join([str(library), *search])
            (output / "lean-version.txt").write_text(
                run(["lean", "--version"], source, env, pass_fds=pass_fds))
            failed = set()
            for module in ordered:
                blocked = [dep for dep in dependencies[module] if dep in failed]
                if blocked:
                    failed.add(module)
                    state["modules"].append(
                        {"module": module, "status": "blocked", "dependencies": blocked})
                    print("BLOCKED", module, blocked, flush=True)
                    continue
                relative = Path(module.replace(".", "/"))
                olean = (library / relative).with_suffix(".olean")
                olean.parent.mkdir(parents=True, exist_ok=True)
                result = subprocess.run(
                    ["lean", "-o", str(olean), str((source / relative).with_suffix(".lean"))],
                    cwd=source, env=env, text=True, stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT, pass_fds=pass_fds)
                (output / (module + ".log")).write_text(result.stdout)
                state["modules"].append({"module": module, "returncode": result.returncode})
                print("CHECK", module, result.returncode, flush=True)
                print(result.stdout, flush=True)
                if result.returncode:
                    failed.add(module)
            if failed:
                state["failed_modules"] = sorted(failed)
                raise RuntimeError("Compilation failed; no declaration audit performed")
            audit = source / "GradedCliffordStarRankAudit.lean"
            audit.write_text(audit_source(TARGETS))
            evidence = run(["lean", str(audit)], source, env, pass_fds=pass_fds)
            (output / "audit.log").write_text(evidence)
            state["declarations_by_owner"] = parse_audit_output(evidence, TARGETS)
            state.update(status="passed", axiom_audit_passed=True)
            print(evidence, flush=True)
    except Exception as error:
        state.update(status="failed", error=str(error))
        raise
    finally:
        (output / "status.json").write_text(json.dumps(state, indent=2) + "\n")


if __name__ == "__main__":
    main()
