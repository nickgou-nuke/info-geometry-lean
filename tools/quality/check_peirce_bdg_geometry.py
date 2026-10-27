#!/usr/bin/env python3
"""Compile and audit the exact Peirce/BdG/BKM operator-geometry source closure.

This is a selected-module kernel check, not a root Lake build. Every repository
module in the import closure is compiled from copied, hashed source. No existing
repository olean is trusted. Mathlib revision and toolchain must match the pins.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.build_lock import acquire_build_lock
from tools.quality.check_reviewed_prs import closure
from tools.quality.reviewed_audit_source import audit_source, parse_audit_output

TARGETS = [
    "InfoGeometry.Algebra.MatrixNoncommutativity",
    "InfoGeometry.Core.IdempotentTangent",
    "InfoGeometry.Thermo.OnsagerTwoOperatorForm",
    "InfoGeometry.Physics.BdGOperatorCalculus",
    "InfoGeometry.OperatorAlgebra.ChiralBlockSpectralGap",
    "InfoGeometry.OperatorAlgebra.BdGOperatorGeometryTests",
    "InfoGeometry.OperatorAlgebra.PartnerGeneralizedEigenspaces",
    "InfoGeometry.OperatorAlgebra.PartnerGeneralizedEigenspacesTests",
    "InfoGeometry.OperatorAlgebra.PeirceCompressionCurvature",
    "InfoGeometry.OperatorAlgebra.PeirceProjectedConnection",
    "InfoGeometry.OperatorAlgebra.PeirceCompressedGramPositivity",
    "InfoGeometry.OperatorAlgebra.BdGPeirceCurvature",
    "InfoGeometry.Canonical.CenteredBKMCommutatorGeometry",
]


def run(command, cwd, env=None, log=None, pass_fds=()):
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            pass_fds=pass_fds)
    if log is not None:
        log.write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f"Command failed ({result.returncode}): {command!r}\n"
                           + (f"See {log}" if log else result.stdout))
    return result.stdout


def compiler_preflight():
    processes = subprocess.check_output(["ps", "-eo", "pid=,comm="], text=True)
    active = [line.strip() for line in processes.splitlines()
              if line.split()[-1:] and line.split()[-1] in
              {"lean", "lake", "leanc", "clang", "gcc", "pytest"}]
    if active:
        raise RuntimeError("Concurrent compiler/test task: " + ", ".join(active))


def main(*, targets=None, label="peirce-bdg-geometry",
         audit_filename="PeirceBdGGeometryAudit.lean", description=None):
    targets = TARGETS if targets is None else targets
    parser = argparse.ArgumentParser(description or __doc__)
    parser.add_argument("--mathlib-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True,
                        help="A new directory; verification never reuses project oleans")
    parser.add_argument("--fetch-cache", action="store_true",
                        help="Fetch only the required pinned Mathlib import closure")
    args = parser.parse_args()
    mathlib, output = args.mathlib_root.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    state = {"status": "pending", "targets": targets,
             "scope": "exact repository source closure; selected-owner native axiom audit",
             "modules": [], "axiom_audit_passed": False}
    try:
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        pin = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
        toolchain = (ROOT / "lean-toolchain").read_text().strip()
        state.update(revision=run(["git", "rev-parse", "HEAD"], ROOT).strip(),
                     mathlib=pin, toolchain=toolchain)
        if run(["git", "rev-parse", "HEAD"], mathlib).strip() != pin:
            raise RuntimeError("Mathlib revision mismatch")
        if (mathlib / "lean-toolchain").read_text().strip() != toolchain:
            raise RuntimeError("Toolchain mismatch")
        run(["git", "diff", "--exit-code", "HEAD", "--", "Mathlib", "Mathlib.lean",
             "lakefile.lean", "lake-manifest.json", "lean-toolchain"], mathlib)
        ordered, dependencies, native = closure(ROOT, targets)
        state["dependencies"] = dependencies
        state["source_sha256"] = {}
        source, lib, logs = output / "src", output / "lib", output / "logs"
        for path in (source, lib, logs):
            path.mkdir()
        (source / "lean-toolchain").write_text(toolchain + "\n")
        for module in ordered:
            relative = Path(module.replace(".", "/") + ".lean")
            data = (ROOT / "lean" / relative).read_bytes()
            destination = source / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
            state["source_sha256"][module] = hashlib.sha256(data).hexdigest()
        # The selected graph uses ordinary imports. Fail closed if the source
        # parser would otherwise miss a differently spelled import command.
        for module in ordered:
            text = (source / (module.replace(".", "/") + ".lean")).read_text()
            for line in text.splitlines():
                stripped = line.lstrip()
                if ((stripped.startswith("import ") and not line.startswith("import "))
                        or stripped.startswith(("public import ", "private import "))):
                    raise RuntimeError("Unsupported import syntax in " + module)
        compiler_preflight()
        lock = acquire_build_lock(None, label + ":" + str(os.getpid()), block=False)
        try:
            compiler_preflight()
            fds = (lock.fileno(),)
            clean_env = os.environ.copy()
            clean_env.pop("LEAN_PATH", None)
            clean_env.pop("LEAN_SRC_PATH", None)
            if args.fetch_cache:
                run(["lake", "exe", "cache", "get", *sorted(native)],
                    mathlib, clean_env, log=logs / "mathlib-cache.log", pass_fds=fds)
            search = run(["lake", "env", "printenv", "LEAN_PATH"], mathlib,
                         clean_env, pass_fds=fds).strip().split(os.pathsep)
            search = [str((mathlib / p).resolve()) if not Path(p).is_absolute() else p
                      for p in search if p]
            # Standard Lean modules are found by the pinned executable itself.
            # Only pinned Mathlib and its own dependencies enter LEAN_PATH.
            search = [p for p in search if Path(p).resolve().is_relative_to(mathlib)]
            if not search:
                raise RuntimeError("No pinned Mathlib module paths found")
            env = clean_env.copy()
            env["LEAN_PATH"] = os.pathsep.join([str(lib), *search])
            state["lean_path"] = env["LEAN_PATH"]
            version = run(["lean", "--version"], source, env, pass_fds=fds)
            (output / "lean-version.txt").write_text(version)
            expected = toolchain.rsplit(":v", 1)[-1]
            if f"version {expected}," not in version:
                raise RuntimeError("Active Lean executable differs from the toolchain pin")
            for module in ordered:
                relative = Path(module.replace(".", "/"))
                olean = (lib / relative).with_suffix(".olean")
                olean.parent.mkdir(parents=True, exist_ok=True)
                log = logs / (module + ".log")
                run(["lean", "-o", str(olean), str((source / relative).with_suffix(".lean"))],
                    source, env, log, fds)
                warnings = log.read_text().count("warning:")
                state["modules"].append({"module": module, "returncode": 0,
                                         "warnings": warnings})
                print(f"CHECK {module}: passed ({warnings} warnings)", flush=True)
            audit = source / audit_filename
            audit.write_text(audit_source(targets))
            evidence = run(["lean", str(audit)], source, env, logs / "audit.log", fds)
            state["declaration_counts"] = parse_audit_output(evidence, targets)
            state["axioms"] = next(line.removeprefix("AUDIT_AXIOMS: ")
                for line in evidence.splitlines() if line.startswith("AUDIT_AXIOMS: "))
            for module, digest in state["source_sha256"].items():
                path = ROOT / "lean" / (module.replace(".", "/") + ".lean")
                if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                    raise RuntimeError("Source changed during verification: " + module)
            state.update(status="passed", axiom_audit_passed=True)
            print("AUDIT passed:", sum(state["declaration_counts"].values()),
                  "declarations;", state["axioms"], flush=True)
        finally:
            lock.release()
    except BaseException as error:
        state.update(status="failed", error=str(error))
        raise
    finally:
        (output / "status.json").write_text(json.dumps(state, indent=2) + "\n")


if __name__ == "__main__":
    main()
