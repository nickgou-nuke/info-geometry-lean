#!/usr/bin/env python3
"""Check the narrow Cuntz/Clifford chain against the unchanged repository pins."""
from __future__ import annotations

import argparse
import fcntl
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

TARGETS = [
    "InfoGeometry.Algebra.RegularBimoduleWeylObstruction",
    "InfoGeometry.Algebra.CuntzMatrixUnitRepresentation",
    "InfoGeometry.Clifford.CuntzSplitClifford22",
    "InfoGeometry.Geometry.AssociativeGaugeConnection",
]


def run(cmd, cwd, env=None):
    result = subprocess.run(cmd, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"{cmd!r}\n{result.stdout}")
    return result.stdout


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--mathlib-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[2]
    mathlib = args.mathlib_root.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((repo / "lake-manifest.json").read_text())
    pinned = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    assert run(["git", "rev-parse", "HEAD"], mathlib).strip() == pinned
    toolchain = (repo / "lean-toolchain").read_text()
    assert (mathlib / "lean-toolchain").read_text() == toolchain
    report = {"mathlib": pinned, "toolchain": toolchain.strip(), "modules": [],
              "scope": "new modules and their complete repository import closure",
              "status": "pending"}
    seen, ordered, native = set(), [], set()

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        path = repo / "lean" / (module.replace(".", "/") + ".lean")
        for line in path.read_text().splitlines():
            if line.startswith("import "):
                for dependency in line[7:].split():
                    if dependency.startswith("InfoGeometry."):
                        visit(dependency)
                    elif dependency.startswith("Mathlib"):
                        native.add(dependency.replace(".", "/") + ".lean")
        ordered.append(module)

    for target in TARGETS:
        visit(target)
    source, lib = output / "src", output / "lib"
    source.mkdir(exist_ok=True)
    lib.mkdir(exist_ok=True)
    (source / "lean-toolchain").write_text(toolchain)
    for module in ordered:
        rel = Path(module.replace(".", "/") + ".lean")
        (source / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(repo / "lean" / rel, source / rel)

    # The same host-wide lock covers cache generation, compilation, and the audit.
    with open("/tmp/info-geometry-build.lock", "a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        active = run(["ps", "-eo", "comm="], repo).splitlines()
        if any(name.strip() in {"lean", "lake", "leanc"} for name in active):
            raise RuntimeError("Another Lean/Lake process is active; no concurrent build started")
        try:
            print("Fetching pinned Mathlib cache", flush=True)
            print(run(["lake", "exe", "cache", "get", *sorted(native)], mathlib), flush=True)
            env = os.environ.copy()
            base_path = run(["lake", "env", "printenv", "LEAN_PATH"], mathlib).strip()
            # Lake may emit relative paths; make them valid from the isolated source root.
            paths = [str((mathlib / p).resolve()) if not Path(p).is_absolute() else p
                     for p in base_path.split(os.pathsep) if p]
            env["LEAN_PATH"] = os.pathsep.join([str(lib), *paths])
            print(run(["lean", "--version"], source, env), flush=True)
            for module in ordered:
                rel = Path(module.replace(".", "/"))
                destination = (lib / rel).with_suffix(".olean")
                destination.parent.mkdir(parents=True, exist_ok=True)
                print(f"Checking {module}", flush=True)
                diagnostics = run(["lean", "-o", str(destination),
                                   str((source / rel).with_suffix(".lean"))], source, env)
                (output / (module + ".log")).write_text(diagnostics)
                report["modules"].append({"module": module, "status": "passed",
                                          "warnings": diagnostics.count("warning:")})
                if diagnostics:
                    print(diagnostics, flush=True)
            declarations = []
            for target in TARGETS:
                text = (source / (target.replace(".", "/") + ".lean")).read_text()
                stack = []
                for line in text.splitlines():
                    if line.startswith("namespace "):
                        stack.append(line.split()[1])
                    elif re.match(r"(?:noncomputable )?section(?:\s|$)", line):
                        stack.append("")
                    elif re.match(r"end(?:\s|$)", line):
                        stack.pop()
                    match = re.match(r"(?:@\[[^]]+\]\s*)?(?:def|theorem|lemma)\s+(\S+)", line)
                    if match:
                        declarations.append(".".join([n for n in stack if n] + [match[1]]))
            audit = source / "AuditCuntzCliffordChain.lean"
            audit.write_text("\n".join([*("import " + m for m in TARGETS),
                                         *("#print axioms " + n for n in declarations)]) + "\n")
            axioms = run(["lean", str(audit)], source, env)
            (output / "axioms.log").write_text(axioms)
            allowed = {"propext", "Classical.choice", "Quot.sound"}
            for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", axioms):
                unexpected = {x.strip() for x in group.split(",") if x.strip()} - allowed
                if unexpected:
                    raise RuntimeError(f"Unexpected axioms: {unexpected}")
            if "sorryAx" in axioms:
                raise RuntimeError("A proof depends on sorryAx")
            report.update(status="passed", audited_declarations=len(declarations))
            print(axioms, flush=True)
        except Exception as error:
            report.update(status="failed", error=str(error))
            raise
        finally:
            (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
