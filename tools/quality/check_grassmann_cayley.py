#!/usr/bin/env python3
"""Compile the exact exterior-geometry source closure and audit every declaration.

Uses the repository's pinned Lean and Mathlib and the shared build lock. It
does not load unrelated root Lake packages, change dependency pins, or clean
caches. Native Mathlib caches are trusted in the ordinary Lean import model.
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

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.build_lock import acquire_build_lock
from tools.infra.opengauss_screener import _strip_lean_comments_and_strings
from tools.quality.reviewed_audit_source import audit_source, parse_audit_output

TARGETS = [
    "InfoGeometry.Projective.ExteriorBladeIncidence",
    "InfoGeometry.OperatorAlgebra.ExteriorOperatorGeometry",
    "InfoGeometry.Projective.ExteriorRegressive",
    "InfoGeometry.OperatorAlgebra.GrassmannCayley",
]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def imports(text: str) -> list[str]:
    stripped = _strip_lean_comments_and_strings(text)
    found = []
    for line in stripped.splitlines():
        if re.match(r"\s*(?:(?:public|private|meta)\s+)*import\b", line):
            match = re.fullmatch(
                r"\s*(?:(?:public|private|meta)\s+)*import\s+([\w.]+)\s*", line)
            if not match:
                raise RuntimeError("Unsupported import syntax: " + line)
            found.append(match.group(1))
    return found


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=shutil.which("lean"))
    parser.add_argument("--mathlib", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not args.lean:
        parser.error("Lean is not on PATH; pass --lean")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    status_path = output / "verification.json"
    report = {"status": "checking", "targets": TARGETS,
              "scope": "full selected source closure; not root Lake build"}
    status_path.write_text(json.dumps(report, indent=2) + "\n")
    try:
        with acquire_build_lock(None, "grassmann-cayley-verification", block=True):
            active = subprocess.check_output(["ps", "-eo", "comm="], text=True).splitlines()
            if any(p.strip() in {"lean", "lake", "leanc", "pytest", "cargo", "rustc"}
                   for p in active):
                raise RuntimeError("Another compiler/test process is active")
            manifest = json.loads((ROOT / "lake-manifest.json").read_text())
            pin = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
            mathlib = args.mathlib.resolve()
            actual = subprocess.check_output(
                ["git", "-C", str(mathlib), "rev-parse", "HEAD"], text=True).strip()
            if actual != pin:
                raise RuntimeError(f"Mathlib pin mismatch: expected {pin}, found {actual}")
            subprocess.run(["git", "-C", str(mathlib), "diff", "--quiet", "HEAD"], check=True)
            toolchain = (ROOT / "lean-toolchain").read_text().strip()
            version = subprocess.check_output([args.lean, "--version"], text=True).strip()
            if f"version {toolchain.rsplit(':v', 1)[-1]}," not in version:
                raise RuntimeError(f"Compiler mismatch: {version}; expected {toolchain}")
            if (mathlib / "lean-toolchain").read_text().strip() != toolchain:
                raise RuntimeError("Mathlib declares a different Lean toolchain")
            report.update(toolchain=toolchain, compiler=version, mathlib=pin,
                          base_commit=subprocess.check_output(
                              ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip())
            libs = [output, mathlib / ".lake/build/lib/lean"]
            libs += sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean"))
            env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, libs)))
            checked, visiting, failed = {}, set(), {}
            def check(module: str) -> None:
                if module in checked:
                    return
                if module in failed:
                    raise RuntimeError("Previously failed dependency: " + module)
                if module in visiting:
                    raise RuntimeError("Cyclic source imports: " + module)
                visiting.add(module)
                try:
                    path = ROOT / "lean" / (module.replace(".", "/") + ".lean")
                    if not path.is_file():
                        raise RuntimeError("Missing source owner: " + module)
                    text = path.read_text()
                    before = sha256(path)
                    for dep in imports(text):
                        if dep.startswith(("InfoGeometry.", "DAG.")):
                            check(dep)
                        elif dep.split(".")[0] not in {
                                "Mathlib", "Lean", "Std", "Init", "Batteries", "Aesop",
                                "Qq", "ProofWidgets", "Plausible", "ImportGraph", "LeanSearchClient"}:
                            raise RuntimeError("Unresolved non-Mathlib dependency: " + dep)
                    if module in TARGETS:
                        code = _strip_lean_comments_and_strings(text)
                        if re.search(r"\b(sorry|admit|axiom|unsafe|partial|native_decide)\b", code):
                            raise RuntimeError("Forbidden proof construct: " + module)
                    olean = output / (module.replace(".", "/") + ".olean")
                    olean.parent.mkdir(parents=True, exist_ok=True)
                    print("CHECK", module, flush=True)
                    result = subprocess.run(
                        [args.lean, "--root=" + str(ROOT / "lean"), "-o", str(olean), str(path)],
                        env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                    print(result.stdout, end="", flush=True)
                    olean.with_suffix(".log").write_text(result.stdout)
                    result.check_returncode()
                    if sha256(path) != before:
                        raise RuntimeError("Source changed during compilation: " + module)
                    checked[module] = before
                except Exception as error:
                    failed[module] = repr(error)
                    raise
                finally:
                    visiting.remove(module)
            failures = {}
            for target in TARGETS:
                try:
                    check(target)
                except Exception as error:
                    failures[target] = repr(error)
            report.update(source_sha256=checked, compilation_failures=failures)
            if failures:
                raise RuntimeError("Target compilation failed: " + ", ".join(failures))
            audit = output / "GrassmannCayleyAudit.lean"
            audit.write_text(audit_source(TARGETS))
            result = subprocess.run([args.lean, "--root=" + str(output), str(audit)],
                                    env=env, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT)
            print(result.stdout, end="", flush=True)
            (output / "axioms.log").write_text(result.stdout)
            result.check_returncode()
            counts = parse_audit_output(result.stdout, TARGETS)
            for module, before in checked.items():
                path = ROOT / "lean" / (module.replace(".", "/") + ".lean")
                if sha256(path) != before:
                    raise RuntimeError("Source changed after compilation: " + module)
            report.update(status="pass", source_sha256=checked,
                          audited_declarations=counts, source_module_count=len(checked),
                          allowed_axioms=["propext", "Classical.choice", "Quot.sound"])
            print("PASS: complete source closure and native declaration axiom audit", flush=True)
    except BaseException as error:
        report.update(status="failed", error=repr(error))
        raise
    finally:
        status_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
