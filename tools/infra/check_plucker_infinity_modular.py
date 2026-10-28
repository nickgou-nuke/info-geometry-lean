#!/usr/bin/env python3
"""Serial source-closure check without loading unrelated root Lake packages.

Use existing dependency checkouts at the exact repository pins. An explicit
diagnostic Architect revision can isolate a pre-existing compatibility error;
that mode reports diagnostic_pass and never certifies the pinned environment.
This script does not download dependencies, change pins, or clean build caches.
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


def imports(source: str) -> list[str]:
    """Read import commands, ignoring nested block comments and strings."""
    out: list[str] = []
    depth, i, in_string = 0, 0, False
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif in_string:
            if source[i] == "\\":
                i += 2
            elif source[i] == '"':
                in_string = False
                i += 1
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth, i = 1, i + 2
        elif pair == "--":
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        elif source[i] == '"':
            in_string = True
            i += 1
        else:
            out.append(source[i])
            i += 1
    result = []
    prefix = r"[ \t]*(?:(?:public|private|meta)[ \t]+)*import\b"
    declaration = prefix + r"[ \t]+(?:all[ \t]+)?([A-Za-z_][A-Za-z0-9_'.]*)[ \t]*"
    for line in "".join(out).splitlines():
        if re.match(prefix, line):
            match = re.fullmatch(declaration, line)
            if match is None:
                raise RuntimeError(f"Unsupported import syntax; refusing an incomplete closure: {line}")
            result.append(match.group(1))
    return result


def git_head(path: Path) -> str:
    return subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"],
                                   text=True).strip()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="*",
                        default=["InfoGeometry.Twistor.PluckerInfinityModularAudit"])
    parser.add_argument("--lean", default=shutil.which("lean"))
    parser.add_argument("--mathlib", type=Path, default=ROOT / ".lake/packages/mathlib")
    parser.add_argument("--lean-architect", type=Path,
                        default=ROOT / ".lake/packages/LeanArchitect")
    parser.add_argument("--diagnostic-architect-revision",
                        help="Explicit alternate checkout revision for diagnosis only; "
                             "the report cannot certify the pinned environment")
    parser.add_argument("--output", type=Path,
                        default=ROOT / ".lake/plucker-infinity-modular")
    args = parser.parse_args()
    if not args.lean:
        parser.error("Lean is not on PATH; pass --lean with the pinned compiler path")
    output = args.output.resolve()
    with acquire_build_lock(None, "plucker-infinity-modular", block=True):
        output.mkdir(parents=True, exist_ok=True)
        report_path = output / "verification.json"
        report_path.write_text(json.dumps({"status": "checking", "targets": args.modules}) + "\n")
        try:
            processes = subprocess.check_output(["ps", "-eo", "comm="], text=True).splitlines()
            if any(p.strip() in {"lean", "lake", "leanc"} for p in processes):
                raise RuntimeError("Another Lean/Lake compiler is active; retry after it finishes")
            return verify(args, output)
        except BaseException as error:
            report_path.write_text(json.dumps({"status": "failed", "targets": args.modules,
                                               "error": str(error)}, indent=2) + "\n")
            raise


def verify(args: argparse.Namespace, output: Path) -> int:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    pins = {p["name"]: p.get("rev") for p in manifest["packages"]}
    dependency_pins = {}
    for name, path in [("mathlib", args.mathlib), ("LeanArchitect", args.lean_architect)]:
        actual = git_head(path)
        expected_revision = (args.diagnostic_architect_revision
                             if name == "LeanArchitect" and args.diagnostic_architect_revision
                             else pins[name])
        if actual != expected_revision:
            raise RuntimeError(f"{name}: expected {expected_revision}, found {actual}")
        if subprocess.run(["git", "-C", str(path), "diff", "--quiet", "HEAD"],
                          check=False).returncode != 0:
            raise RuntimeError(f"{name}: dependency checkout has tracked source changes")
        dependency_pins[name] = actual
    version = subprocess.check_output([args.lean, "--version"], text=True).strip()
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    expected = toolchain.rsplit(":v", 1)[-1]
    if f"version {expected}," not in version:
        raise RuntimeError(f"Compiler mismatch: expected {toolchain}; found {version}")

    libraries = [output, args.mathlib / ".lake/build/lib/lean"]
    libraries += sorted((args.mathlib / ".lake/packages").glob("*/.lake/build/lib/lean"))
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, libraries)))
    # The declared `proofs` library is rooted at the repository root. Native
    # Hestenes owners still import its actual source modules.
    roots = [ROOT / "lean", ROOT / "lib/InfoGeometryCore", ROOT, args.lean_architect]
    owned_namespaces = {"InfoGeometry", "InfoGeometryCore", "DAG", "Architect", "proofs"}
    fingerprint = f"lean-{expected}/mathlib-{pins['mathlib'][:8]}"
    seen: dict[str, str] = {}
    active: set[str] = set()

    def source(module: str):
        for root in roots:
            path = root / (module.replace(".", "/") + ".lean")
            if path.exists():
                return root, path
        return None

    def check(module: str) -> str:
        if module in seen:
            return seen[module]
        if module in active:
            raise RuntimeError(f"Cyclic source import: {module}")
        entry = source(module)
        if entry is None:
            raise RuntimeError(f"No source root for requested module {module}")
        root, path = entry
        active.add(module)
        text = path.read_text()
        deps = []
        for dep in imports(text):
            if source(dep) is not None:
                deps.append(check(dep))
            elif dep.split(".", 1)[0] in owned_namespaces:
                raise RuntimeError(f"Missing owned import source: {module} imports {dep}")
        if path.read_text() != text:
            raise RuntimeError(f"Source changed while checking dependencies: {module}; retry")
        digest = hashlib.sha256((text + "".join(deps) + fingerprint).encode()).hexdigest()
        olean = output / (module.replace(".", "/") + ".olean")
        stamp = olean.with_suffix(".stamp")
        cached = olean.exists() and stamp.exists() and stamp.read_text() == digest
        if not cached or module.endswith("Audit"):
            olean.parent.mkdir(parents=True, exist_ok=True)
            stamp.unlink(missing_ok=True)
            print(f"CHECK {module}", flush=True)
            subprocess.run([args.lean, "--root=" + str(root), "-o", str(olean), str(path)],
                           env=env, check=True)
            stamp.write_text(digest)
        seen[module] = digest
        active.remove(module)
        return digest

    for module in args.modules:
        check(module)
    status = "diagnostic_pass" if args.diagnostic_architect_revision else "pass"
    report = {"status": status, "scope": "selected source import closure; not root Lake build",
              "pinned_environment_verified": not bool(args.diagnostic_architect_revision),
              "base_commit": git_head(ROOT), "toolchain": toolchain, "compiler": version,
              "declared_dependency_pins": {name: pins[name] for name in dependency_pins},
              "checked_dependency_revisions": dependency_pins, "targets": args.modules,
              "module_count": len(seen), "source_closure_digests": seen}
    output.mkdir(parents=True, exist_ok=True)
    (output / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    label = "DIAGNOSTIC PASS" if args.diagnostic_architect_revision else "PASS"
    print(f"{label}: {len(args.modules)} targets; {len(seen)} source modules in closure")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
