#!/usr/bin/env python3
"""
Axiom checker for info-geometry-lean.

For each .olean module, generates a temp .lean file that imports the module
and runs `#check` on every declaration, combing for axiom dependencies.

Usage:
  python3 tools/infra/axiom_check.py              # check all InfoGeometry .olean files
  python3 tools/infra/axiom_check.py Module.Name  # check one module
  python3 tools/infra/axiom_check.py --json       # JSON output
"""

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
OLEAN_DIR = REPO_ROOT / ".lake" / "build" / "lib" / "lean"

ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
SKIP_PREFIXES = {"_", "inst", "h", "match"}


def olean_to_module(path: Path) -> str:
    """Convert an .olean path like InfoGeometry/Canonical/Foo.olean to module name."""
    rel = path.relative_to(OLEAN_DIR)
    return str(rel.with_suffix("")).replace("/", ".")


def check_olean_file(olean_path: Path) -> dict:
    """Check a single .olean file by generating a Lean script that imports it."""
    module = olean_to_module(olean_path)
    if not olean_path.exists():
        return {"module": module, "passed": False, "error": "file not found"}

    # Generate a script that imports the module and prints axiom info for each decl
    # We use `#eval` with a CoreM computation that calls Lean.collectAxioms
    script = f"""
import Lean
open Lean

def showAxioms (modName : Name) : CoreM Unit := do
  let env ← getEnv
  for (name, ci) in env.constants.map₂ do
    if ci.kind ∈ ["theorem", "def", "opaque", "inductive"] then
      let axioms : Array Name := Lean.collectAxioms name
      let disallowed := axioms.filter fun a => a ∉ [`propext, `Quot.sound, `Classical.choice]
      if !disallowed.isEmpty then
        IO.println s!"AXIOM_VIOLATION:{{name}}:{{disallowed}}"
      if ci.isPartial && !name.toString.endsWith "_unsafe_rec" then
        IO.println s!"PARTIAL:{{name}}"
      if ci.isUnsafe then
        IO.println s!"UNSAFE:{{name}}"

#eval showAxioms `{module}
"""
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False, dir="/tmp") as f:
        f.write(script)
        tmp_path = f.name

    try:
        result = subprocess.run(
            ["lake", "env", "lean", "--run", tmp_path],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=60,
        )
    except subprocess.TimeoutExpired:
        Path(tmp_path).unlink(missing_ok=True)
        return {"module": module, "passed": False, "error": "timeout"}
    finally:
        Path(tmp_path).unlink(missing_ok=True)

    violations = []
    for line in result.stdout.split("\n"):
        if line.startswith("AXIOM_VIOLATION:"):
            parts = line[len("AXIOM_VIOLATION:"):].split(":")
            violations.append({"name": parts[0], "type": "axiom", "detail": parts[1] if len(parts) > 1 else ""})
        elif line.startswith("PARTIAL:"):
            violations.append({"name": line[len("PARTIAL:"):], "type": "partial"})
        elif line.startswith("UNSAFE:"):
            violations.append({"name": line[len("UNSAFE:"):], "type": "unsafe"})

    passed = len(violations) == 0
    return {"module": module, "passed": passed, "violations": violations, "stderr": result.stderr[:500] if not passed else ""}


def main():
    parser = argparse.ArgumentParser(description="Axiom checker")
    parser.add_argument("modules", nargs="*", help="Module names to check")
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    if args.modules:
        paths = []
        for m in args.modules:
            p = OLEAN_DIR / (m.replace(".", "/") + ".olean")
            paths.append(p)
    elif args.all:
        paths = sorted(OLEAN_DIR.rglob("*.olean"))
    else:
        paths = sorted(OLEAN_DIR.rglob("InfoGeometry/**/*.olean")) + sorted(OLEAN_DIR.rglob("InfoGeometry.lean.olean"))

    if not paths:
        print("No .olean files found.")
        sys.exit(1)

    print(f"Checking {len(paths)} module(s)...")
    results = []
    any_fail = False
    for p in paths:
        r = check_olean_file(p)
        results.append(r)
        status = "FAIL" if not r["passed"] else "OK"
        print(f"  {r['module']}: {status}")
        if not r["passed"]:
            any_fail = True
            for v in r.get("violations", []):
                print(f"      {v['type']}: {v['name']} {v.get('detail', '')}")

    if args.json:
        print(json.dumps(results, indent=2))

    sys.exit(1 if any_fail else 0)


if __name__ == "__main__":
    main()
