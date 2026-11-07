#!/usr/bin/env python3
"""Offline structural checks for repository hygiene (the alint-style layer)."""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
REQUIRED = ("AGENTS.md", "lean-toolchain", "lake-manifest.json", ".githooks/pre-push", "scripts/quality/post_build_gate.sh", "scripts/lint/required/module_doc_lint.py", "scripts/lint/required/theorem_lint.py", "tools/qms/__init__.py", "tools/qms/intent_envelope.py", "tools/qms/roles.py", "tools/qms/gates.py", "tools/qms/audit_report.py", "tools/qms/qa_record.py", "tools/qms/capa.py", "tools/qms/qms_runner.py", "tools/qms/run_qms.py")
STRUCTURAL_EXEMPTIONS = ROOT / "scripts/lint/exemptions/structural.txt"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    errors: list[str] = []
    for rel in REQUIRED:
        if not (ROOT / rel).is_file():
            errors.append(f"required file missing: {rel}")
    lakefile_lean = ROOT / "lakefile.lean"
    lakefile_toml = ROOT / "lakefile.toml"
    if not lakefile_lean.is_file() and not lakefile_toml.is_file():
        errors.append("no root Lake configuration found (expected lakefile.lean or lakefile.toml)")
    if lakefile_toml.is_file():
        try:
            tomllib.loads(lakefile_toml.read_text(encoding="utf-8"))
        except (OSError, tomllib.TOMLDecodeError) as exc:
            errors.append(f"invalid lakefile.toml: {exc}")
    if not (ROOT / "src").is_dir() and not (ROOT / "lean").is_dir():
        errors.append("no Lean source root found (expected src/ or lean/)")
    for rel in ("lake-manifest.json",):
        try:
            json.loads((ROOT / rel).read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            errors.append(f"invalid {rel}: {exc}")
    workflows = ROOT / ".github/workflows"
    if not workflows.is_dir() or not any(workflows.glob("*.yml")) and not any(workflows.glob("*.yaml")):
        errors.append("no GitHub Actions workflow files found")
    tracked = subprocess.run(
        ["git", "ls-files", "--cached", "--", "**/lake-manifest.json", "lake-manifest.json"],
        cwd=ROOT, text=True, capture_output=True, check=True,
    ).stdout.splitlines()
    for rel in sorted(set(tracked)):
        path = ROOT / rel
        sibling_toolchain = path.with_name("lean-toolchain")
        if not sibling_toolchain.is_file():
            errors.append(f"manifest has no sibling toolchain pin: {rel}")
    for path in (ROOT / "scripts").rglob("*.sh"):
        if any(part in {".git", "__pycache__"} for part in path.parts):
            continue
        if path.stat().st_mode & 0o111 and not path.read_text(encoding="utf-8", errors="replace").startswith("#!"):
            errors.append(f"executable shell script has no shebang: {path.relative_to(ROOT)}")
    allowed_floating = {
        parts[1]
        for line in STRUCTURAL_EXEMPTIONS.read_text(encoding="utf-8").splitlines()
        if (parts := line.split()) and len(parts) == 2 and parts[0] == "floating-action"
    }
    for path in (ROOT / ".github/workflows").glob("*.y*ml"):
        text = path.read_text(encoding="utf-8", errors="replace")
        if re.search(r"uses:\s+[^\s@]+@main\b", text):
            rel = path.relative_to(ROOT).as_posix()
            if rel not in allowed_floating:
                errors.append(f"workflow uses a floating @main action reference: {rel}")
            else:
                print(f"reviewed structural exception: floating action reference in {rel}")
    if args.json:
        print(json.dumps({"ok": not errors, "errors": errors}, indent=2))
    elif errors:
        print("\n".join(f"ERROR: {e}" for e in errors), file=sys.stderr)
    else:
        print("repository structure lint: passed")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
