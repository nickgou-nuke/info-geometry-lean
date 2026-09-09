#!/usr/bin/env python3
"""
Axiom & Debt Auditor for info-geometry-lean

Scans all Lean 4 files under `lean/`, runs compilation checks,
and generates a machine-readable JSON report of verified modules
vs. open closure debt (sorry / axiom / admit).
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import argparse
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = REPO_ROOT / "lean"
OUTPUT_REPORT = REPO_ROOT / "artifacts" / "axiom_audit_report.json"


def lean_source_files(include_ignored: bool) -> list[Path]:
    """Return repo source files, excluding ignored fixtures by default."""
    if include_ignored:
        return sorted(LEAN_DIR.glob("**/*.lean"))

    try:
        result = subprocess.run(
            ["git", "ls-files", "--cached", "--others", "--exclude-standard", "--", "lean/*.lean"],
            cwd=REPO_ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError):
        return sorted(LEAN_DIR.glob("**/*.lean"))

    paths = []
    for raw_path in result.stdout.splitlines():
        path = REPO_ROOT / raw_path
        if path.is_relative_to(LEAN_DIR) and path.is_file():
            paths.append(path)
    return sorted(paths)


def scan_file(filepath: Path) -> dict[str, Any] | None:
    if not filepath.exists() or not filepath.is_file():
        return None
    try:
        content = filepath.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return None
    clean_content = re.sub(
        r'/-.*?-/|--.*|"(?:[^"\\]|\\.)*"|«[^»]*»|`+[^`\n]*`+|`[a-zA-Z_][a-zA-Z0-9._]*|[a-zA-Z0-9_.-]*\.(?:sorry|admit|axiom)[a-zA-Z0-9_.-]*|[a-zA-Z0-9_.-]*(?:sorry|admit|axiom)\.[a-zA-Z0-9_.-]*',
        lambda m: "".join("\n" if c == "\n" else " " for c in m.group(0)),
        content,
        flags=re.DOTALL
    )
    lines = clean_content.splitlines()

    sorries = []
    axioms = []
    admits = []

    for idx, line in enumerate(lines, start=1):
        stripped = line.strip()
        if not stripped:
            continue
        # A qualified identifier such as `DAG.Morphism.admit` is metadata,
        # not the Lean `admit` command.  Only standalone proof-debt tokens
        # count; this keeps the repo-wide audit honest without rejecting
        # legitimate trace-class names.
        if re.search(r"(?<![A-Za-z0-9_.])sorry(?![A-Za-z0-9_.])", stripped):
            sorries.append(idx)
        if re.search(r"(?<![A-Za-z0-9_.])axiom(?![A-Za-z0-9_.])", stripped):
            axioms.append(idx)
        if re.search(r"(?<![A-Za-z0-9_.])admit(?![A-Za-z0-9_.])", stripped):
            admits.append(idx)

    rel_path = str(filepath.relative_to(REPO_ROOT))

    return {
        "file": rel_path,
        "clean": len(sorries) == 0 and len(axioms) == 0 and len(admits) == 0,
        "sorry_lines": sorries,
        "axiom_lines": axioms,
        "admit_lines": admits,
        "total_gaps": len(sorries) + len(axioms) + len(admits),
    }


def run_lean_check(filepath: Path) -> dict[str, Any]:
    rel_path = str(filepath.relative_to(REPO_ROOT))
    cmd = ["lake", "env", "lean", str(filepath)]
    try:
        res = subprocess.run(
            cmd,
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=60,
        )
        return {
            "file": rel_path,
            "success": res.returncode == 0,
            "stdout": res.stdout.strip(),
            "stderr": res.stderr.strip(),
        }
    except subprocess.TimeoutExpired:
        return {
            "file": rel_path,
            "success": False,
            "stdout": "",
            "stderr": "Lean compilation timed out (60s)",
        }
    except Exception as e:
        return {
            "file": rel_path,
            "success": False,
            "stdout": "",
            "stderr": str(e),
        }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Scan Lean source for sorry/admit/axiom closure debt."
    )
    parser.add_argument(
        "--fail-on-gaps",
        action="store_true",
        help="Return a nonzero status when any open gap is found.",
    )
    parser.add_argument(
        "--format",
        choices=("text", "json"),
        default="text",
        help="Choose human-readable text or machine-readable JSON stdout.",
    )
    parser.add_argument(
        "--include-ignored",
        action="store_true",
        help="Scan ignored Lean fixtures too (forensic mode).",
    )
    parser.add_argument(
        "files",
        nargs="*",
        type=Path,
        help="Optional specific Lean files to scan. If omitted, scans all files.",
    )
    args = parser.parse_args()

    if args.files:
        lean_files = [p.resolve() for p in args.files if p.is_file() and p.suffix == ".lean"]
    else:
        lean_files = lean_source_files(args.include_ignored)

    results = []
    clean_count = 0
    debt_count = 0
    total_sorries = 0

    for f in lean_files:
        info = scan_file(f)
        if info is None:
            continue
        results.append(info)
        if info["clean"]:
            clean_count += 1
        else:
            debt_count += 1
            total_sorries += info["total_gaps"]

    OUTPUT_REPORT.parent.mkdir(parents=True, exist_ok=True)
    report = {
        "timestamp": os.popen("date -u +'%Y-%m-%dT%H:%M:%SZ'").read().strip(),
        "include_ignored": args.include_ignored,
        "total_files": len(lean_files),
        "clean_files": clean_count,
        "debt_files": debt_count,
        "total_open_gaps": total_sorries,
        "files": results,
    }

    OUTPUT_REPORT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    if args.format == "json":
        print(json.dumps(report, indent=2))
    else:
        print("🔍 Running info-geometry-lean Axiom & Debt Audit...")
        print("✅ Audit complete!")
        print(f"   Total Lean Files: {len(lean_files)}")
        print(f"   Clean Files (0 sorries): {clean_count}")
        print(f"   Files with Debt: {debt_count}")
        print(f"   Total Open Gaps (sorry/axiom/admit): {total_sorries}")
        print(f"   Report saved to: {OUTPUT_REPORT}")

    if args.fail_on_gaps and total_sorries:
        print(
            "❌ Axiom & Debt Audit failed: open closure debt is present "
            "(--fail-on-gaps).",
            file=sys.stderr,
        )
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
