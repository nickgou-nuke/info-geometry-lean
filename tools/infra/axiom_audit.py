#!/usr/bin/env python3
"""Lexically scan maintained Lean proof sources for explicit closure debt.

This source audit detects standalone ``sorry``/``admit`` tokens and axiom
declarations after masking comments, strings, and quoted identifiers. It does
not compile Lean or inspect transitive kernel axiom dependencies; use the
compiled ``axiom_check.lean`` runner for that separate audit.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
import argparse
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.quality.audit_constructivity import strip_comments

REPO_ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = REPO_ROOT / "lean"
OUTPUT_REPORT = REPO_ROOT / "artifacts" / "axiom_audit_report.json"


def lean_source_files(include_ignored: bool) -> list[Path]:
    """Return maintained theorem sources; forensic mode selects repository Lean files."""
    if include_ignored:
        excluded = {".git", ".lake", ".lake-packages", "node_modules", "external_refs"}
        return sorted(
            path for path in REPO_ROOT.rglob("*.lean")
            if path.is_file() and not any(part in excluded for part in path.relative_to(REPO_ROOT).parts)
        )

    result = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "--", "lean", "proofs", "lib", "*.lean"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return sorted(
        REPO_ROOT / raw_path
        for raw_path in result.stdout.splitlines()
        if raw_path.endswith(".lean")
        and (REPO_ROOT / raw_path).is_file()
        and (Path(raw_path).parts[0] in {"lean", "proofs", "lib"} or len(Path(raw_path).parts) == 1)
    )


AXIOM_DECL_RE = re.compile(
    r"^\s*(?:(?:@\[[^\n]*?\]\s*)|(?:(?:private|protected|local|unsafe|noncomputable)\s+))*"
    r"(?:axiom|postulate)\b",
    re.MULTILINE,
)
DEBT_TOKEN_RE = {
    token: re.compile(rf"(?<![\w.«.]){token}(?![\w.'»])")
    for token in ("sorry", "admit")
}


def scan_file(filepath: Path) -> dict[str, Any]:
    """Scan one source file. Read/decoding failures are raised to the caller."""
    content = filepath.read_text(encoding="utf-8")
    clean_content = strip_comments(content, strip_strings=True, strip_quoted_identifiers=True)
    lines = clean_content.splitlines()

    sorries = []
    axioms = []
    admits = []

    for idx, line in enumerate(lines, start=1):
        if DEBT_TOKEN_RE["sorry"].search(line):
            sorries.append(idx)
        if AXIOM_DECL_RE.match(line):
            axioms.append(idx)
        if DEBT_TOKEN_RE["admit"].search(line):
            admits.append(idx)

    try:
        rel_path = str(filepath.resolve().relative_to(REPO_ROOT))
    except ValueError:
        rel_path = str(filepath)

    return {
        "file": rel_path,
        "clean": len(sorries) == 0 and len(axioms) == 0 and len(admits) == 0,
        "sorry_lines": sorries,
        "axiom_lines": axioms,
        "admit_lines": admits,
        "total_gaps": len(sorries) + len(axioms) + len(admits),
    }


def scan_files(filepaths: list[Path]) -> tuple[list[dict[str, Any]], list[dict[str, str]]]:
    results: list[dict[str, Any]] = []
    failures: list[dict[str, str]] = []
    for filepath in filepaths:
        try:
            results.append(scan_file(filepath))
        except (OSError, UnicodeError) as exc:
            failures.append({"file": str(filepath), "error": str(exc)})
    return results, failures


def run_lean_check(filepath: Path) -> dict[str, Any]:
    try:
        rel_path = str(filepath.resolve().relative_to(REPO_ROOT))
    except ValueError:
        rel_path = str(filepath)
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
        lean_files = [p.resolve() for p in args.files if p.suffix == ".lean"]
    else:
        try:
            lean_files = lean_source_files(args.include_ignored)
        except (OSError, subprocess.CalledProcessError) as exc:
            print(f"Unable to select Lean sources: {exc}", file=sys.stderr)
            return 2

    results, read_failures = scan_files(lean_files)
    clean_count = 0
    debt_count = 0
    total_sorries = 0

    for info in results:
        if info["clean"]:
            clean_count += 1
        else:
            debt_count += 1
            total_sorries += info["total_gaps"]

    OUTPUT_REPORT.parent.mkdir(parents=True, exist_ok=True)
    report = {
        "timestamp": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "include_ignored": args.include_ignored,
        "selection_scope": "forensic_repository" if args.include_ignored else "maintained_lean_proof_sources",
        "source_roots": ["repository Lean files except excluded external/cache directories"] if args.include_ignored else ["lean/", "proofs/", "lib/", "<repo-root>/*.lean"],
        "total_files": len(lean_files),
        "files_read": len(results),
        "read_failures": read_failures,
        "coverage_complete": len(results) == len(lean_files) and not read_failures and bool(lean_files),
        "clean_files": clean_count,
        "debt_files": debt_count,
        "total_open_gaps": total_sorries,
        "files": results,
    }

    try:
        OUTPUT_REPORT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    except OSError as exc:
        print(f"Unable to write audit report {OUTPUT_REPORT}: {exc}", file=sys.stderr)
        return 2
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

    if not lean_files or read_failures:
        print("❌ Axiom & Debt Audit failed: source selection or read coverage is incomplete.", file=sys.stderr)
        return 2
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
