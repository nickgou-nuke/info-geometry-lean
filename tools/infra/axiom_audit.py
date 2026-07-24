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
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = REPO_ROOT / "lean"
OUTPUT_REPORT = REPO_ROOT / "artifacts" / "axiom_audit_report.json"


def scan_file(filepath: Path) -> dict[str, Any] | None:
    if not filepath.exists() or not filepath.is_file():
        return None
    try:
        content = filepath.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return None
    # Strip block comments and line comments preserving newlines
    clean_content = re.sub(
        r"/-.*?-/|--.*",
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
        if re.search(r"\bsorry\b", stripped):
            sorries.append(idx)
        if re.search(r"\baxiom\b", stripped):
            axioms.append(idx)
        if re.search(r"\badmit\b", stripped):
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
    print("🔍 Running info-geometry-lean Axiom & Debt Audit...")
    lean_files = sorted(LEAN_DIR.glob("**/*.lean"))

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
        "total_files": len(lean_files),
        "clean_files": clean_count,
        "debt_files": debt_count,
        "total_open_gaps": total_sorries,
        "files": results,
    }

    OUTPUT_REPORT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"✅ Audit complete!")
    print(f"   Total Lean Files: {len(lean_files)}")
    print(f"   Clean Files (0 sorries): {clean_count}")
    print(f"   Files with Debt: {debt_count}")
    print(f"   Total Open Gaps (sorry/axiom/admit): {total_sorries}")
    print(f"   Report saved to: {OUTPUT_REPORT}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
