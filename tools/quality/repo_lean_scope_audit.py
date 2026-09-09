#!/usr/bin/env python3
"""Audit every tracked Lean file and separate package truth from forensic debt.

The Lake package has ``lean/`` as its source root.  The repository also keeps
historical recovery, scratch, and fixture Lean files outside that root.  Those
files must be visible to debt audits, but they must not be reported as
kernel-built package theorems.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TOKEN_RE = {
    word: re.compile(rf"(?<![A-Za-z0-9_.]){word}(?![A-Za-z0-9_.])")
    for word in ("sorry", "admit", "axiom")
}
# Keep line comments line-local.  Using ``re.DOTALL`` for the whole expression
# makes ``--`` consume the remainder of a file, silently hiding declarations
# after the first comment (including real `axiom`/`sorry` debt).  Block
# comments are the only alternative that needs DOTALL.
COMMENT_OR_STRING_RE = re.compile(
    r'/-.*?-/|--[^\n]*|"(?:[^"\\]|\\.)*"|«[^»]*»|`+[^`\n]*`+',
    re.DOTALL,
)

FORENSIC_PREFIXES = (
    "archive/",
    "agent_memory_recovery/",
    "agent_memory_recovery_stitched/",
    "agent_writes_recovery_v4/",
    "lean_sandbox/",
    ".spectral-sandbox/",
    "tests/",
    "tools/multisystem/",
)


def tracked_lean_files() -> list[Path]:
    result = subprocess.run(
        [
            "git",
            "ls-files",
            "--cached",
            "--others",
            "--exclude-standard",
            "--",
            "*.lean",
            ":(exclude)archive/upstream_pr_extraction/*",
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return sorted(ROOT / raw for raw in result.stdout.splitlines() if (ROOT / raw).is_file())


def classification(path: Path) -> str:
    rel = path.relative_to(ROOT).as_posix()
    if rel.startswith("lean/"):
        return "lake_package"
    if (
        rel.startswith(FORENSIC_PREFIXES)
        or "/sandbox" in rel.lower()
        or "/" not in rel
    ):
        return "forensic_or_fixture"
    return "unclassified_nonpackage"


def scan(path: Path) -> list[dict[str, object]]:
    text = path.read_text(encoding="utf-8", errors="ignore")
    clean = COMMENT_OR_STRING_RE.sub(
        lambda match: "".join("\n" if c == "\n" else " " for c in match.group(0)),
        text,
    )
    findings: list[dict[str, object]] = []
    for line_no, line in enumerate(clean.splitlines(), start=1):
        for word, pattern in TOKEN_RE.items():
            if pattern.search(line):
                findings.append({"line": line_no, "kind": word})
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--fail-on",
        choices=("authoritative", "tracked", "none"),
        default="authoritative",
        help="Debt threshold for the exit status (default: authoritative Lake package).",
    )
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args()

    tracked_files = tracked_lean_files()
    records = []
    for path in tracked_files:
        findings = scan(path)
        if findings:
            records.append(
                {
                    "file": path.relative_to(ROOT).as_posix(),
                    "classification": classification(path),
                    "findings": findings,
                }
            )

    counts = {"lake_package": 0, "forensic_or_fixture": 0, "unclassified_nonpackage": 0}
    for record in records:
        counts[record["classification"]] += len(record["findings"])

    report = {
        "tracked_lean_files": len(tracked_files),
        "debt_files": len(records),
        "debt_findings": sum(len(record["findings"]) for record in records),
        "finding_counts_by_classification": counts,
        "records": records,
        "fail_on": args.fail_on,
    }

    if args.format == "json":
        print(json.dumps(report, indent=2))
    else:
        print("Tracked Lean scope audit")
        print("=========================")
        print(f"tracked Lean files: {report['tracked_lean_files']}")
        print(f"debt files: {report['debt_files']}")
        print(f"debt findings: {report['debt_findings']}")
        for key, value in counts.items():
            print(f"{key}: {value}")
        for record in records:
            print(f"  {record['file']} [{record['classification']}] ({len(record['findings'])})")

    if args.fail_on == "none":
        return 0
    if args.fail_on == "tracked":
        return int(bool(records))
    return int(counts["lake_package"] > 0)


if __name__ == "__main__":
    sys.exit(main())
