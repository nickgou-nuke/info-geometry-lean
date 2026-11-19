#!/usr/bin/env python3
"""Report debt retained in explicitly quarantined Lean artifacts."""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).parent))
from repo_lean_scope_audit import scan  # noqa: E402


def tracked_disabled_files() -> list[Path]:
    result = subprocess.run(
        [
            "git", "ls-files", "--cached", "--others", "--exclude-standard",
            "--", "*.lean.disabled",
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return sorted(
        ROOT / raw for raw in result.stdout.splitlines()
        if (ROOT / raw).is_file()
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fail-on-findings", action="store_true")
    parser.add_argument(
        "files",
        nargs="*",
        help="Optional explicit .lean.disabled files to scan incrementally.",
    )
    args = parser.parse_args()
    if args.files:
        candidates = []
        for raw in args.files:
            p = Path(raw)
            resolved = p.resolve() if p.is_absolute() else (ROOT / p).resolve()
            if resolved.name.endswith(".lean.disabled") and resolved.is_file():
                candidates.append(resolved)
        files = sorted(set(candidates))
    else:
        files = tracked_disabled_files()
    records = []
    for path in files:
        findings = scan(path)
        if findings:
            records.append((path.relative_to(ROOT).as_posix(), findings))
    total = sum(len(findings) for _, findings in records)
    print("Quarantined Lean artifact audit")
    print("================================")
    print(f"quarantine files: {len(files)}")
    print(f"files with debt: {len(records)}")
    print(f"debt findings: {total}")
    for path, findings in records:
        print(f"  {path} ({len(findings)})")
    return int(args.fail_on_findings and bool(records))


if __name__ == "__main__":
    raise SystemExit(main())
