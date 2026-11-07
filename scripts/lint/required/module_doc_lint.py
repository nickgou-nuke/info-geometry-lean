#!/usr/bin/env python3
"""Check required module-documentation sections in Lean source files."""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SECTIONS = (
    ("## i. Overview", re.compile(r"^##\s+i\.\s+Overview\s*$", re.M | re.I)),
    ("## ii. Key results", re.compile(r"^##\s+ii\.\s+Key results\s*$", re.M | re.I)),
    ("## iii. Table of contents", re.compile(r"^##\s+iii\.\s+Table of contents\s*$", re.M | re.I)),
    ("## iv. References", re.compile(r"^##\s+iv\.\s+References\s*$", re.M | re.I)),
)


def files_for(args: argparse.Namespace) -> list[Path]:
    if args.files:
        return [Path(p) if Path(p).is_absolute() else ROOT / p for p in args.files]
    if args.all:
        paths = [*(ROOT / "src").rglob("*.lean")] if (ROOT / "src").is_dir() else []
        if (ROOT / "lean").is_dir():
            paths.extend((ROOT / "lean").rglob("*.lean"))
        return sorted(paths)
    result = subprocess.run(
        ["git", "diff", "--name-only", "--diff-filter=ACMRTUXB", "HEAD", "--", "src", "lean"],
        cwd=ROOT, check=True, capture_output=True, text=True,
    )
    return [ROOT / p for p in result.stdout.splitlines() if p.endswith(".lean")]


def lint(path: Path) -> list[str]:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        return [f"{path}: cannot read: {exc}"]
    module_doc = re.search(r"/-!(.*?)-/", text, re.S)
    if not module_doc:
        return [f"{path}: missing module doc block `/-! ... -/`"]
    body = module_doc.group(1)
    findings = []
    if not re.search(r"^#\s+\S.+$", body, re.M):
        findings.append(f"{path}: module doc needs a `# Title` heading")
    for label, pattern in SECTIONS:
        if not pattern.search(body):
            findings.append(f"{path}: module doc missing `{label}`")
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*", help="Lean files; default is changed Lean sources")
    parser.add_argument("--all", action="store_true", help="scan all Lean sources under lean/")
    args = parser.parse_args()
    paths = [p for p in files_for(args) if p.is_file()]
    if not paths:
        print("module-doc lint: no Lean files in scope")
        return 0
    findings = [finding for path in paths for finding in lint(path)]
    if findings:
        print("\n".join(findings), file=sys.stderr)
        return 1
    print(f"module-doc lint: passed ({len(paths)} files)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
