#!/usr/bin/env python3
"""Small changed-file Lean style gate (line width, tabs, module doc presence)."""
from __future__ import annotations
import argparse, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("files", nargs="*")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--strict-line-length", action="store_true")
    ns = ap.parse_args()
    if ns.files:
        files = [Path(p) if Path(p).is_absolute() else ROOT / p for p in ns.files]
    elif ns.all:
        files = [*(ROOT / "src").rglob("*.lean")] if (ROOT / "src").is_dir() else []
        if (ROOT / "lean").is_dir():
            files.extend((ROOT / "lean").rglob("*.lean"))
    else:
        r = subprocess.run(["git", "diff", "--name-only", "--diff-filter=ACMRTUXB", "HEAD", "--", "src", "lean"], cwd=ROOT, text=True, capture_output=True, check=True)
        files = [ROOT / p for p in r.stdout.splitlines() if p.endswith(".lean")]
    errors=[]
    for path in files:
        if not path.is_file(): continue
        text = path.read_text(encoding="utf-8")
        if not text.startswith("/-"):
            errors.append(f"{path.relative_to(ROOT)}:1: missing copyright header `/- ... -/`")
        for i, line in enumerate(text.splitlines(), 1):
            if ns.strict_line_length and len(line) > 100 and "http" not in line:
                errors.append(f"{path.relative_to(ROOT)}:{i}: {len(line)} chars (limit 100)")
            if "\t" in line:
                errors.append(f"{path.relative_to(ROOT)}:{i}: tab character")
    if errors:
        print("\n".join(errors), file=sys.stderr); return 1
    print(f"style lint: passed ({len(files)} selected Lean paths)"); return 0
if __name__ == "__main__": raise SystemExit(main())
