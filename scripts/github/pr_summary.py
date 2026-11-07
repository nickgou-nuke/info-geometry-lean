#!/usr/bin/env python3
"""Render a source-backed Markdown summary of a Git change range."""
from __future__ import annotations
import argparse, subprocess

def git(*args: str) -> str:
    return subprocess.run(["git", *args], check=True, text=True, capture_output=True).stdout.strip()

def main() -> int:
    ap=argparse.ArgumentParser(description=__doc__); ap.add_argument("--base",default="upstream/main"); ap.add_argument("--head",default="HEAD"); n=ap.parse_args()
    changed=git("diff","--name-status",n.base,n.head).splitlines()
    stats=git("diff","--shortstat",n.base,n.head)
    print(f"## Change summary\n\nRange: `{n.base}..{n.head}`\n\n{stats or 'No changes.'}\n")
    print("### Changed paths\n")
    for item in changed: print(f"- `{item}`")
    lean=[line for line in changed if line.split("\t")[-1].endswith(".lean")]
    print(f"\nLean source paths changed: **{len(lean)}**")
    print("\nGenerated from Git diff metadata; it does not certify compilation or proof quality.")
    return 0
if __name__=="__main__": raise SystemExit(main())
