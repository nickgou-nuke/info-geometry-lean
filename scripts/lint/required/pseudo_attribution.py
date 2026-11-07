#!/usr/bin/env python3
"""Require a nearby explanatory comment on any `@[pseudo]` declaration."""
from __future__ import annotations
import argparse,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
def main()->int:
 ap=argparse.ArgumentParser(description=__doc__); ap.add_argument("files",nargs="*"); ap.add_argument("--all",action="store_true"); n=ap.parse_args()
 if n.files: files=[Path(p) if Path(p).is_absolute() else ROOT/p for p in n.files]
 elif n.all:
  files=[*(ROOT/"src").rglob("*.lean")] if (ROOT/"src").is_dir() else []
  if (ROOT/"lean").is_dir(): files.extend((ROOT/"lean").rglob("*.lean"))
 else:
  r=subprocess.run(["git","diff","--name-only","--diff-filter=ACMRTUXB","HEAD","--","src","lean"],cwd=ROOT,text=True,capture_output=True,check=True); files=[ROOT/p for p in r.stdout.splitlines() if p.endswith(".lean")]
 errors=[]
 for p in files:
  if not p.is_file(): continue
  lines=p.read_text(encoding="utf-8").splitlines()
  for i,line in enumerate(lines):
   if "@[pseudo]" in line:
    context="\n".join(lines[max(0,i-8):i+1]).lower()
    if not re.search(r"(--|/-\*?|\*)[^\n]*(pseudo|approx|surrogate|reason|source|reference)",context): errors.append(f"{p.relative_to(ROOT)}:{i+1}: @[pseudo] needs a nearby rationale/source comment")
 if errors: print("\n".join(errors),file=sys.stderr); return 1
 print(f"pseudo attribution: passed ({len(files)} selected Lean paths)"); return 0
if __name__=="__main__": raise SystemExit(main())
