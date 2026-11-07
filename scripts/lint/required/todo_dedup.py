#!/usr/bin/env python3
"""Reject repeated normalized TODO/FIXME comment text within a Lean file."""
from __future__ import annotations
import argparse,re,subprocess,sys
from collections import defaultdict
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
TODO=re.compile(r"(?:--|/-|\*)\s*(TODO|FIXME)\s*:?\s*(.*?)\s*(?:\*/|-/)?$",re.I)
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
  found=defaultdict(list)
  for i,line in enumerate(p.read_text(encoding="utf-8").splitlines(),1):
   m=TODO.search(line)
   if m and m.group(2).strip(): found[(m.group(1).lower(),re.sub(r"\s+"," ",m.group(2).strip()).casefold())].append(i)
  for (_,text),lines in found.items():
   if len(lines)>1: errors.append(f"{p.relative_to(ROOT)}:{','.join(map(str,lines))}: duplicate TODO/FIXME `{text}`")
 if errors: print("\n".join(errors),file=sys.stderr); return 1
 print(f"TODO dedup: passed ({len(files)} selected Lean paths)"); return 0
if __name__=="__main__": raise SystemExit(main())
