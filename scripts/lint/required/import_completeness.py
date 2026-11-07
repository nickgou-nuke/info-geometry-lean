#!/usr/bin/env python3
"""Check selected Lean import names resolve to source modules or known roots."""
from __future__ import annotations
import argparse, re, subprocess, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
IMPORT=re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)")
def main()->int:
    ap=argparse.ArgumentParser(description=__doc__); ap.add_argument("files",nargs="*"); ap.add_argument("--all",action="store_true"); ns=ap.parse_args()
    if ns.files: paths=[Path(p) if Path(p).is_absolute() else ROOT/p for p in ns.files]
    elif ns.all:
        paths=[*(ROOT/"src").rglob("*.lean")] if (ROOT/"src").is_dir() else []
        if (ROOT/"lean").is_dir(): paths.extend((ROOT/"lean").rglob("*.lean"))
    else:
        r=subprocess.run(["git","diff","--name-only","--diff-filter=ACMRTUXB","HEAD","--","src","lean"],cwd=ROOT,text=True,capture_output=True,check=True); paths=[ROOT/p for p in r.stdout.splitlines() if p.endswith(".lean")]
    errors=[]
    for path in paths:
        if not path.is_file(): continue
        seen=set()
        for n,line in enumerate(path.read_text(encoding="utf-8").splitlines(),1):
            m=IMPORT.match(line)
            if not m: continue
            name=m.group(1)
            if name in seen: errors.append(f"{path.relative_to(ROOT)}:{n}: duplicate import {name}")
            seen.add(name)
            rel=Path(*name.split(".")).with_suffix(".lean")
            if name.startswith("InfoGeometry.") and not ((ROOT/"src"/rel).is_file() or (ROOT/"lean"/rel).is_file()): errors.append(f"{path.relative_to(ROOT)}:{n}: unresolved repo import {name}")
    if errors: print("\n".join(errors),file=sys.stderr); return 1
    print(f"import completeness: passed ({len(paths)} selected Lean paths)"); return 0
if __name__=="__main__": raise SystemExit(main())
