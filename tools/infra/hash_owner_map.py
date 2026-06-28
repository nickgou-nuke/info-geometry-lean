#!/usr/bin/env python3
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
LEAN_ROOT = REPO / "lean"

LEAN_SCANNER = r'''
import Lean
import DAG.ExprFingerprint

open Lean
open DAG

def scanValueHash (target : UInt64) (limit : Nat) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `InfoGeometry.All : Import }] {} 0
  let mut count : Nat := 0
  let mut shown : Nat := 0
  for (n, ci) in env.constants do
    if let some v := ci.value? then
      let h := (computeFingerprint v).shapeHash
      if h == target then
        count := count + 1
        if shown < limit then
          IO.println s!"VALUE {h.toNat} {n}"
          shown := shown + 1
  IO.println s!"TOTAL {target.toNat} {count}"

def main (args : List String) : IO UInt32 := do
  match args with
  | hs :: lims :: _ =>
      scanValueHash (UInt64.ofNat (String.toNat! hs)) (String.toNat! lims)
      pure 0
  | hs :: _ =>
      scanValueHash (UInt64.ofNat (String.toNat! hs)) 50
      pure 0
  | [] =>
      IO.eprintln "need hash"
      pure 1
'''


def run_hash_scan(hash_value: str, limit: int) -> tuple[list[str], int]:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(LEAN_SCANNER)
        scanner_path = f.name
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", "--run", scanner_path, hash_value, str(limit)],
            cwd=REPO,
            text=True,
            capture_output=True,
            check=False,
        )
        if proc.returncode != 0:
            sys.stderr.write(proc.stdout)
            sys.stderr.write(proc.stderr)
            raise SystemExit(proc.returncode)
        names: list[str] = []
        total = 0
        for line in proc.stdout.splitlines():
            if line.startswith("VALUE "):
                _, _, name = line.split(" ", 2)
                names.append(name.strip())
            elif line.startswith("TOTAL "):
                parts = line.split()
                total = int(parts[-1])
        return names, total
    finally:
        try:
            os.unlink(scanner_path)
        except OSError:
            pass


def recursive_owner_scan(names: list[str]) -> dict[str, list[dict[str, object]]]:
    needles = {}
    for name in names:
        if not name.startswith("InfoGeometry."):
            continue
        short_name = name.split(".")[-1]
        if not re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", short_name):
            continue
        needles[short_name] = name
    owners: dict[str, list[dict[str, object]]] = {}
    for path in LEAN_ROOT.rglob("*.lean"):
        text = path.read_text(errors="ignore")
        lines = text.splitlines()
        local_hits: list[dict[str, object]] = []
        for i, line in enumerate(lines, start=1):
            stripped = line.strip()
            for short_name, full_name in needles.items():
                if re.search(rf"\b{re.escape(short_name)}\b", line):
                    kind = "use"
                    if re.match(rf"^(theorem|lemma|def|abbrev|structure)\s+{re.escape(short_name)}\b", stripped):
                        kind = "declaration"
                    elif stripped.startswith("--") or stripped.startswith("/-"):
                        kind = "comment"
                    local_hits.append(
                        {
                            "line": i,
                            "kind": kind,
                            "name": full_name,
                            "short_name": short_name,
                            "source": stripped,
                        }
                    )
        if local_hits:
            owners[str(path.relative_to(REPO))] = local_hits
    return owners


def main() -> int:
    if len(sys.argv) < 2:
        print("usage: hash_owner_map.py <shapeHash> [limit]", file=sys.stderr)
        return 2
    hash_value = sys.argv[1]
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    names, total = run_hash_scan(hash_value, limit)
    owners = recursive_owner_scan(names)
    result = {
        "shapeHash": hash_value,
        "sample_count": len(names),
        "total_matches": total,
        "sample_names": names,
        "owner_map": owners,
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
