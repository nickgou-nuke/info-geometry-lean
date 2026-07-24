#!/usr/bin/env python3
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
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


def strip_lean_comments_preserve_lines(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(text):
        if block_depth:
            if text.startswith("/-", i):
                block_depth += 1
                out.extend((" ", " "))
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
            else:
                ch = text[i]
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            ch = text[i]
            out.append(ch)
            i += 1
            if ch == "\\" and i < len(text):
                out.append(text[i])
                i += 1
            elif ch == '"':
                in_string = False
            continue

        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if text.startswith("/-", i):
            block_depth = 1
            out.extend((" ", " "))
            i += 2
            continue
        ch = text[i]
        out.append(ch)
        i += 1
        if ch == '"':
            in_string = True
    return "".join(out)


DECL_RE_TEMPLATE = (
    r"^(?:noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|opaque|structure|class|instance)\s+"
    r"{name}\b"
)


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
        source_lines = text.splitlines()
        code_lines = strip_lean_comments_preserve_lines(text).splitlines()
        local_hits: list[dict[str, object]] = []
        for i, code_line in enumerate(code_lines, start=1):
            stripped = code_line.strip()
            source = source_lines[i - 1].strip() if i <= len(source_lines) else stripped
            for short_name, full_name in needles.items():
                if re.search(rf"\b{re.escape(short_name)}\b", code_line):
                    kind = "use"
                    decl_re = DECL_RE_TEMPLATE.format(name=re.escape(short_name))
                    if re.match(decl_re, stripped):
                        kind = "declaration"
                    local_hits.append(
                        {
                            "line": i,
                            "kind": kind,
                            "name": full_name,
                            "short_name": short_name,
                            "source": source,
                        }
                    )
        if local_hits:
            owners[str(path.relative_to(REPO))] = local_hits
    return owners


def summarize_owner_map(owners: dict[str, list[dict[str, object]]]) -> list[dict[str, object]]:
    summaries: list[dict[str, object]] = []
    for file, hits in sorted(owners.items()):
        declarations = sorted(
            {
                str(hit["name"])
                for hit in hits
                if hit.get("kind") == "declaration"
            }
        )
        uses = sorted(
            {
                str(hit["name"])
                for hit in hits
                if hit.get("kind") == "use"
            }
        )
        summaries.append(
            {
                "file": file,
                "declarations": declarations,
                "uses": uses,
                "declaration_count": len(declarations),
                "use_count": len(uses),
                "code_only": True,
            }
        )
    return summaries


def declaration_users(owners: dict[str, list[dict[str, object]]]) -> dict[str, list[str]]:
    declared_in: dict[str, set[str]] = defaultdict(set)
    used_in: dict[str, set[str]] = defaultdict(set)
    for file, hits in owners.items():
        for hit in hits:
            name = str(hit.get("name") or "")
            if not name:
                continue
            if hit.get("kind") == "declaration":
                declared_in[name].add(file)
            elif hit.get("kind") == "use":
                used_in[name].add(file)
    return {
        name: sorted(files - declared_in.get(name, set()))
        for name, files in sorted(used_in.items())
    }


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
        "file_summary": summarize_owner_map(owners),
        "external_code_users": declaration_users(owners),
        "source_policy": "Lean comments and docstrings excluded",
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
