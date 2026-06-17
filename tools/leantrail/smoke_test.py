#!/usr/bin/env python3
"""Smoke-test LeanTrail utilities in this repository.

This test avoids network/LLM calls and validates the local paths that should work
on a fresh checkout with the local Arango service available:

- `ast_extract.py` on a small Lean subtree;
- `external_index.py` on a repository-local Lean path;
- `oracle_search.py --local-only` for actual repo symbols;
- optional `arango_dump.py` live check unless `--skip-arango` is passed.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
TMP = Path("/tmp/leantrail_smoke")


def run(cmd: list[str]) -> subprocess.CompletedProcess[str]:
    print("$", " ".join(cmd))
    proc = subprocess.run(cmd, cwd=REPO, text=True, capture_output=True)
    if proc.stdout:
        print(proc.stdout.strip())
    if proc.stderr:
        print(proc.stderr.strip(), file=sys.stderr)
    if proc.returncode != 0:
        raise SystemExit(proc.returncode)
    return proc


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--skip-arango", action="store_true")
    args = ap.parse_args()

    TMP.mkdir(parents=True, exist_ok=True)

    run([
        "python3", "tools/leantrail/ast_extract.py",
        "--root", "lean/InfoGeometry/Algebra",
        "--out", str(TMP / "algebra_ast"),
        "--jsonl", "--no-imports",
    ])
    node = json.loads((TMP / "algebra_ast_nodes.jsonl").read_text().splitlines()[0])
    assert "_key" in node and "module" in node and "namespace" in node

    run([
        "python3", "tools/leantrail/external_index.py",
        "--repo", "lean/InfoGeometry/Algebra",
        "--out", str(TMP / "external_arango.json"),
        "--format", "arango", "--chunk", "--limit", "3",
    ])
    ext = json.loads((TMP / "external_arango.json").read_text())
    assert ext["collection"] == "alexandria_chunks" and ext["documents"]

    proc = run([
        "python3", "tools/leantrail/oracle_search.py",
        "--search", "cuntzMajoranaSupercharge",
        "--local-only", "--limit", "3",
    ])
    assert "CuntzSupergradedSUSY.lean" in proc.stdout

    syntax_jsonl = TMP / "dump_syntax.jsonl"
    with syntax_jsonl.open("w", encoding="utf-8") as out:
        proc = subprocess.run([
            "lake", "env", "lean", "--run", "tools/leantrail/DumpLeanGraph.lean",
            "lean/InfoGeometry/Algebra/CuntzLorentzPoincarePresentation.lean",
        ], cwd=REPO, text=True, stdout=out, stderr=subprocess.PIPE)
    if proc.stderr:
        print(proc.stderr.strip(), file=sys.stderr)
    if proc.returncode != 0:
        raise SystemExit(proc.returncode)
    check = subprocess.run([
        "python3", "tools/leantrail/check_dump_shape.py", "--expect-keyword", "theorem",
    ], cwd=REPO, text=True, stdin=syntax_jsonl.open("r", encoding="utf-8"), capture_output=True)
    if check.stderr:
        print(check.stderr.strip(), file=sys.stderr)
    if check.returncode != 0:
        print(check.stdout)
        raise SystemExit(check.returncode)

    if not args.skip_arango:
        run([
            "python3", "tools/leantrail/arango_dump.py",
            "--cone-downstream", "InfoGeometry.Algebra.AlbertCD.CDInvolutionDatum.casesOn",
            "--max-depth", "1",
            "--out", str(TMP / "cone.json"),
        ])
        cone = json.loads((TMP / "cone.json").read_text())
        assert isinstance(cone, list)

        run(["bash", "tools/leantrail/aql_smoke_test.sh"])
        run([
            "python3", "tools/leantrail/ingest_syntax_to_arango.py",
            str(syntax_jsonl), "--execute-http",
        ])
        proc = run([
            "python3", "tools/leantrail/ast_aql_optimize.py",
            "--no-index", "--depth", "5",
        ])
        assert "atom_first_sorry_scan" in proc.stdout
        assert "bounded_decl_ast_cone" in proc.stdout

    print("leantrail smoke passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
