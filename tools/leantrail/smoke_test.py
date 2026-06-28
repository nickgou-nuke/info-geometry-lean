#!/usr/bin/env python3
"""Smoke-test LeanTrail utilities in this repository.

This test avoids network/LLM calls and validates the local paths that should work
on a fresh checkout with the local Arango service available:

- `refresh_mathlib_infogeometry_graphs.py` for the coordinated syntax,
  declaration/type, syntax-ingest, and AST-AQL lane;
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


def run(cmd: list[str], *, capture: bool = True) -> subprocess.CompletedProcess[str]:
    print("$", " ".join(cmd))
    proc = subprocess.run(
        cmd,
        cwd=REPO,
        text=True,
        capture_output=capture,
    )
    if capture:
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

    print("[smoke] stage 1/5: coordinated graph refresh", flush=True)
    run([
        "python3", "tools/infra/refresh_mathlib_infogeometry_graphs.py",
        "--syntax-out", str(TMP / "batch_syntax.jsonl"),
        "--decl-index-dir", str(TMP / "decl-index"),
        "--decl-graph-out", str(TMP / "decl-graph.json"),
        "--decl-structure-out", str(TMP / "decl-structure.json"),
        "--skip-prebuild",
        *([] if args.skip_arango else [
            "--ingest-http",
            "--ast-aql-smoke",
            "--ast-aql-no-index",
        ]),
    ], capture=False)
    batch_syntax = TMP / "batch_syntax.jsonl"
    node = json.loads(batch_syntax.read_text().splitlines()[0])
    assert node.get("layer") == "syntax" and "name" in node
    assert (TMP / "decl-index" / "decls.jsonl").exists()

    print("[smoke] stage 2/5: external index export", flush=True)
    run([
        "python3", "tools/leantrail/external_index.py",
        "--repo", "lean/InfoGeometry/Algebra",
        "--out", str(TMP / "external_arango.json"),
        "--format", "arango", "--chunk", "--limit", "3",
    ], capture=False)
    ext = json.loads((TMP / "external_arango.json").read_text())
    assert ext["collection"] == "alexandria_chunks" and ext["documents"]

    print("[smoke] stage 3/5: oracle search", flush=True)
    proc = run([
        "python3", "tools/leantrail/oracle_search.py",
        "--search", "cuntzMajoranaSupercharge",
        "--local-only", "--limit", "3",
    ])
    assert "CuntzSupergradedSUSY.lean" in proc.stdout

    print("[smoke] stage 4/5: syntax shape check", flush=True)
    check = subprocess.run([
        "python3", "tools/leantrail/check_dump_shape.py", "--expect-keyword", "theorem",
    ], cwd=REPO, text=True, stdin=batch_syntax.open("r", encoding="utf-8"), capture_output=True)
    if check.stderr:
        print(check.stderr.strip(), file=sys.stderr)
    if check.returncode != 0:
        print(check.stdout)
        raise SystemExit(check.returncode)

    if not args.skip_arango:
        print("[smoke] stage 5/5: live arango checks", flush=True)
        run([
            "python3", "tools/leantrail/arango_dump.py",
            "--cone-downstream", "InfoGeometry.Algebra.AlbertCD.CDInvolutionDatum.casesOn",
            "--max-depth", "1",
            "--out", str(TMP / "cone.json"),
        ], capture=False)
        cone = json.loads((TMP / "cone.json").read_text())
        assert isinstance(cone, list)

        run(["bash", "tools/leantrail/aql_smoke_test.sh"], capture=False)
    print("leantrail smoke passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
