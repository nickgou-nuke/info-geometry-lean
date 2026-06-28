#!/usr/bin/env python3
"""Refresh the Lean syntax, declaration/type, and AST-AQL graph lanes for Mathlib + InfoGeometry.

This wrapper keeps the two maintained export surfaces aligned:

* syntax-tree export via `tools/leantrail/batch_dump_syntax.py`
* declaration/type export via `tools/infra/refresh_decl_graph.py`
* syntax ingest and AST AQL smoke via `tools/leantrail/ingest_syntax_to_arango.py`
  and `tools/leantrail/ast_aql_optimize.py`

The category-theory owner files are already part of `InfoGeometry.All`, so they
are included through the declaration/type lane once `InfoGeometry` is in the
namespace filter.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def run(cmd: list[str]) -> None:
    proc = subprocess.run(cmd, cwd=ROOT)
    if proc.returncode != 0:
        raise SystemExit(proc.returncode)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--syntax-out", default="artifacts/leantrail/batch_syntax_dump.jsonl")
    ap.add_argument("--syntax-root", action="append", type=Path)
    ap.add_argument("--decl-import-root", default="InfoGeometry.All")
    ap.add_argument("--decl-namespace", default="InfoGeometry")
    ap.add_argument("--decl-build-target", default="InfoGeometry.All")
    ap.add_argument("--decl-index-dir", default=None)
    ap.add_argument("--decl-graph-out", default=None)
    ap.add_argument("--decl-structure-out", default=None)
    ap.add_argument("--ingest-http", action="store_true")
    ap.add_argument("--ast-aql-smoke", action="store_true")
    ap.add_argument("--ast-aql-no-index", action="store_true")
    ap.add_argument("--ast-aql-decl", default="AffineDynkinGoutevTonev.affine_delta_cartan_quadratic_zero")
    ap.add_argument("--ast-aql-depth", type=int, default=10)
    ap.add_argument("--skip-prebuild", action="store_true")
    ap.add_argument("--run-mode", choices=["exe", "run"], default="exe")
    ap.add_argument("--stream", action="store_true", help="Use streaming mode for declaration graph (pipe JSONL to ArangoDB)")
    args = ap.parse_args()

    syntax_cmd = [sys.executable, "tools/leantrail/batch_dump_syntax.py", "--out", args.syntax_out]
    if args.syntax_root:
        for root in args.syntax_root:
            syntax_cmd.extend(["--root", str(root)])
    run(syntax_cmd)

    if args.ingest_http:
        ingest_cmd = [
            sys.executable,
            "tools/leantrail/ingest_syntax_to_arango.py",
            str(args.syntax_out),
            "--execute-http",
        ]
    else:
        ingest_cmd = [
            sys.executable,
            "tools/leantrail/ingest_syntax_to_arango.py",
            str(args.syntax_out),
            "--execute",
        ]
    run(ingest_cmd)

    decl_cmd = [
        sys.executable,
        "tools/infra/refresh_decl_graph.py",
        "--import-root",
        args.decl_import_root,
        "--namespace",
        args.decl_namespace,
        "--build-target",
        args.decl_build_target,
        "--run-mode",
        args.run_mode,
    ]
    if args.stream:
        decl_cmd.append("--stream")
    if args.decl_index_dir:
        decl_cmd.extend(["--index-dir", args.decl_index_dir])
    if args.decl_graph_out:
        decl_cmd.extend(["--graph-out", args.decl_graph_out])
    if args.decl_structure_out:
        decl_cmd.extend(["--structure-out", args.decl_structure_out])
    if args.skip_prebuild:
        decl_cmd.append("--skip-prebuild")
    run(decl_cmd)

    if args.ast_aql_smoke:
        ast_cmd = [
            sys.executable,
            "tools/leantrail/ast_aql_optimize.py",
            "--decl",
            args.ast_aql_decl,
            "--depth",
            str(args.ast_aql_depth),
        ]
        if args.ast_aql_no_index:
            ast_cmd.append("--no-index")
        run(ast_cmd)

    print("refresh_mathlib_infogeometry_graphs: refreshed syntax, declaration, and AST lanes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
