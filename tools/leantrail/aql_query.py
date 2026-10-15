#!/usr/bin/env python3
"""Run AQL against local LeanTrail ArangoDB using only Python stdlib.

Examples:
  python3 tools/leantrail/aql_query.py 'RETURN 1'

  python3 tools/leantrail/aql_query.py <<'AQL'
  FOR d IN syntax_decls
    FILTER CONTAINS(d.name, 'Cuntz')
    LIMIT 5
    RETURN {name: d.name, keyword: d.keyword, range: d.range}
  AQL
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "src"))
sys.path.insert(0, str(REPO_ROOT))


def load_env_file(path: Path) -> None:
    if not path.exists():
        return
    for raw in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("export "):
            line = line[len("export "):].strip()
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        key = key.strip()
        value = value.strip().strip('"').strip("'")
        if key and key not in os.environ:
            os.environ[key] = value


def env_first(*names: str, default: str | None = None) -> str | None:
    for name in names:
        value = os.environ.get(name)
        if value:
            return value
    return default


def read_query(args: argparse.Namespace) -> str:
    if args.query:
        return args.query
    if args.file:
        return args.file.read_text(encoding="utf-8")
    if not sys.stdin.isatty():
        return sys.stdin.read()
    raise SystemExit("aql_query: provide query argument, --file, or stdin")


def run_aql(query: str, args: argparse.Namespace) -> dict[str, Any]:
    from igf.config import (load_repo_arango_env, arango_endpoint,
                            arango_database, arango_username, arango_password)
    from igf.graph.arango_http import ArangoHttpTarget, execute_aql_response
    load_repo_arango_env()
    if args.env_file:
        load_env_file(args.env_file)
    target = ArangoHttpTarget(args.endpoint or arango_endpoint(),
                             args.database or arango_database(),
                             args.username or arango_username(), arango_password())
    bind_vars = json.loads(args.bind_vars) if args.bind_vars else {}
    if not isinstance(bind_vars, dict):
        raise ValueError("--bind-vars must be a JSON object")
    return execute_aql_response(target, query, bind_vars, timeout=args.timeout,
                                batch_size=args.batch_size, count=args.count)


def main() -> None:
    parser = argparse.ArgumentParser(description="Run AQL via ArangoDB HTTP API")
    parser.add_argument("query", nargs="?", help="AQL query; if omitted, use --file or stdin")
    parser.add_argument("--file", type=Path, help="read AQL query from file")
    parser.add_argument("--env-file", type=Path, default=None)
    parser.add_argument("--endpoint", default=None)
    parser.add_argument("--database", default=None)
    parser.add_argument("--username", default=None)
    parser.add_argument("--bind-vars", help="JSON object for AQL bind variables")
    parser.add_argument("--batch-size", type=int, default=1000)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--count", action="store_true", help="ask ArangoDB to include count metadata")
    parser.add_argument("--raw", action="store_true", help="print full cursor response, not just result")
    parser.add_argument("--compact", action="store_true", help="compact JSON output")
    args = parser.parse_args()

    query = read_query(args).strip()
    if not query:
        raise SystemExit("aql_query: empty query")
    try:
        response = run_aql(query, args)
    except Exception as exc:
        raise SystemExit(f"aql_query: query failed ({type(exc).__name__}); no result produced") from exc
    if response.get("error"):
        raise SystemExit(json.dumps(response, indent=2, ensure_ascii=False))
    output: Any = response if args.raw else response.get("result", [])
    if args.compact:
        print(json.dumps(output, ensure_ascii=False, separators=(",", ":")))
    else:
        print(json.dumps(output, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
