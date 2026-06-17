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
import base64
import json
import os
import sys
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any


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
    load_env_file(args.env_file)
    endpoint = env_first("ARANGO_URL", "ARANGO_ENDPOINT", "ARANGO_HOST", default=args.endpoint)
    database = env_first("ARANGO_DATABASE", "ARANGO_DB", default=args.database)
    username = env_first("ARANGO_USERNAME", "ARANGO_USER", default=args.username)
    password = env_first("ARANGO_PASSWORD", default=args.password) or ""
    if not endpoint or not database or not username:
        raise SystemExit("aql_query: missing endpoint/database/username")

    body: dict[str, Any] = {"query": query, "batchSize": args.batch_size, "count": args.count}
    if args.bind_vars:
        try:
            body["bindVars"] = json.loads(args.bind_vars)
        except json.JSONDecodeError as exc:
            raise SystemExit(f"aql_query: invalid --bind-vars JSON: {exc}") from exc

    payload = json.dumps(body).encode("utf-8")
    url = f"{endpoint.rstrip('/')}/_db/{database}/_api/cursor"
    request = urllib.request.Request(url, data=payload, headers={"Content-Type": "application/json"})
    token = base64.b64encode(f"{username}:{password}".encode("utf-8")).decode("ascii")
    request.add_header("Authorization", f"Basic {token}")
    try:
        with urllib.request.urlopen(request, timeout=args.timeout) as response:
            return json.load(response)
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", "replace")
        raise SystemExit(f"aql_query: HTTP {exc.code}: {detail}") from exc
    except urllib.error.URLError as exc:
        raise SystemExit(f"aql_query: connection failed: {exc}") from exc


def main() -> None:
    parser = argparse.ArgumentParser(description="Run AQL via ArangoDB HTTP API")
    parser.add_argument("query", nargs="?", help="AQL query; if omitted, use --file or stdin")
    parser.add_argument("--file", type=Path, help="read AQL query from file")
    parser.add_argument("--env-file", type=Path, default=Path.home() / ".config/arango/env.sh")
    parser.add_argument("--endpoint", default="http://127.0.0.1:8530")
    parser.add_argument("--database", default="infogeometry")
    parser.add_argument("--username", default="root")
    parser.add_argument("--password", default="")
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
    response = run_aql(query, args)
    if response.get("error"):
        raise SystemExit(json.dumps(response, indent=2, ensure_ascii=False))
    output: Any = response if args.raw else response.get("result", [])
    if args.compact:
        print(json.dumps(output, ensure_ascii=False, separators=(",", ":")))
    else:
        print(json.dumps(output, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
