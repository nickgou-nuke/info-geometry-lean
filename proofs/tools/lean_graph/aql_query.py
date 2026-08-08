#!/usr/bin/env python3
"""Run AQL against the local Lean AST ArangoDB with only Python stdlib.

This is intentionally dependency-light.  Use it when `python-arango` is not
installed, or when an agent only needs to inspect the existing graph before
editing code.

Examples, from /home/goutev/auto/proofs:

  source /home/goutev/.config/arango/env.sh
  python3 tools/lean_graph/aql_query.py 'RETURN LENGTH(FOR d IN syntax_decls RETURN 1)'

  python3 tools/lean_graph/aql_query.py --file /tmp/query.aql

  python3 tools/lean_graph/aql_query.py <<'AQL'
  FOR d IN syntax_decls
    FILTER CONTAINS(d.name, 'SupergradedCuntzBdG')
    LIMIT 5
    RETURN KEEP(d, ['name', 'keyword', 'range'])
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


def load_env_file(path: Path) -> bool:
    """Load simple `export KEY="value"` shell env files without running shell."""
    if not path.exists():
        return False
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("export "):
            line = line[len("export ") :].strip()
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        key = key.strip()
        value = value.strip().strip('"').strip("'")
        if key and key not in os.environ:
            os.environ[key] = value
    return True


def load_default_env_files(explicit: Path | None) -> None:
    candidates = []
    if explicit is not None:
        candidates.append(explicit)
    for name in ("ARANGO_ENV_FILE", "HIVE_ARANGO_ENV_FILE"):
        value = os.environ.get(name)
        if value:
            candidates.append(Path(value))
    candidates.extend([
        Path("/home/goutev/.config/arango/env.sh"),
        Path.home() / "GITHUB/info-geometry-lean/configs/local/hive_arango.env",
        Path("/home/goutev/auto/configs/local/hive_arango.env"),
    ])
    for candidate in candidates:
        load_env_file(candidate)
    if "ARANGO_PASSWORD" not in os.environ and "ARANGO_PASS" in os.environ:
        os.environ["ARANGO_PASSWORD"] = os.environ["ARANGO_PASS"]
    if "ARANGO_PASS" not in os.environ and "ARANGO_PASSWORD" in os.environ:
        os.environ["ARANGO_PASS"] = os.environ["ARANGO_PASSWORD"]
    if "ARANGO_USER" not in os.environ and "ARANGO_USERNAME" in os.environ:
        os.environ["ARANGO_USER"] = os.environ["ARANGO_USERNAME"]
    if "ARANGO_USERNAME" not in os.environ and "ARANGO_USER" in os.environ:
        os.environ["ARANGO_USERNAME"] = os.environ["ARANGO_USER"]
    if "ARANGO_HOST" not in os.environ and "ARANGO_ENDPOINT" in os.environ:
        os.environ["ARANGO_HOST"] = os.environ["ARANGO_ENDPOINT"]
    if "ARANGO_URL" not in os.environ and "ARANGO_ENDPOINT" in os.environ:
        os.environ["ARANGO_URL"] = os.environ["ARANGO_ENDPOINT"]
    if "ARANGO_DB" not in os.environ and "ARANGO_DATABASE" in os.environ:
        os.environ["ARANGO_DB"] = os.environ["ARANGO_DATABASE"]


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
    load_default_env_files(args.env_file)
    endpoint = args.endpoint or env_first(
        "ARANGO_URL", "ARANGO_ENDPOINT", "ARANGO_HOST", default="http://127.0.0.1:8530"
    )
    database = args.database or env_first("ARANGO_DATABASE", "ARANGO_DB", default="infogeometry")
    username = args.username or env_first("ARANGO_USERNAME", "ARANGO_USER", default="root")
    password = (
        args.password
        if args.password is not None
        else env_first("ARANGO_PASSWORD", "ARANGO_PASS", default="")
    ) or ""
    if not endpoint or not database or not username:
        raise SystemExit("aql_query: missing endpoint/database/username; source env.sh or pass flags")

    body = {
        "query": query,
        "batchSize": args.batch_size,
        "count": args.count,
    }
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
    parser.add_argument("--env-file", type=Path, default=None)
    parser.add_argument("--endpoint")
    parser.add_argument("--database")
    parser.add_argument("--username")
    parser.add_argument("--password")
    parser.add_argument("--bind-vars", help="JSON object for AQL bind variables")
    parser.add_argument("--batch-size", type=int, default=1000)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--count", action="store_true", help="ask ArangoDB to include fullCount/count metadata")
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
