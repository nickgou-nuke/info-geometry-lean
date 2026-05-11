#!/usr/bin/env python3
"""Loogle retrieval bee worker for Hive.

Queries the local Loogle Mathlib search server and emits
RetrievalResultPacket packets for other bees to consume.

Usage:
    python3 tools/infra/hive_loogle_bee_worker.py --query "List.replicate (_ + _) _"
    python3 tools/infra/hive_loogle_bee_worker.py --task task.json
"""

from __future__ import annotations

import argparse
import json
import sys
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

LOOGLE_DEFAULT_URL = "http://127.0.0.1:8088/json"


def query_loogle(q: str, url: str = LOOGLE_DEFAULT_URL, timeout: int = 30) -> dict:
    """Query Loogle and return parsed JSON."""
    full_url = f"{url}?q={urllib.parse.quote(q)}"
    req = urllib.request.Request(full_url, headers={"User-Agent": "loogle-hive-bee/1.0"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read().decode())


def make_retrieval_packet(query: str, result: dict, worker_id: str = "LoogleBee") -> dict:
    """Create a RetrievalResultPacket from Loogle results."""
    now = datetime.now(timezone.utc).isoformat()
    hits = result.get("hits", [])
    count = result.get("count", 0)

    return {
        "id": f"loogle_retrieval_{hash(query) & 0xFFFFFFFF:08x}",
        "kind": "RetrievalResultPacket",
        "status": "done",
        "authority": "navigation",
        "promotion_allowed": False,
        "created_at": now,
        "updated_at": now,
        "worker_id": worker_id,
        "query": query,
        "result_count": count,
        "hits": [
            {
                "name": h["name"],
                "module": h["module"],
                "type": h.get("type", ""),
                "doc": h.get("doc", ""),
            }
            for h in hits[:20]
        ],
    }


def main():
    parser = argparse.ArgumentParser(description="Loogle retrieval bee worker")
    parser.add_argument("--query", help="Loogle query string")
    parser.add_argument("--task", help="Path to a Hive task JSON file")
    parser.add_argument("--loogle-url", default=LOOGLE_DEFAULT_URL, help="Loogle server URL")
    parser.add_argument("--output", help="Output path for the result packet (JSON)")
    parser.add_argument("--json", action="store_true", help="Print raw Loogle JSON")
    args = parser.parse_args()

    query = args.query

    if args.task:
        task = json.loads(Path(args.task).read_text())
        query = query or task.get("query") or task.get("instruction", "")

    if not query:
        print("Error: No query provided. Use --query or --task.", file=sys.stderr)
        sys.exit(1)

    try:
        result = query_loogle(query, url=args.loogle_url)
    except Exception as e:
        print(f"Loogle query failed: {e}", file=sys.stderr)
        sys.exit(1)

    if args.json:
        print(json.dumps(result, indent=2))
        return

    packet = make_retrieval_packet(query, result)
    packet_json = json.dumps(packet, indent=2)

    if args.output:
        Path(args.output).write_text(packet_json)
        print(f"RetrievalResultPacket written to {args.output}")
    else:
        print(packet_json)


if __name__ == "__main__":
    main()
