#!/usr/bin/env python3
"""Phase-1 claim promotion guard.

Promotes claim.status according to an allowed transition lattice.
Enforces witness/formal/audit gates for formal_candidate promotion.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import sys
from typing import Any

import requests


ALLOWED = {
    "prima_materia": {"analogy", "hypothesis"},
    "analogy": {"hypothesis", "rejected", "unsafe_overclaim"},
    "hypothesis": {"witness_socket", "unsafe_overclaim", "rejected"},
    "witness_socket": {"formal_candidate", "rejected"},
    "formal_candidate": {"lean_theorem", "rejected"},
    "lean_theorem": set(),
    "unsafe_overclaim": {"rejected"},
    "rejected": set(),
}


def now_iso() -> str:
    return dt.datetime.utcnow().replace(microsecond=0).isoformat() + "Z"


def env(name: str, *aliases: str, required: bool = False, default: str | None = None) -> str | None:
    for k in (name, *aliases):
        v = os.environ.get(k)
        if v:
            return v
    if required and default is None:
        raise RuntimeError(f"missing env var: {name}")
    return default


class Arango:
    def __init__(self) -> None:
        self.endpoint = env("ARANGO_ENDPOINT", required=True)
        self.database = env("ARANGO_DATABASE", default="infogeometry")
        self.user = env("ARANGO_USER", "ARANGO_USERNAME", required=True)
        self.password = env("ARANGO_PASS", "ARANGO_PASSWORD", required=True)
        self.base = f"{self.endpoint.rstrip('/')}/_db/{self.database}/_api"
        self.auth = (self.user, self.password)
        self.headers = {"content-type": "application/json"}

    def aql(self, query: str, bind: dict[str, Any]) -> list[dict[str, Any]]:
        r = requests.post(
            f"{self.base}/cursor",
            auth=self.auth,
            headers=self.headers,
            data=json.dumps({"query": query, "bindVars": bind}),
            timeout=30,
        )
        if r.status_code not in (200, 201):
            raise RuntimeError(f"AQL failed {r.status_code}: {r.text[:400]}")
        return r.json().get("result", [])


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--claim-id", required=True)
    ap.add_argument("--to-status", required=True)
    ap.add_argument("--note", default="")
    args = ap.parse_args()

    ar = Arango()
    rows = ar.aql("FOR c IN claims FILTER c.claim_id == @id LIMIT 1 RETURN c", {"id": args.claim_id})
    if not rows:
        raise RuntimeError(f"claim not found: {args.claim_id}")
    claim = rows[0]
    cur = claim.get("status", "prima_materia")
    nxt = args.to_status

    allowed = ALLOWED.get(cur, set())
    if nxt not in allowed:
        raise RuntimeError(f"invalid transition: {cur} -> {nxt}")

    if nxt == "formal_candidate":
        if not claim.get("formal_target"):
            raise RuntimeError("formal_candidate requires formal_target")
        if claim.get("status") != "witness_socket":
            raise RuntimeError("formal_candidate requires current status witness_socket")
        if not claim.get("pauli_audit_note"):
            raise RuntimeError("formal_candidate requires pauli_audit_note")

    claim["status"] = nxt
    claim["updated_at"] = now_iso()
    if args.note:
        claim.setdefault("promotion_notes", []).append({"ts": claim["updated_at"], "note": args.note})

    # replace by _key
    ar.aql(
        "FOR c IN claims FILTER c._key == @k UPDATE c WITH @doc IN claims OPTIONS { mergeObjects: false } RETURN NEW",
        {"k": claim["_key"], "doc": claim},
    )

    print(json.dumps({"ok": True, "claim_id": args.claim_id, "from": cur, "to": nxt}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as e:
        print(json.dumps({"ok": False, "error": str(e)}), file=sys.stderr)
        raise
