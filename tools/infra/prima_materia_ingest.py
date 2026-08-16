#!/usr/bin/env python3
"""Phase-1 Prima Materia ingest (ArangoDB).

Inputs:
  - artifact JSON file (required)
  - optional claims JSON file (list of claim docs)

Writes:
  - prima_materia_artifacts
  - claims (status default: prima_materia)
  - graph_morphisms (optional provenance morphism)
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import sys
from typing import Any

import requests


# [lossless-compact] now_iso folded into igf.common.time_utils.now_iso
from igf.common.time_utils import now_iso


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

    def insert(self, collection: str, doc: dict[str, Any], overwrite: bool = True) -> dict[str, Any]:
        mode = "replace" if overwrite else "ignore"
        url = f"{self.base}/document/{collection}?overwriteMode={mode}"
        r = requests.post(url, auth=self.auth, headers=self.headers, data=json.dumps(doc), timeout=30)
        if r.status_code not in (200, 201, 202):
            raise RuntimeError(f"insert {collection} failed {r.status_code}: {r.text[:400]}")
        return r.json()


# [lossless-compact] load_json folded into igf.common.json_io.load_json
from igf.common.json_io import load_json


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--artifact-json", required=True, help="Artifact JSON document")
    ap.add_argument("--claims-json", help="Optional JSON array of claim docs")
    ap.add_argument("--session-id", default="manual")
    ap.add_argument("--agent", default="Hermes")
    args = ap.parse_args()

    ar = Arango()
    artifact = load_json(args.artifact_json)

    artifact.setdefault("created_at", now_iso())
    artifact.setdefault("updated_at", artifact["created_at"])
    artifact.setdefault("claim_status", "prima_materia")
    if "artifact_id" not in artifact:
        raise RuntimeError("artifact JSON must include artifact_id")

    ar.insert("prima_materia_artifacts", artifact)

    inserted_claims = []
    if args.claims_json:
        claims = load_json(args.claims_json)
        if not isinstance(claims, list):
            raise RuntimeError("claims JSON must be an array")
        for c in claims:
            c.setdefault("status", "prima_materia")
            c.setdefault("created_at", now_iso())
            c.setdefault("updated_at", c["created_at"])
            c.setdefault("artifact_ref", f"prima_materia_artifacts/{artifact['artifact_id']}")
            if "claim_id" not in c:
                raise RuntimeError("every claim must include claim_id")
            ar.insert("claims", c)
            inserted_claims.append(c["claim_id"])

    morphism = {
        "morphism_id": f"morph.{args.agent.lower()}.{args.session_id}.{artifact['artifact_id']}",
        "agent": args.agent,
        "operation": "ingest_prima_materia",
        "source_graph": artifact.get("source", "external"),
        "target_graph": "claims" if inserted_claims else "prima_materia_artifacts",
        "input_nodes": [artifact["artifact_id"]],
        "output_nodes": inserted_claims,
        "claim_status": artifact.get("claim_status", "prima_materia"),
        "requires_audit": True,
        "created_at": now_iso(),
    }
    ar.insert("graph_morphisms", morphism)

    print(json.dumps({
        "ok": True,
        "artifact_id": artifact["artifact_id"],
        "claims_inserted": inserted_claims,
        "morphism_id": morphism["morphism_id"],
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as e:
        print(json.dumps({"ok": False, "error": str(e)}), file=sys.stderr)
        raise
