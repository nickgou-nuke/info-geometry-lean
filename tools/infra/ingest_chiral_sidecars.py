#!/usr/bin/env python3
"""Ingest chiral sidecar JSONL artifacts into ArangoDB (immutable runs).

One-command pipeline:
1) create collections/indexes if missing
2) import run/patch/spectral docs with onDuplicate=ignore
3) resolve ig_patch_members _to via ig_nodes.name -> _id
4) import patch members and patch edges
5) verify latest run summary with AQL
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
from typing import Dict, Any, List, Tuple

import requests


DOC = 2
EDGE = 3


def env(name: str, alt: str = "") -> str:
    return os.environ.get(name) or (os.environ.get(alt) if alt else "")


def arango_ctx(args) -> Tuple[str, str, Tuple[str, str]]:
    endpoint = (args.endpoint or env("ARANGO_ENDPOINT") or "http://127.0.0.1:8530").rstrip("/")
    database = args.database or env("ARANGO_DATABASE") or "infogeometry"
    user = args.user or env("ARANGO_USER", "ARANGO_USERNAME")
    passwd = args.password or env("ARANGO_PASS", "ARANGO_PASSWORD")
    if not user or not passwd:
        raise SystemExit("Missing Arango credentials (ARANGO_USER/ARANGO_PASS or aliases).")
    return endpoint, database, (user, passwd)


def req_json(method: str, url: str, auth, **kwargs) -> Dict[str, Any]:
    r = requests.request(method, url, auth=auth, timeout=120, **kwargs)
    r.raise_for_status()
    return r.json()


def ensure_collections(endpoint: str, db: str, auth, verbose: bool = True) -> None:
    base = f"{endpoint}/_db/{db}/_api"
    existing = req_json("GET", f"{base}/collection", auth).get("result", [])
    existing_names = {c["name"] for c in existing}

    defs = [
        ("ig_patch_runs", DOC),
        ("ig_chiral_patches", DOC),
        ("ig_patch_spectral_signatures", DOC),
        ("ig_patch_members", EDGE),
        ("ig_patch_edges", EDGE),
    ]

    for name, ctype in defs:
        if name in existing_names:
            continue
        req_json("POST", f"{base}/collection", auth, json={"name": name, "type": ctype})
        if verbose:
            print(f"created collection: {name}")


def ensure_index(endpoint: str, db: str, auth, collection: str, fields: List[str], unique: bool = False) -> None:
    base = f"{endpoint}/_db/{db}/_api"
    payload = {"type": "persistent", "fields": fields, "unique": unique}
    try:
        req_json("POST", f"{base}/index?collection={collection}", auth, json=payload)
    except requests.HTTPError as e:
        # ignore duplicate index attempts
        if e.response is None or e.response.status_code not in (400, 409):
            raise


def ensure_indexes(endpoint: str, db: str, auth) -> None:
    ensure_index(endpoint, db, auth, "ig_patch_runs", ["schema_version"])
    ensure_index(endpoint, db, auth, "ig_patch_runs", ["created_at"])

    ensure_index(endpoint, db, auth, "ig_chiral_patches", ["run_id"])
    ensure_index(endpoint, db, auth, "ig_chiral_patches", ["patch_type", "level"])
    ensure_index(endpoint, db, auth, "ig_chiral_patches", ["coarse_hash"])
    ensure_index(endpoint, db, auth, "ig_chiral_patches", ["chiral_entropy"])
    ensure_index(endpoint, db, auth, "ig_chiral_patches", ["chiral_bias"])

    ensure_index(endpoint, db, auth, "ig_patch_spectral_signatures", ["run_id"])
    ensure_index(endpoint, db, auth, "ig_patch_spectral_signatures", ["patch_id"])

    ensure_index(endpoint, db, auth, "ig_patch_members", ["_from"])
    ensure_index(endpoint, db, auth, "ig_patch_members", ["_to"])
    ensure_index(endpoint, db, auth, "ig_patch_members", ["membership_type"])

    ensure_index(endpoint, db, auth, "ig_patch_edges", ["_from"])
    ensure_index(endpoint, db, auth, "ig_patch_edges", ["_to"])
    ensure_index(endpoint, db, auth, "ig_patch_edges", ["edge_type"])


def import_jsonl(endpoint: str, db: str, auth, collection: str, path: Path) -> Dict[str, Any]:
    if not path.exists():
        raise SystemExit(f"missing input file: {path}")
    url = f"{endpoint}/_db/{db}/_api/import?collection={collection}&type=documents&onDuplicate=ignore&details=true"
    data = path.read_bytes()
    r = requests.post(url, auth=auth, headers={"Content-Type": "text/plain"}, data=data, timeout=300)
    r.raise_for_status()
    return r.json()


def fetch_name_to_id(endpoint: str, db: str, auth) -> Dict[str, str]:
    base = f"{endpoint}/_db/{db}/_api/cursor"
    q = "FOR n IN ig_nodes FILTER HAS(n,'name') RETURN {name:n.name,id:n._id}"
    data = req_json("POST", base, auth, json={"query": q, "batchSize": 5000})
    rows = data.get("result", [])
    while data.get("hasMore"):
        cid = data["id"]
        data = req_json("PUT", f"{base}/{cid}", auth)
        rows.extend(data.get("result", []))
    return {r["name"]: r["id"] for r in rows if r.get("name") and r.get("id")}


def resolve_members(in_path: Path, out_path: Path, name_to_id: Dict[str, str]) -> Dict[str, int]:
    kept = dropped = 0
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with in_path.open("r", encoding="utf-8") as src, out_path.open("w", encoding="utf-8") as out:
        for line in src:
            line = line.strip()
            if not line:
                continue
            obj = json.loads(line)
            to = obj.get("_to", "")
            decl_name = obj.get("decl_name")
            if to.startswith("ig_nodes/decl_"):
                decl = str(decl_name or to[len("ig_nodes/decl_"):].replace("_", "."))
                rid = name_to_id.get(decl)
                if not rid:
                    dropped += 1
                    continue
                obj["_to"] = rid
            kept += 1
            out.write(json.dumps(obj, ensure_ascii=False) + "\n")
    return {"kept": kept, "dropped": dropped}


def verify_latest_summary(endpoint: str, db: str, auth) -> Dict[str, Any]:
    base = f"{endpoint}/_db/{db}/_api/cursor"
    q = '''
LET latestDoc = FIRST(FOR r IN ig_patch_runs SORT r.created_at DESC LIMIT 1 RETURN r)
LET runCandidates = UNIQUE([latestDoc._key, latestDoc.run_id, latestDoc.legacy_run_id])
LET matchedCandidate = FIRST(
  FOR rid IN runCandidates
    FILTER rid != null
    FILTER LENGTH(FOR p IN ig_chiral_patches FILTER p.run_id == rid LIMIT 1 RETURN 1) > 0
    RETURN rid
)
LET effectiveRun = matchedCandidate ? matchedCandidate : FIRST(FOR p IN ig_chiral_patches SORT p.run_id DESC LIMIT 1 RETURN p.run_id)
LET patchKeys = (FOR p IN ig_chiral_patches FILTER p.run_id == effectiveRun RETURN p._key)
LET pcount = LENGTH(patchKeys)
LET scount = LENGTH(FOR s IN ig_patch_spectral_signatures FILTER s.patch_id IN patchKeys RETURN 1)
LET mcount = LENGTH(FOR m IN ig_patch_members FILTER PARSE_IDENTIFIER(m._from).key IN patchKeys RETURN 1)
LET ecount = LENGTH(FOR e IN ig_patch_edges FILTER PARSE_IDENTIFIER(e._from).key IN patchKeys RETURN 1)
RETURN {
  latest_run_key: latestDoc._key,
  latest_run_created_at: latestDoc.created_at,
  effective_run_id: effectiveRun,
  used_fallback_run: matchedCandidate == null,
  patches: pcount,
  spectral: scount,
  members: mcount,
  patch_edges: ecount
}
'''
    res = req_json("POST", base, auth, json={"query": q}).get("result", [])
    return res[0] if res else {}


def main() -> None:
    ap = argparse.ArgumentParser(description="Ingest chiral sidecar artifacts into ArangoDB")
    ap.add_argument("--endpoint", default="")
    ap.add_argument("--database", default="")
    ap.add_argument("--user", default="")
    ap.add_argument("--password", default="")
    ap.add_argument("--dir", default="artifacts/dag/index", help="directory with ig_*.jsonl files")
    ap.add_argument("--print-json", action="store_true")
    args = ap.parse_args()

    endpoint, db, auth = arango_ctx(args)
    d = Path(args.dir)

    ensure_collections(endpoint, db, auth, verbose=not args.print_json)
    ensure_indexes(endpoint, db, auth)

    imports = {}
    imports["ig_patch_runs"] = import_jsonl(endpoint, db, auth, "ig_patch_runs", d / "ig_patch_runs.jsonl")
    imports["ig_chiral_patches"] = import_jsonl(endpoint, db, auth, "ig_chiral_patches", d / "ig_chiral_patches.jsonl")
    imports["ig_patch_spectral_signatures"] = import_jsonl(endpoint, db, auth, "ig_patch_spectral_signatures", d / "ig_patch_spectral_signatures.jsonl")

    name_to_id = fetch_name_to_id(endpoint, db, auth)
    resolved_path = d / "ig_patch_members_resolved.jsonl"
    member_stats = resolve_members(d / "ig_patch_members.jsonl", resolved_path, name_to_id)

    imports["ig_patch_members"] = import_jsonl(endpoint, db, auth, "ig_patch_members", resolved_path)
    imports["ig_patch_edges"] = import_jsonl(endpoint, db, auth, "ig_patch_edges", d / "ig_patch_edges.jsonl")

    summary = verify_latest_summary(endpoint, db, auth)

    out = {
        "ok": True,
        "endpoint": endpoint,
        "database": db,
        "member_resolution": {"mapped_nodes": len(name_to_id), **member_stats},
        "imports": {
            k: {"created": v.get("created", 0), "ignored": v.get("ignored", 0), "errors": v.get("errors", 0)}
            for k, v in imports.items()
        },
        "latest_summary": summary,
        "resolved_members_file": str(resolved_path),
    }

    if args.print_json:
        print(json.dumps(out, ensure_ascii=False))
    else:
        print(json.dumps(out, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
