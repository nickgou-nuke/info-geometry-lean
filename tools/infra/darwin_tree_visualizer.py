#!/usr/bin/env python3
"""Export a read-only, interactive commit-DAG view enriched with DNA fingerprints.

The tool joins separate Arango databases in the application process (never with
cross-database AQL), validates the join mode explicitly, and emits JSON plus an
interactive Cytoscape HTML page. Fingerprint fields are allow-listed so raw
sequences are not exported unless the operator explicitly requests them.
"""
from __future__ import annotations

import argparse
import base64
import json
import os
import re
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Iterable
from urllib.error import HTTPError, URLError
from urllib.parse import quote
from urllib.request import Request, urlopen

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.infra.arango_env import (  # noqa: E402
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
    normalized_darwin_arango_env,
)

SCHEMA = "info_geometry.darwin_tree_visualization.v1"
DEFAULT_FINGERPRINT_FIELDS = (
    "_key,name,module,kind,line,file,typeFingerprint,valueFingerprint,typeDigest,valueDigest,"
    "canonicalTypeHash,canonicalValueHash,dagShapeHash"
)


def _key(doc: dict[str, Any]) -> str | None:
    for field in ("sha", "hash", "_key"):
        value = doc.get(field)
        if isinstance(value, str) and value:
            return value
    return None


def _commit_time(doc: dict[str, Any]) -> str:
    for field in ("committed_at", "committedAt", "date", "authored_at"):
        value = doc.get(field)
        if isinstance(value, str) and value:
            return value
    return ""


def _parse_datetime(value: str) -> datetime:
    try:
        return datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        # Git's legacy commit_nodes store ctime as e.g. "Thu Feb 12 22:15:00 2026 +0200".
        return datetime.strptime(value, "%a %b %d %H:%M:%S %Y %z")


def _since_match(doc: dict[str, Any], since: str | None) -> bool:
    if not since:
        return True
    timestamp = _commit_time(doc)
    if not timestamp:
        return False
    try:
        stamp = _parse_datetime(timestamp)
        try:
            boundary = _parse_datetime(since)
        except ValueError:
            relative = re.fullmatch(r"(\d+)\s+(year|month|week|day)s?\s+ago", since.strip(), re.I)
            if not relative:
                raise ValueError(f"unsupported --since expression: {since}")
            count = int(relative.group(1))
            unit_days = {"year": 365, "month": 30, "week": 7, "day": 1}[relative.group(2).lower()]
            boundary = datetime.now(timezone.utc) - timedelta(days=count * unit_days)
    except ValueError as exc:
        raise ValueError(f"invalid date in since filter: {exc}") from exc
    if stamp.tzinfo is None and boundary.tzinfo is not None:
        stamp = stamp.replace(tzinfo=boundary.tzinfo)
    if boundary.tzinfo is None and stamp.tzinfo is not None:
        boundary = boundary.replace(tzinfo=stamp.tzinfo)
    return stamp >= boundary


def _edge_endpoint(edge: dict[str, Any], field: str) -> str | None:
    value = edge.get(field)
    if isinstance(value, str):
        return value.rsplit("/", 1)[-1]
    return None


def _fingerprint_key(doc: dict[str, Any], field: str) -> str | None:
    value = doc.get(field)
    return str(value) if value is not None else None


def build_payload(
    commits: Iterable[dict[str, Any]],
    fingerprints: Iterable[dict[str, Any]],
    *,
    join_mode: str,
    fingerprint_join_field: str,
    fingerprint_fields: list[str],
    since: str | None = None,
    declaration_edges: Iterable[dict[str, Any]] = (),
    commit_edge_field: str = "commitHash",
    declaration_edge_field: str = "declKey",
) -> dict[str, Any]:
    """Normalize two data sources into a stable visualization JSON payload."""
    if join_mode not in {"direct", "declaration"}:
        raise ValueError("join_mode must be 'direct' or 'declaration'")
    if join_mode == "declaration" and not fingerprint_join_field:
        raise ValueError("declaration join requires an explicit fingerprint key field")

    selected: dict[str, dict[str, Any]] = {}
    for doc in commits:
        key = _key(doc)
        if key and _since_match(doc, since):
            selected[key] = doc
    if not selected:
        raise ValueError("no commit records matched; check source collection and date filter")

    children: dict[str, set[str]] = {key: set() for key in selected}
    parent_pairs: set[tuple[str, str]] = set()
    external_parents: dict[str, int] = {}
    for child, doc in selected.items():
        parents = doc.get("parents") or []
        if isinstance(parents, str):
            parents = parents.split()
        external = 0
        for parent in parents:
            parent_key = str(parent).rsplit("/", 1)[-1]
            if parent_key in selected:
                parent_pairs.add((parent_key, child))
                children[parent_key].add(child)
            else:
                external += 1
        external_parents[child] = external
    leaf_keys = {key for key in selected if not children[key]}

    fingerprints_by_key: dict[str, list[dict[str, Any]]] = {}
    for doc in fingerprints:
        join_key = _fingerprint_key(doc, fingerprint_join_field)
        if join_key is None:
            continue
        safe_doc = {field: doc[field] for field in fingerprint_fields if field in doc}
        safe_doc.setdefault("_key", doc.get("_key", join_key))
        fingerprints_by_key.setdefault(join_key, []).append(safe_doc)

    attached: dict[str, list[dict[str, Any]]] = {key: [] for key in selected}
    if join_mode == "direct":
        for key in leaf_keys:
            attached[key].extend(fingerprints_by_key.get(key, []))
    else:
        for edge in declaration_edges:
            commit_key = edge.get(commit_edge_field)
            if not isinstance(commit_key, str):
                commit_key = _edge_endpoint(edge, "_from")
            decl_key = edge.get(declaration_edge_field)
            if decl_key is None:
                decl_key = _edge_endpoint(edge, "_to")
            if commit_key in leaf_keys and decl_key is not None:
                rows = fingerprints_by_key.get(str(decl_key), [])
                attached[commit_key].extend({
                    **row,
                    "commit_decl_resolution": edge.get("resolution", "configured_key_match"),
                    "exact_match": edge.get("exact_match", False),
                    "moduleName": edge.get("moduleName"),
                } for row in rows)

    nodes: list[dict[str, Any]] = []
    for key, doc in selected.items():
        subject = doc.get("subject", doc.get("message", ""))
        if not isinstance(subject, str):
            subject = str(subject)
        dna = attached[key]
        churn_known = (doc.get("diff_stats_status") != "not_collected"
                       and all(type(doc.get(field)) in (int, float)
                               for field in ("insertions", "deletions")))
        nodes.append({"data": {
            "id": key,
            "label": subject[:100] or key[:12],
            "sha": key,
            "date": _commit_time(doc),
            "author": doc.get("author_name", doc.get("author", "")),
            "change_labels": doc.get("changeLabels", doc.get("labels", [])),
            "churn": doc["insertions"] + doc["deletions"] if churn_known else None,
            "churn_status": "observed" if churn_known else "unknown",
            "fingerprint_count": len(dna),
            "fingerprints": dna,
            "external_parent_count": external_parents[key],
            "is_leaf": not children[key],
        }})
    edges = [{"data": {"id": f"parent:{parent}:{child}", "source": parent,
                       "target": child, "kind": "git_parent"}}
             for parent, child in sorted(parent_pairs)]
    leaves = [key for key in selected if not children[key]]
    leaf_count = len(leaves)
    leaves_with_fingerprints = sum(bool(attached[key]) for key in leaves)
    attached_count = sum(bool(attached[key]) for key in selected)
    return {
        "schema": SCHEMA,
        "meta": {
            "join_mode": join_mode,
            "fingerprint_join_field": fingerprint_join_field,
            "since": since,
            "commit_count": len(selected),
            "parent_edge_count": len(edges),
            "leaf_count": leaf_count,
            "leaves_with_fingerprints": leaves_with_fingerprints,
            "unmatched_leaf_count": leaf_count - leaves_with_fingerprints,
            "commits_with_fingerprints": attached_count,
            "fingerprint_fields_exported": fingerprint_fields,
            "parent_direction": "older parent -> newer child",
            "truth_boundary": (
                "Git ancestry and configured fingerprint-key matches are displayed. "
                "Weak taxon labels are metadata, not biological classifications; "
                "a fingerprint match does not establish semantic equivalence."
            ),
        },
        "elements": {"nodes": nodes, "edges": edges},
    }


def _request_json(url: str, *, username: str, password: str,
                  method: str = "GET", payload: dict[str, Any] | None = None) -> Any:
    token = base64.b64encode(f"{username}:{password}".encode()).decode("ascii")
    data = json.dumps(payload).encode("utf-8") if payload is not None else None
    request = Request(url, data=data, method=method, headers={
        "Authorization": f"Basic {token}", "Content-Type": "application/json",
        "Accept": "application/json",
    })
    try:
        with urlopen(request, timeout=60) as response:
            return json.loads(response.read().decode("utf-8"))
    except (HTTPError, URLError, TimeoutError) as exc:
        raise RuntimeError(f"Arango request failed ({method} {url}): {exc}") from exc


def read_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    """Yield bridge rows incrementally; exports can be multi-gigabyte files."""
    with path.open(encoding="utf-8") as source:
        for line_number, line in enumerate(source, 1):
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"invalid declaration-edge JSONL at {path}:{line_number}: {exc}") from exc
            if isinstance(row, dict):
                yield row


def iter_collection(endpoint: str, database: str, collection: str, *,
                    username: str, password: str) -> Iterable[dict[str, Any]]:
    """Stream a read-only Arango cursor instead of materializing edge collections."""
    url = f"{endpoint.rstrip('/')}/_db/{quote(database)}/_api/cursor"
    result = _request_json(url, username=username, password=password, method="POST",
                           payload={"query": "FOR d IN @@collection RETURN d",
                                    "bindVars": {"@collection": collection},
                                    "batchSize": 1000})
    while True:
        if not isinstance(result, dict):
            raise RuntimeError(f"unexpected Arango cursor response for {collection}")
        yield from result.get("result", [])
        if not result.get("hasMore"):
            break
        cursor_id = result.get("id")
        if not cursor_id:
            raise RuntimeError(f"cursor for {collection} hasMore without id")
        result = _request_json(f"{url}/{quote(str(cursor_id))}", username=username,
                               password=password, method="PUT")


def fetch_collection(endpoint: str, database: str, collection: str, *,
                     username: str, password: str) -> list[dict[str, Any]]:
    """Materialize a small node/declaration collection; edges should be streamed."""
    return list(iter_collection(endpoint, database, collection,
                                username=username, password=password))


def render_html(payload: dict[str, Any], title: str) -> str:
    embedded = json.dumps(payload, ensure_ascii=False).replace("</", "<\\/")
    safe_title = title.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width">
<title>{safe_title}</title>
<script src="https://unpkg.com/cytoscape@3.30.4/dist/cytoscape.min.js"></script>
<style>
*{{box-sizing:border-box}}body{{margin:0;font:14px system-ui;background:#0b1020;color:#e5e7eb}}
header{{height:58px;padding:12px 18px;border-bottom:1px solid #25304a;display:flex;gap:20px;align-items:center}}
header strong{{font-size:17px}}#stats{{color:#aab6ce}}main{{display:grid;grid-template-columns:minmax(0,1fr) 350px;height:calc(100vh - 58px)}}
#cy{{width:100%;height:100%;background:radial-gradient(#1a2540 1px,transparent 1px);background-size:22px 22px}}
aside{{padding:16px;overflow:auto;border-left:1px solid #25304a;background:#10182b}}aside h2{{font-size:16px;margin:0 0 12px}}
.item{{padding:10px;margin:8px 0;background:#17223a;border:1px solid #293858;border-radius:8px;overflow-wrap:anywhere}}
.muted{{color:#9ba9c4}}code{{font-size:12px;color:#8ed8d2}}input{{margin-left:auto;padding:7px 10px;background:#17223a;color:#fff;border:1px solid #354361;border-radius:6px}}
@media(max-width:800px){{main{{grid-template-columns:1fr;grid-template-rows:60vh 1fr;height:auto}}aside{{border-left:0;border-top:1px solid #25304a}}}}
</style></head><body><header><strong>{safe_title}</strong><span id="stats"></span><input id="search" placeholder="Filter commit label / SHA"></header>
<main><div id="cy"></div><aside id="details"><h2>Commit / fingerprint details</h2><p class="muted">Select a commit node to inspect its attached fingerprint records.</p></aside></main>
<script>
const graph={embedded};
const nodes=graph.elements.nodes, edges=graph.elements.edges;
document.getElementById('stats').textContent=`${{graph.meta.commit_count}} commits · ${{graph.meta.parent_edge_count}} parent links · ${{graph.meta.leaf_count}} leaves · ${{graph.meta.commits_with_fingerprints}} matched`;
const cy=cytoscape({{container:document.getElementById('cy'),elements:[...nodes,...edges],
  style:[
    {{selector:'node',style:{{'label':'data(label)','font-size':9,'color':'#e5e7eb','text-wrap':'wrap','text-max-width':110,'text-valign':'bottom','text-margin-y':5,'background-color':'#5b7cfa','width': 'mapData(fingerprint_count, 0, 5, 13, 30)','height':'mapData(fingerprint_count, 0, 5, 13, 30)','border-width': 'mapData(is_leaf, false, true, 0, 3)','border-color':'#f5c451'}}}},
    {{selector:'edge',style:{{'curve-style':'bezier','target-arrow-shape':'triangle','target-arrow-color':'#7585a6','line-color':'#43516d','width':1.2,'arrow-scale':0.7}}}},
    {{selector:':selected',style:{{'background-color':'#ff8b5e','line-color':'#ff8b5e','target-arrow-color':'#ff8b5e'}}}}
  ],layout:{{name:'breadthfirst',directed:true,roots:nodes.filter(n=>!edges.some(e=>e.data.target===n.data.id)).map(n=>n.data.id),spacingFactor:1.15,padding:30,animate:false}}}});
cy.on('tap','node',evt=>{{const d=evt.target.data(),box=document.getElementById('details');
  const fps=d.fingerprints||[];
  box.innerHTML=''; const h=document.createElement('h2');h.textContent=d.label||d.sha;box.appendChild(h);
  for(const [k,v] of Object.entries({{sha:d.sha,date:d.date,author:d.author,churn:d.churn??'unknown',leaf:d.is_leaf,external_parents:d.external_parent_count,change_labels:d.change_labels}})){{const p=document.createElement('p');p.className='muted';p.textContent=k+': '+(typeof v==='object'?JSON.stringify(v):String(v??''));box.appendChild(p)}}
  const fh=document.createElement('h2');fh.textContent='DNA fingerprints ('+fps.length+')';box.appendChild(fh);
  if(!fps.length){{const p=document.createElement('p');p.className='muted';p.textContent='No record matched the configured key.';box.appendChild(p)}}
  for(const fp of fps){{const card=document.createElement('div');card.className='item';for(const [k,v] of Object.entries(fp)){{const row=document.createElement('div');row.textContent=k+': '+(typeof v==='object'?JSON.stringify(v):String(v));card.appendChild(row)}}box.appendChild(card)}}
}});
document.getElementById('search').addEventListener('input',ev=>{{const q=ev.target.value.toLowerCase();cy.nodes().forEach(n=>{{const d=n.data();const hit=!q||(d.label+' '+d.sha).toLowerCase().includes(q);n.style('display',hit?'element':'none')}});cy.edges().forEach(e=>e.style('display',e.source().style('display')==='none'||e.target().style('display')==='none'?'none':'element'))}});
</script></body></html>'''


def _identity(prefix: str) -> tuple[str, str, str]:
    return (os.environ.get(f"{prefix}_ARANGO_ENDPOINT", arango_endpoint()),
            os.environ.get(f"{prefix}_ARANGO_DATABASE", arango_database()),
            os.environ.get(f"{prefix}_ARANGO_USER", arango_username()))


def main() -> int:
    load_repo_arango_env(REPO_ROOT)
    darwin_config = normalized_darwin_arango_env()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--commit-database", default=darwin_config["database"])
    parser.add_argument("--commit-collection", default="commit_nodes",
                        help="Use commit_nodes or evo_commits; parent ids are read from each document's parents")
    parser.add_argument("--commit-endpoint", default=darwin_config["endpoint"])
    parser.add_argument("--commit-edge-collection", default="commit_decl_edges",
                        help="Commit-to-declaration links; used only with --join-mode declaration")
    parser.add_argument("--declaration-edges-jsonl", type=Path,
                        help="read declaration links from local JSONL instead of the Arango edge collection")
    parser.add_argument("--dna-endpoint", default=os.environ.get("DNA_ARANGO_ENDPOINT", arango_endpoint()))
    parser.add_argument("--dna-database", default=os.environ.get("DNA_ARANGO_DATABASE", ""))
    parser.add_argument("--dna-collection", required=True)
    parser.add_argument("--join-mode", choices=("direct", "declaration"), required=True,
                        help="Join DNA records by commit id, or through commit_decl_edges")
    parser.add_argument("--fingerprint-join-field", required=True,
                        help="Field in DNA documents matching commit id (direct) or declKey (declaration)")
    parser.add_argument("--decl-edge-commit-field", default="commitHash")
    parser.add_argument("--decl-edge-key-field", default="declKey")
    parser.add_argument("--fingerprint-fields", default=DEFAULT_FINGERPRINT_FIELDS,
                        help="Comma-separated output fields (default is limited to declaration identity and versioned fingerprints)")
    parser.add_argument("--since", help="Optional ISO-8601 lower bound, e.g. 2025-01-01T00:00:00Z")
    parser.add_argument("--json-out", type=Path, default=Path("darwin_tree.json"))
    parser.add_argument("--html-out", type=Path, default=Path("darwin_tree.html"))
    parser.add_argument("--title", default="Repository commit tree + DNA fingerprints")
    args = parser.parse_args()

    commit_identity = (args.commit_endpoint, args.commit_database,
                       darwin_config["user"], darwin_config["password"])
    dna_database = args.dna_database or os.environ.get("ARANGO_DATABASE", arango_database())
    dna_identity = (args.dna_endpoint, dna_database,
                    os.environ.get("DNA_ARANGO_USER", arango_username()),
                    os.environ.get("DNA_ARANGO_PASS", arango_password()))
    commits = fetch_collection(commit_identity[0], commit_identity[1], args.commit_collection,
                               username=commit_identity[2], password=commit_identity[3])
    fingerprints = fetch_collection(dna_identity[0], dna_identity[1], args.dna_collection,
                                   username=dna_identity[2], password=dna_identity[3])
    decl_edges: Iterable[dict[str, Any]] = ()
    if args.join_mode == "declaration":
        if args.declaration_edges_jsonl:
            decl_edges = read_jsonl(args.declaration_edges_jsonl)
        else:
            decl_edges = iter_collection(commit_identity[0], commit_identity[1],
                                         args.commit_edge_collection,
                                         username=commit_identity[2], password=commit_identity[3])
    fields = [field.strip() for field in args.fingerprint_fields.split(",") if field.strip()]
    payload = build_payload(
        commits, fingerprints, join_mode=args.join_mode,
        fingerprint_join_field=args.fingerprint_join_field,
        fingerprint_fields=fields, since=args.since, declaration_edges=decl_edges,
        commit_edge_field=args.decl_edge_commit_field,
        declaration_edge_field=args.decl_edge_key_field,
    )
    payload["meta"].update({
        "commit_database": args.commit_database,
        "commit_collection": args.commit_collection,
        "dna_database": dna_database,
        "dna_collection": args.dna_collection,
        "external_database_aql": False,
    })
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.html_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    args.html_out.write_text(render_html(payload, args.title), encoding="utf-8")
    print(json.dumps({"json": str(args.json_out), "html": str(args.html_out), **payload["meta"]},
                     ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
