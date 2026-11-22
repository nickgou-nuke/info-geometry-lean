#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any
from urllib.error import URLError

REPO_ROOT = Path(__file__).resolve().parents[2]
for _path in (str(REPO_ROOT), str(REPO_ROOT / "src")):
    if _path not in sys.path:
        sys.path.insert(0, _path)

from igf.common.json_io import read_jsonl  # noqa: E402
from igf.config.env_aliases import (  # noqa: E402
    alexandria_arango_database,
    alexandria_arango_endpoint,
    alexandria_arango_password,
    alexandria_arango_username,
    guard_alexandria_target,
    load_alexandria_arango_env,
)
from igf.graph.arango_http import ArangoHttpTarget, execute_aql  # noqa: E402

AUTHORITY = "retrieval_context_only"
DISCLAIMER = "Retrieval and navigation context only; NOT verified Lean proof evidence."


def tokenize(text: str) -> set[str]:
    return {tok.lower() for tok in re.findall(r"[A-Za-z][A-Za-z0-9_]{2,}", text)}


def safe_search_terms(query: str) -> list[str]:
    """Extract identifier terms without splitting letter-digit boundaries."""
    terms: list[str] = []
    seen: set[str] = set()
    for ident in re.findall(r"[A-Za-z][A-Za-z0-9_.']{2,}", query):
        cleaned = ident.strip(".'").lower()
        if len(cleaned) >= 3 and cleaned not in seen:
            seen.add(cleaned)
            terms.append(cleaned)
        if "." in cleaned or "_" in cleaned:
            for part in re.split(r"[._']+", cleaned):
                if len(part) >= 3 and any(ch.isalpha() for ch in part) and part not in seen:
                    seen.add(part)
                    terms.append(part)
    return terms[:24]


def score(query_tokens: set[str], chunk: dict[str, Any]) -> tuple[int, int]:
    tokens = set(chunk.get("tokens", []))
    if not tokens:
        tokens = tokenize(f"{chunk.get('title', '')} {chunk.get('text', '')}")
    overlap = query_tokens & tokens
    return (len(overlap), len(tokens))


def _compact_chunk(chunk: dict[str, Any]) -> dict[str, Any]:
    out = dict(chunk)
    out.pop("_rev", None)
    if "rawContent" in out and "text" in out:
        out.pop("rawContent", None)
    out.setdefault("sourceAuthority", AUTHORITY)
    return out


def _compact_doc(doc: dict[str, Any] | None) -> dict[str, Any] | None:
    if not isinstance(doc, dict):
        return None
    return {
        "_key": doc.get("_key"),
        "title": doc.get("title"),
        "path": doc.get("path"),
        "contentHash": doc.get("contentHash"),
        "sourceType": doc.get("sourceType"),
        "sourceKind": doc.get("sourceKind"),
        "sourceFormat": doc.get("sourceFormat"),
        "sourceAuthority": doc.get("sourceAuthority") or AUTHORITY,
        "pageCount": doc.get("pageCount"),
    }


def _build_source(chunk: dict[str, Any], doc: dict[str, Any] | None) -> dict[str, Any]:
    prov = dict(chunk.get("provenance") or {})
    if isinstance(doc, dict):
        for field in ("path", "contentHash", "sourceKind", "sourceFormat", "sourceUri", "title"):
            if prov.get(field) is None and doc.get(field) is not None:
                prov[field] = doc[field]
    prov.setdefault("sourceAuthority", AUTHORITY)
    return prov


def _normalize_hit(
    *,
    chunk: dict[str, Any],
    doc: dict[str, Any] | None,
    hit_score: float,
    score_breakdown: dict[str, Any],
    entities: list[dict[str, Any]],
    neighbors: list[dict[str, Any]],
    dag_neighbors: list[dict[str, Any]],
) -> dict[str, Any]:
    compact_chunk = _compact_chunk(chunk)
    compact_doc = _compact_doc(doc)
    source = _build_source(compact_chunk, compact_doc)
    document_key = compact_chunk.get("documentKey") or (compact_doc or {}).get("_key") or ""
    title = compact_chunk.get("title") or (compact_doc or {}).get("title") or source.get("title") or ""
    path = source.get("path") or (compact_doc or {}).get("path") or ""
    content_hash = source.get("contentHash") or (compact_doc or {}).get("contentHash") or ""
    return {
        "chunk": compact_chunk,
        "source": source,
        "document": compact_doc,
        "documentKey": document_key,
        "chunkKey": compact_chunk.get("_key") or "",
        "title": title,
        "path": path,
        "contentHash": content_hash,
        "pageStart": source.get("pageStart"),
        "pageEnd": source.get("pageEnd"),
        "chunkKind": compact_chunk.get("chunkKind"),
        "score": hit_score,
        "scoreBreakdown": score_breakdown,
        "entities": entities,
        "neighbors": neighbors,
        "dagNeighbors": dag_neighbors,
        "authority": AUTHORITY,
        "sourceAuthority": AUTHORITY,
    }


def _empty_packet(
    query: str,
    *,
    mode: str,
    target: dict[str, str] | None = None,
) -> dict[str, Any]:
    packet: dict[str, Any] = {
        "authority": AUTHORITY,
        "sourceAuthority": AUTHORITY,
        "disclaimer": DISCLAIMER,
        "mode": mode,
        "query": query,
        "queryTokens": sorted(tokenize(query)),
        "hits": [],
    }
    if target is not None:
        packet["target"] = target
    return packet


def retrieve_jsonl_context(
    input_dir: Path,
    query: str,
    *,
    top_k: int = 8,
    hops: int = 1,
) -> dict[str, Any]:
    if top_k < 0:
        raise ValueError("top_k must be >= 0")
    if not input_dir.exists() or not input_dir.is_dir():
        raise FileNotFoundError(f"Alexandria input directory does not exist: {input_dir}")
    chunks_path = input_dir / "alexandria_chunks.jsonl"
    if not chunks_path.exists():
        raise FileNotFoundError(f"Required artifact missing: {chunks_path}")

    if not query.strip() or top_k == 0:
        return _empty_packet(query, mode="jsonl")

    chunks = read_jsonl(chunks_path)
    documents = read_jsonl(input_dir / "alexandria_documents.jsonl")
    sections = read_jsonl(input_dir / "alexandria_sections.jsonl")
    entities = read_jsonl(input_dir / "alexandria_entities.jsonl")
    chunk_entities = read_jsonl(input_dir / "alexandria_chunk_entity_edges.jsonl")
    adjacent = read_jsonl(input_dir / "alexandria_chunk_adjacent_edges.jsonl")
    dag_edges = read_jsonl(input_dir / "alexandria_dag_edges.jsonl")

    query_tokens = tokenize(query)
    if not query_tokens:
        return _empty_packet(query, mode="jsonl")

    def _rank_key(row: dict[str, Any]) -> tuple[float, int, int]:
        lex, tok_len = score(query_tokens, row)
        title_low = str(row.get("title", "")).lower()
        title_hits = sum(1 for tok in query_tokens if tok in title_low)
        total = float(lex) + (0.5 * title_hits if lex > 0 else 0.0)
        return (total, lex, tok_len)

    ranked = sorted(chunks, key=_rank_key, reverse=True)
    top = [row for row in ranked if _rank_key(row)[1] > 0][:top_k]

    doc_by_key = {row["_key"]: row for row in documents if row.get("_key")}
    section_by_key = {row["_key"]: row for row in sections if row.get("_key")}
    entity_by_key = {row["_key"]: row for row in entities if row.get("_key")}
    chunk_by_key = {row["_key"]: row for row in chunks if row.get("_key")}

    entities_for_chunk: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for edge in chunk_entities:
        chunk_key = str(edge.get("_from", "")).split("/", 1)[-1]
        entity_key = str(edge.get("_to", "")).split("/", 1)[-1]
        entity = entity_by_key.get(entity_key)
        if entity:
            entities_for_chunk[chunk_key].append(entity)

    neighbor_map: dict[str, list[str]] = defaultdict(list)
    for edge in adjacent:
        src = str(edge.get("_from", "")).split("/", 1)[-1]
        dst = str(edge.get("_to", "")).split("/", 1)[-1]
        if src and dst:
            neighbor_map[src].append(dst)
            neighbor_map[dst].append(src)

    dag_adj: dict[str, list[tuple[str, dict[str, Any], str]]] = defaultdict(list)
    for edge in dag_edges:
        src = str(edge.get("_from", ""))
        dst = str(edge.get("_to", ""))
        if src and dst:
            dag_adj[src].append((dst, edge, "outbound"))
            dag_adj[dst].append((src, edge, "inbound"))

    def _lookup_node(doc_id: str) -> dict[str, Any] | None:
        if "/" not in doc_id:
            return None
        col, key = doc_id.split("/", 1)
        if col == "alexandria_chunks":
            return chunk_by_key.get(key)
        if col == "alexandria_entities":
            return entity_by_key.get(key)
        if col == "alexandria_documents":
            return doc_by_key.get(key)
        if col == "alexandria_sections":
            return section_by_key.get(key)
        return None

    def _collect_dag_neighbors(chunk_key: str) -> list[dict[str, Any]]:
        start_id = f"alexandria_chunks/{chunk_key}"
        visited = {start_id}
        frontier = [start_id]
        collected: list[dict[str, Any]] = []
        for _ in range(max(1, min(3, hops))):
            next_frontier: list[str] = []
            for cur in frontier:
                for nxt, edge, direction in dag_adj.get(cur, []):
                    if nxt in visited:
                        continue
                    visited.add(nxt)
                    next_frontier.append(nxt)
                    target_node = _lookup_node(nxt) or {}
                    collected.append(
                        {
                            "_key": target_node.get("_key") or nxt.split("/", 1)[-1],
                            "_id": nxt,
                            "documentKey": target_node.get("documentKey"),
                            "chunkKind": target_node.get("chunkKind"),
                            "entityType": target_node.get("entityType"),
                            "surface": target_node.get("surface"),
                            "normalized": target_node.get("normalized"),
                            "title": target_node.get("title"),
                            "text": str(target_node["text"])[:320] if isinstance(target_node.get("text"), str) else None,
                            "provenance": target_node.get("provenance"),
                            "edgeType": edge.get("edgeType"),
                            "evidence": edge.get("evidence"),
                            "confidence": edge.get("confidence"),
                            "direction": direction,
                        }
                    )
                    if len(collected) >= 8:
                        return collected
            frontier = next_frontier
            if not frontier:
                break
        return collected

    hits: list[dict[str, Any]] = []
    for chunk in top:
        lex, _ = score(query_tokens, chunk)
        title_low = str(chunk.get("title", "")).lower()
        title_flag = 1 if any(t in title_low for t in query_tokens) else 0
        total_score = float(lex) + 0.5 * sum(1 for t in query_tokens if t in title_low)
        doc = doc_by_key.get(str(chunk.get("documentKey") or ""))
        adj_hits = [_compact_chunk(chunk_by_key[n]) for n in neighbor_map.get(chunk["_key"], []) if n in chunk_by_key][:4]
        dag_hits = _collect_dag_neighbors(chunk["_key"])
        hits.append(
            _normalize_hit(
                chunk=chunk,
                doc=doc,
                hit_score=total_score,
                score_breakdown={"lexical": lex, "title": title_flag},
                entities=entities_for_chunk.get(chunk["_key"], []),
                neighbors=adj_hits,
                dag_neighbors=dag_hits,
            )
        )

    packet = _empty_packet(query, mode="jsonl")
    packet["hits"] = hits
    return packet


ARANGO_RETRIEVE_AQL = """
LET qTokens = TOKENS(@q, "text_en")
FOR c IN alexandria_chunks_search
SEARCH (
    LENGTH(qTokens) > 0 AND (
        ANALYZER(c.text IN qTokens, "text_en")
        OR BOOST(ANALYZER(c.title IN qTokens, "text_en"), 2.0)
    )
) OR (LENGTH(@terms) > 0 AND c.searchTerms IN @terms)
OPTIONS {waitForSync: true}
LET bm25Score = BM25(c)
SORT bm25Score DESC
LIMIT @limit
LET doc = c.documentKey != null ? DOCUMENT(CONCAT("alexandria_documents/", c.documentKey)) : null
LET entities = (
    FOR e IN alexandria_chunk_entity_edges
    FILTER e._from == c._id
    LIMIT 12
    LET ent = DOCUMENT(e._to)
    FILTER ent != null
    RETURN ent
)
LET adjNeighbors = (
    FOR v, e IN 1..1 ANY c._id alexandria_chunk_adjacent_edges
    FILTER v != null
    LIMIT 4
    RETURN {
        _key: v._key,
        _id: v._id,
        documentKey: v.documentKey,
        chunkKind: v.chunkKind,
        title: v.title,
        text: IS_STRING(v.text) ? SUBSTRING(v.text, 0, 320) : null,
        provenance: v.provenance,
        edgeType: e.kind != null ? e.kind : "adjacent",
        direction: e._from == c._id ? "outbound" : "inbound"
    }
)
LET dagNeighbors = (
    FOR v, e IN 1..@hops ANY c._id alexandria_dag_edges
    OPTIONS {uniqueVertices: "global", bfs: true}
    FILTER v != null
    LIMIT 8
    RETURN {
        _key: v._key,
        _id: v._id,
        documentKey: v.documentKey,
        chunkKind: v.chunkKind,
        entityType: v.entityType,
        surface: v.surface,
        normalized: v.normalized,
        title: v.title,
        text: IS_STRING(v.text) ? SUBSTRING(v.text, 0, 320) : null,
        provenance: v.provenance,
        edgeType: e.edgeType,
        evidence: e.evidence,
        confidence: e.confidence,
        direction: e._to == v._id ? "outbound" : "inbound"
    }
)
RETURN {
    chunk: c,
    document: doc,
    score: bm25Score,
    entities: entities,
    adjNeighbors: adjNeighbors,
    dagNeighbors: dagNeighbors
}
""".strip()


def retrieve_arango_context(
    query: str,
    *,
    endpoint: str | None = None,
    database: str | None = None,
    username: str | None = None,
    password: str | None = None,
    top_k: int = 8,
    hops: int = 1,
) -> dict[str, Any]:
    load_alexandria_arango_env(REPO_ROOT)
    resolved_endpoint = (endpoint or alexandria_arango_endpoint()).rstrip("/")
    resolved_database = database or alexandria_arango_database()
    resolved_username = username or alexandria_arango_username()
    resolved_password = password if password is not None else alexandria_arango_password("alexandria_root")

    guard_alexandria_target(resolved_endpoint, resolved_database)
    if top_k < 0:
        raise ValueError("top_k must be >= 0")
    clamped_hops = max(1, min(3, int(hops)))

    target_meta = {"endpoint": resolved_endpoint, "database": resolved_database}
    if not query.strip() or top_k == 0:
        return _empty_packet(query, mode="arango", target=target_meta)

    terms = safe_search_terms(query)
    query_tokens = tokenize(query)
    if not query_tokens and not terms:
        # Punctuation-only queries still verify connectivity if needed; check query text tokens.
        pass

    target = ArangoHttpTarget(
        endpoint=resolved_endpoint,
        database=resolved_database,
        username=resolved_username,
        password=resolved_password,
    )
    rows = execute_aql(
        target,
        ARANGO_RETRIEVE_AQL,
        bind_vars={
            "q": query,
            "terms": terms,
            "limit": int(top_k),
            "hops": clamped_hops,
        },
        timeout=15.0,
    )

    hits: list[dict[str, Any]] = []
    for row in rows:
        if not isinstance(row, dict):
            continue
        chunk = row.get("chunk")
        if not isinstance(chunk, dict):
            continue
        doc = row.get("document") if isinstance(row.get("document"), dict) else None
        bm25_score = float(row.get("score") or 0.0)
        lex, _ = score(query_tokens, chunk)
        title_low = str(chunk.get("title", "")).lower()
        title_flag = 1 if any(t in title_low for t in query_tokens) else 0
        entities = [e for e in (row.get("entities") or []) if isinstance(e, dict)]
        adj_neighbors = [n for n in (row.get("adjNeighbors") or []) if isinstance(n, dict)]
        dag_neighbors = [n for n in (row.get("dagNeighbors") or []) if isinstance(n, dict)]
        hits.append(
            _normalize_hit(
                chunk=chunk,
                doc=doc,
                hit_score=bm25_score,
                score_breakdown={"bm25": bm25_score, "lexical": lex, "title": title_flag},
                entities=entities,
                neighbors=adj_neighbors,
                dag_neighbors=dag_neighbors,
            )
        )

    hits.sort(key=lambda h: float(h.get("score") or 0.0), reverse=True)
    packet = _empty_packet(query, mode="arango", target=target_meta)
    packet["hits"] = hits
    return packet


def format_text_packet(packet: dict[str, Any]) -> str:
    lines = [
        f"[AUTHORITY: {packet.get('authority', AUTHORITY)} — {packet.get('disclaimer', DISCLAIMER)}]",
        f"Query: {packet.get('query', '')}",
        f"Mode: {packet.get('mode', 'unknown')} | Hits: {len(packet.get('hits', []))}",
        "",
    ]
    for idx, hit in enumerate(packet.get("hits", []), start=1):
        chunk = hit.get("chunk") or {}
        score_val = float(hit.get("score") or 0.0)
        title = hit.get("title") or "(untitled)"
        path = hit.get("path") or ""
        p_start = hit.get("pageStart")
        p_end = hit.get("pageEnd")
        pages = f"p.{p_start}" + (f"-{p_end}" if p_end is not None and p_end != p_start else "") if p_start is not None else "p.?"
        kind = hit.get("chunkKind") or "chunk"
        doc_key = hit.get("documentKey") or ""
        chash = str(hit.get("contentHash") or "")[:12]
        lines.append(f"{idx}. [{score_val:.3f}] {title} ({path} {pages}, kind={kind}, doc={doc_key}, sha256={chash})")
        snippet = str(chunk.get("text") or "").strip().replace("\n", " ")
        if snippet:
            lines.append(f"   text: {snippet[:320]}")
        ents = [str(e.get("surface") or e.get("normalized") or "") for e in (hit.get("entities") or [])[:6] if e]
        if ents:
            lines.append(f"   entities: {', '.join(ents)}")
        dags = [
            f"{d.get('edgeType', 'dag')}({d.get('direction', '?')})->{d.get('title') or d.get('surface') or d.get('_key')}"
            for d in (hit.get("dagNeighbors") or [])[:4]
        ]
        if dags:
            lines.append(f"   dagNeighbors: {'; '.join(dags)}")
    return "\n".join(lines) + "\n"


def parse_args(argv: list[str] | None = None) -> tuple[argparse.ArgumentParser, argparse.Namespace]:
    ap = argparse.ArgumentParser(description="Retrieve Alexandria context from local JSONL artifacts or live ArangoDB")
    ap.add_argument("--query", required=True)
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--input-dir", type=Path)
    mode.add_argument("--arango", action="store_true")
    ap.add_argument("--endpoint", default=None)
    ap.add_argument("--database", default=None)
    ap.add_argument("--username", default=None)
    ap.add_argument("--password", default=None)
    ap.add_argument("--top-k", type=int, default=8)
    ap.add_argument("--limit", type=int, default=None, help="Alias overriding --top-k")
    ap.add_argument("--hops", type=int, default=1)
    ap.add_argument("--format", choices=("json", "text"), default="json")
    args = ap.parse_args(argv)
    if args.top_k < 0:
        ap.error("--top-k must be >= 0")
    if args.limit is not None and args.limit < 0:
        ap.error("--limit must be >= 0")
    if args.hops < 1:
        ap.error("--hops must be >= 1")
    return ap, args


def main(argv: list[str] | None = None) -> int:
    load_alexandria_arango_env(REPO_ROOT)
    _, args = parse_args(argv)
    top_k = args.limit if args.limit is not None else args.top_k

    if args.arango:
        endpoint = (args.endpoint or alexandria_arango_endpoint()).rstrip("/")
        database = args.database or alexandria_arango_database()
        username = args.username or alexandria_arango_username()
        password = args.password if args.password is not None else alexandria_arango_password("alexandria_root")
        try:
            guard_alexandria_target(endpoint, database)
        except ValueError as exc:
            print(json.dumps({"error": str(exc)}, ensure_ascii=False), file=sys.stderr)
            return 2
        try:
            packet = retrieve_arango_context(
                args.query,
                endpoint=endpoint,
                database=database,
                username=username,
                password=password,
                top_k=top_k,
                hops=args.hops,
            )
        except (URLError, OSError, RuntimeError, ValueError) as exc:
            print(json.dumps({"error": f"ArangoDB retrieval failed: {exc}"}, ensure_ascii=False), file=sys.stderr)
            return 1
    else:
        try:
            packet = retrieve_jsonl_context(args.input_dir, args.query, top_k=top_k, hops=args.hops)
        except FileNotFoundError as exc:
            print(json.dumps({"error": str(exc)}, ensure_ascii=False), file=sys.stderr)
            return 1

    if args.format == "text":
        sys.stdout.write(format_text_packet(packet))
    else:
        print(json.dumps(packet, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
