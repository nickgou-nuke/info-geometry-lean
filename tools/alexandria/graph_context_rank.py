#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
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
from tools.alexandria.retrieve_context import (  # noqa: E402
    AUTHORITY,
    DISCLAIMER,
    _build_source,
    _compact_chunk,
    _compact_doc,
    safe_search_terms,
)

ANCHOR_ENTITY_TYPES = {"theorem", "theorem_name", "module"}
WEAK_ENTITY_TYPES = {"tooling", "symbol"}


def maybe_enable_gpu_backend(use_gpu: bool) -> None:
    if not use_gpu:
        return
    os.environ.setdefault("NETWORKX_BACKEND_PRIORITY_ALGOS", "cugraph")
    os.environ.setdefault("NETWORKX_BACKEND_PRIORITY_GENERATORS", "cugraph")
    os.environ.setdefault("NETWORKX_FALLBACK_TO_NX", "true")
    os.environ.setdefault("NETWORKX_CACHE_CONVERTED_GRAPHS", "true")


def tokenize(text: str) -> set[str]:
    return {tok.lower() for tok in re.findall(r"[A-Za-z][A-Za-z0-9_]{2,}", text)}


def lexical_score(query_tokens: set[str], chunk: dict[str, Any]) -> int:
    tokens = set(chunk.get("tokens", []))
    if not tokens:
        tokens = tokenize(f"{chunk.get('title', '')} {chunk.get('text', '')}")
    return len(query_tokens & tokens)


def chunk_key_from_doc_id(doc_id: str) -> str:
    return doc_id.split("/", 1)[1] if "/" in doc_id else doc_id


def entity_bonus(entity: dict[str, Any]) -> float:
    confidence = float(entity.get("confidence", 0.5))
    entity_type = str(entity.get("entityType", ""))
    if entity_type in ANCHOR_ENTITY_TYPES:
        return 1.2 * confidence
    if entity_type in WEAK_ENTITY_TYPES:
        return 0.7 * confidence
    return 0.95 * confidence


def _debruijn_conductivity(overlap_symbols: list[str], query_tokens: set[str]) -> float:
    if not query_tokens or not overlap_symbols:
        return 0.0
    symbol_tokens: set[str] = set()
    for sym in overlap_symbols:
        symbol_tokens.update(tokenize(sym))
    return len(symbol_tokens & query_tokens) / len(query_tokens)


def add_dag_edges(graph: Any, dag_edges: list[dict[str, Any]] | None) -> None:
    if not dag_edges:
        return
    for edge in dag_edges:
        if not isinstance(edge, dict):
            continue
        raw_from = str(edge.get("_from", ""))
        raw_to = str(edge.get("_to", ""))
        if not raw_from.startswith("alexandria_chunks/") or not raw_to.startswith("alexandria_chunks/"):
            continue
        src = chunk_key_from_doc_id(raw_from)
        dst = chunk_key_from_doc_id(raw_to)
        if src == dst or src not in graph or dst not in graph:
            continue
        conf = max(0.1, float(edge.get("confidence", 0.8) or 0.8))
        edge_type = str(edge.get("edgeType") or "dag")
        cur_fwd = float(graph[src][dst]["weight"]) if graph.has_edge(src, dst) else 0.0
        if conf >= cur_fwd:
            graph.add_edge(src, dst, kind=f"dag:{edge_type}", weight=conf, edgeType=edge_type)
        rev_weight = 0.75 * conf
        cur_rev = float(graph[dst][src]["weight"]) if graph.has_edge(dst, src) else 0.0
        if rev_weight >= cur_rev:
            graph.add_edge(dst, src, kind=f"dag_reverse:{edge_type}", weight=rev_weight, edgeType=edge_type)


def build_graph(
    nx: Any,
    chunks: list[dict[str, Any]],
    entities: list[dict[str, Any]],
    chunk_entities: list[dict[str, Any]],
    adjacent: list[dict[str, Any]],
    debruijn_edges: list[dict[str, Any]],
    entity_relations: list[dict[str, Any]],
    *,
    query_tokens: set[str] | None = None,
    conductive: bool = False,
    dag_edges: list[dict[str, Any]] | None = None,
):
    graph = nx.DiGraph()
    for chunk in chunks:
        graph.add_node(chunk["_key"], kind="chunk", **chunk)

    for edge in adjacent:
        src = chunk_key_from_doc_id(edge["_from"])
        dst = chunk_key_from_doc_id(edge["_to"])
        weight = float(edge.get("weight", 1.0))
        if src in graph and dst in graph:
            graph.add_edge(src, dst, kind="adjacent", weight=weight)
            graph.add_edge(dst, src, kind="adjacent", weight=weight)

    for edge in debruijn_edges:
        src = chunk_key_from_doc_id(edge["_from"])
        dst = chunk_key_from_doc_id(edge["_to"])
        if src not in graph or dst not in graph:
            continue
        prob = float(edge.get("transition_probability", 1.0))
        overlap_symbols: list[str] = edge.get("overlap_symbols", [])
        conductivity = _debruijn_conductivity(overlap_symbols, query_tokens or set()) if conductive else 0.0
        weight = prob * (1.0 + conductivity)
        graph.add_edge(
            src,
            dst,
            kind="debruijn_sequence",
            weight=weight,
            conductivity=conductivity,
            overlap_symbols=overlap_symbols,
            transition_probability=prob,
        )

    entity_by_key = {row["_key"]: row for row in entities if row.get("_key")}
    entity_to_chunks: dict[str, list[str]] = defaultdict(list)
    concept_to_chunks: dict[str, list[str]] = defaultdict(list)
    concept_weight: dict[str, float] = {}
    non_cross_doc_types = {"math_label", "math_reference", "bib_entry"}

    for edge in chunk_entities:
        chunk_key = chunk_key_from_doc_id(edge["_from"])
        entity_key = chunk_key_from_doc_id(edge["_to"])
        entity_to_chunks[entity_key].append(chunk_key)

    def _add_shared_entity_edge(src: str, dst: str, weight: float) -> None:
        if src == dst or src not in graph or dst not in graph:
            return
        cur_fwd = float(graph[src][dst]["weight"]) if graph.has_edge(src, dst) else 0.0
        if weight >= cur_fwd:
            graph.add_edge(src, dst, kind="shared_entity", weight=weight)
        cur_rev = float(graph[dst][src]["weight"]) if graph.has_edge(dst, src) else 0.0
        if weight >= cur_rev:
            graph.add_edge(dst, src, kind="shared_entity", weight=weight)

    for entity_key, linked_chunks in entity_to_chunks.items():
        unique = list(dict.fromkeys(linked_chunks))
        entity = entity_by_key.get(entity_key, {})
        shared_weight = entity_bonus(entity)
        for i, src in enumerate(unique):
            for dst in unique[i + 1 :]:
                _add_shared_entity_edge(src, dst, shared_weight)

        etype = str(entity.get("entityType") or "")
        norm = str(entity.get("normalized") or "").strip().lower()
        ckey = str(entity.get("canonicalKey") or "").strip()
        if not ckey and norm and etype not in non_cross_doc_types:
            ckey = f"{etype}:{norm}" if etype else norm
        if ckey and etype not in non_cross_doc_types:
            concept_to_chunks[ckey].extend(unique)
            concept_weight[ckey] = max(concept_weight.get(ckey, 0.0), shared_weight)

    for ckey, linked_chunks in concept_to_chunks.items():
        unique = list(dict.fromkeys(linked_chunks))
        if len(unique) < 2:
            continue
        w = concept_weight[ckey]
        for i, src in enumerate(unique):
            for dst in unique[i + 1 :]:
                _add_shared_entity_edge(src, dst, w)

    for relation in entity_relations:
        src_entity = entity_by_key.get(chunk_key_from_doc_id(relation["_from"]), {})
        dst_entity = entity_by_key.get(chunk_key_from_doc_id(relation["_to"]), {})
        src_chunks = entity_to_chunks.get(src_entity.get("_key", ""), [])
        dst_chunks = entity_to_chunks.get(dst_entity.get("_key", ""), [])
        weight = float(relation.get("weight", 0.4))
        for src_chunk in src_chunks[:4]:
            for dst_chunk in dst_chunks[:4]:
                if src_chunk == dst_chunk or src_chunk not in graph or dst_chunk not in graph:
                    continue
                current = float(graph[src_chunk][dst_chunk]["weight"]) if graph.has_edge(src_chunk, dst_chunk) else 0.0
                merged = max(current, weight)
                graph.add_edge(src_chunk, dst_chunk, kind="entity_relation", weight=merged)

    add_dag_edges(graph, dag_edges)
    return graph


def activated_edges(
    graph: Any,
    chunks_by_key: dict[str, dict[str, Any]],
    *,
    limit: int = 8,
) -> list[dict[str, Any]]:
    edges: list[dict[str, Any]] = []
    for src, dst, data in graph.edges(data=True):
        if data.get("kind") != "debruijn_sequence":
            continue
        edges.append(
            {
                "from": src,
                "to": dst,
                "weight": data.get("weight", 0.0),
                "conductivity": data.get("conductivity", 0.0),
                "overlap_symbols": data.get("overlap_symbols", []),
                "transition_probability": data.get("transition_probability", 0.0),
            }
        )
    edges.sort(key=lambda e: (e["weight"], e["conductivity"]), reverse=True)
    return edges[:limit]


def query_abstraction_score(query_tokens: set[str]) -> float:
    return min(1.0, len(query_tokens) / 4.0)


def coarse_components(
    nx: Any,
    graph: Any,
    chunks: list[dict[str, Any]],
    entities_for_chunk: dict[str, list[dict[str, Any]]],
    scores: dict[str, float],
    query_tokens: set[str],
) -> list[dict[str, Any]]:
    entity_to_chunks: dict[str, list[str]] = defaultdict(list)
    for chunk_key, ents in entities_for_chunk.items():
        for ent in ents:
            norm = ent.get("normalized", "")
            if norm:
                entity_to_chunks[norm].append(chunk_key)

    ug = nx.Graph()
    for chunk in chunks:
        ug.add_node(chunk["_key"])
    for norm, chunk_keys in entity_to_chunks.items():
        unique = list(dict.fromkeys(chunk_keys))
        for i, src in enumerate(unique):
            for dst in unique[i + 1 :]:
                if ug.has_node(src) and ug.has_node(dst):
                    ug.add_edge(src, dst)

    components: list[dict[str, Any]] = []
    for component in nx.connected_components(ug):
        member_list = sorted(component)
        total_score = sum(scores.get(m, 0.0) for m in member_list)
        all_terms: set[str] = set()
        for m in member_list:
            for ent in entities_for_chunk.get(m, []):
                norm = ent.get("normalized", "")
                if norm:
                    all_terms.add(norm)
        relevant_terms = sorted(term for term in all_terms if query_tokens & tokenize(term))
        components.append(
            {
                "members": member_list,
                "memberCount": len(member_list),
                "totalScore": total_score,
                "representativeTerms": relevant_terms,
            }
        )

    components.sort(key=lambda c: c["totalScore"], reverse=True)
    return components


def scc_quotient_scores(
    nx: Any,
    graph: Any,
    seeds: dict[str, float],
) -> tuple[dict[str, float], list[dict[str, Any]]]:
    condensation = nx.condensation(graph)

    node_to_cond: dict[Any, int] = {}
    for cond_node in condensation.nodes:
        for orig_node in condensation.nodes[cond_node]["members"]:
            node_to_cond[orig_node] = cond_node

    cond_seeds: dict[int, float] = defaultdict(float)
    for node, score in seeds.items():
        if node in node_to_cond:
            cond_seeds[node_to_cond[node]] += score

    cond_scores = personalized_scores(condensation, dict(cond_seeds))

    node_scores: dict[str, float] = {}
    quotient: list[dict[str, Any]] = []
    for cond_node in condensation.nodes:
        members = sorted(condensation.nodes[cond_node]["members"])
        scc_score = cond_scores.get(cond_node, 0.0)
        per_member = scc_score / max(1, len(members))
        for m in members:
            node_scores[m] = per_member
        is_cycle = len(members) > 1 or (bool(members) and graph.has_edge(members[0], members[0]))
        quotient.append(
            {
                "members": members,
                "internalCycle": is_cycle,
                "score": scc_score,
            }
        )

    return node_scores, quotient


def personalized_scores(graph, seeds: dict[str, float], *, steps: int = 12, alpha: float = 0.85) -> dict[str, float]:
    scores = {node: 0.0 for node in graph.nodes}
    total = sum(float(value) for value in seeds.values())
    if total <= 0:
        return {}
    base = {node: (float(seeds.get(node, 0.0)) / total) if node in graph else 0.0 for node in graph.nodes}
    scores.update(base)
    for _ in range(steps):
        next_scores = {node: (1.0 - alpha) * base[node] for node in graph.nodes}
        for node in graph.nodes:
            outgoing = list(graph.successors(node))
            if not outgoing:
                next_scores[node] += alpha * scores[node]
                continue
            total_weight = sum(float(graph[node][dst].get("weight", 1.0)) for dst in outgoing)
            if total_weight <= 0:
                next_scores[node] += alpha * scores[node]
                continue
            for dst in outgoing:
                weight = float(graph[node][dst].get("weight", 1.0))
                next_scores[dst] += alpha * scores[node] * (weight / total_weight)
        scores = next_scores
    return scores


def _graph_meta(nx: Any, graph: Any, use_gpu: bool) -> dict[str, Any]:
    return {
        "nodeCount": graph.number_of_nodes(),
        "edgeCount": graph.number_of_edges(),
        "useGpuRequested": bool(use_gpu),
        "backendPriorityAlgos": list(getattr(getattr(nx.config, "backend_priority", object()), "algos", []))
        if hasattr(nx, "config")
        else [],
        "backendPriorityGenerators": list(getattr(getattr(nx.config, "backend_priority", object()), "generators", []))
        if hasattr(nx, "config")
        else [],
    }


def _build_hit(
    *,
    row: dict[str, Any],
    doc: dict[str, Any] | None,
    graph_score: float,
    lex_score: int,
    bm25_score: float,
    entities: list[dict[str, Any]],
    neighbors: list[dict[str, Any]],
    dag_neighbors: list[dict[str, Any]],
) -> dict[str, Any]:
    compact_chunk = _compact_chunk(row)
    compact_doc = _compact_doc(doc)
    source = _build_source(compact_chunk, compact_doc)
    doc_key = compact_chunk.get("documentKey") or (compact_doc or {}).get("_key") or ""
    title = compact_chunk.get("title") or (compact_doc or {}).get("title") or source.get("title") or ""
    path = source.get("path") or (compact_doc or {}).get("path") or ""
    content_hash = source.get("contentHash") or (compact_doc or {}).get("contentHash") or ""
    return {
        "chunk": compact_chunk,
        "source": source,
        "document": compact_doc,
        "documentKey": doc_key,
        "chunkKey": compact_chunk.get("_key") or "",
        "title": title,
        "path": path,
        "contentHash": content_hash,
        "pageStart": source.get("pageStart"),
        "pageEnd": source.get("pageEnd"),
        "chunkKind": compact_chunk.get("chunkKind"),
        "graphScore": graph_score,
        "lexicalScore": lex_score,
        "bm25Score": bm25_score,
        "score": graph_score,
        "entities": entities,
        "neighbors": neighbors,
        "dagNeighbors": dag_neighbors,
        "authority": AUTHORITY,
        "sourceAuthority": AUTHORITY,
    }


ARANGO_SEED_AQL = """
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
LIMIT @candidateK
LET adj = (
    FOR v, e IN 1..1 ANY c._id alexandria_chunk_adjacent_edges
    FILTER v != null
    LIMIT 4
    RETURN {edge: e, chunk: v}
)
LET dag = (
    FOR v, e IN 1..@hops ANY c._id alexandria_dag_edges
    OPTIONS {uniqueVertices: "global", bfs: true}
    FILTER v != null
    LIMIT 6
    RETURN {edge: e, node: v}
)
RETURN {chunk: c, bm25Score: bm25Score, adj: adj, dag: dag}
""".strip()

ARANGO_SUBGRAPH_AQL = """
LET chunkEntities = (
    FOR e IN alexandria_chunk_entity_edges
    FILTER e._from IN @chunkIds
    LIMIT 600
    LET ent = DOCUMENT(e._to)
    FILTER ent != null
    RETURN {edge: e, entity: ent}
)
LET entityRelations = (
    FOR r IN alexandria_entity_relation_edges
    FILTER r.chunkKey IN @chunkKeys
    LIMIT 200
    RETURN r
)
LET documents = (
    FOR dk IN @docKeys
    LET d = DOCUMENT(CONCAT("alexandria_documents/", dk))
    FILTER d != null
    RETURN d
)
RETURN {
    chunkEntities: chunkEntities,
    entityRelations: entityRelations,
    documents: documents
}
""".strip()


def rank_jsonl_context(
    nx: Any,
    input_dir: Path,
    query: str,
    *,
    top_k: int = 8,
    seed_k: int = 5,
    use_gpu: bool = False,
) -> dict[str, Any]:
    if top_k < 0:
        raise ValueError("top_k must be >= 0")
    if seed_k < 0:
        raise ValueError("seed_k must be >= 0")
    if not input_dir.exists() or not input_dir.is_dir():
        raise FileNotFoundError(f"Alexandria input directory does not exist: {input_dir}")
    chunks_path = input_dir / "alexandria_chunks.jsonl"
    if not chunks_path.exists():
        raise FileNotFoundError(f"Required artifact missing: {chunks_path}")

    query_tokens = tokenize(query)
    if not query.strip() or not query_tokens or top_k == 0 or seed_k == 0:
        empty_graph = nx.DiGraph()
        return {
            "authority": AUTHORITY,
            "sourceAuthority": AUTHORITY,
            "disclaimer": DISCLAIMER,
            "mode": "jsonl",
            "query": query,
            "queryTokens": sorted(query_tokens),
            "graph": _graph_meta(nx, empty_graph, use_gpu),
            "seeds": [],
            "hits": [],
        }

    chunks = read_jsonl(chunks_path)
    documents = read_jsonl(input_dir / "alexandria_documents.jsonl")
    entities = read_jsonl(input_dir / "alexandria_entities.jsonl")
    chunk_entities = read_jsonl(input_dir / "alexandria_chunk_entity_edges.jsonl")
    adjacent = read_jsonl(input_dir / "alexandria_chunk_adjacent_edges.jsonl")
    entity_relations = read_jsonl(input_dir / "alexandria_entity_relation_edges.jsonl")
    debruijn_edges = read_jsonl(input_dir / "alexandria_debruijn_edges.jsonl")
    dag_edges = read_jsonl(input_dir / "alexandria_dag_edges.jsonl")

    graph = build_graph(
        nx,
        chunks,
        entities,
        chunk_entities,
        adjacent,
        debruijn_edges,
        entity_relations,
        query_tokens=query_tokens,
        conductive=True,
        dag_edges=dag_edges,
    )
    lexical_ranked = sorted(
        chunks,
        key=lambda row: (lexical_score(query_tokens, row), len(row.get("tokens", []))),
        reverse=True,
    )
    seeds = {
        row["_key"]: float(lexical_score(query_tokens, row))
        for row in lexical_ranked[:seed_k]
        if lexical_score(query_tokens, row) > 0
    }
    pr = personalized_scores(graph, seeds)

    doc_by_key = {row["_key"]: row for row in documents if row.get("_key")}
    entity_by_key = {row["_key"]: row for row in entities if row.get("_key")}
    entities_for_chunk: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for edge in chunk_entities:
        chunk_key = chunk_key_from_doc_id(edge["_from"])
        entity_key = chunk_key_from_doc_id(edge["_to"])
        entity = entity_by_key.get(entity_key)
        if entity:
            entities_for_chunk[chunk_key].append(entity)

    dag_for_chunk: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for edge in dag_edges:
        src = str(edge.get("_from", ""))
        dst = str(edge.get("_to", ""))
        if src.startswith("alexandria_chunks/"):
            dag_for_chunk[chunk_key_from_doc_id(src)].append(
                {
                    "_id": dst,
                    "_key": chunk_key_from_doc_id(dst),
                    "edgeType": edge.get("edgeType"),
                    "evidence": edge.get("evidence"),
                    "confidence": edge.get("confidence"),
                    "direction": "outbound",
                }
            )
        if dst.startswith("alexandria_chunks/"):
            dag_for_chunk[chunk_key_from_doc_id(dst)].append(
                {
                    "_id": src,
                    "_key": chunk_key_from_doc_id(src),
                    "edgeType": edge.get("edgeType"),
                    "evidence": edge.get("evidence"),
                    "confidence": edge.get("confidence"),
                    "direction": "inbound",
                }
            )

    results = sorted(
        chunks,
        key=lambda row: (pr.get(row["_key"], 0.0), lexical_score(query_tokens, row), len(row.get("tokens", []))),
        reverse=True,
    )

    hits: list[dict[str, Any]] = []
    for row in results[:top_k]:
        key = row["_key"]
        lex = lexical_score(query_tokens, row)
        gscore = pr.get(key, 0.0)
        if gscore <= 0.0 and lex <= 0:
            continue
        ents = sorted(
            entities_for_chunk.get(key, []),
            key=lambda ent: (ent.get("confidence", 0.0), ent.get("entityType", "")),
            reverse=True,
        )
        neighbors = [_compact_chunk(dict(graph.nodes[n])) for n in list(graph.successors(key))[:6] if n in graph.nodes]
        hits.append(
            _build_hit(
                row=row,
                doc=doc_by_key.get(str(row.get("documentKey") or "")),
                graph_score=gscore,
                lex_score=lex,
                bm25_score=float(lex),
                entities=ents,
                neighbors=neighbors,
                dag_neighbors=dag_for_chunk.get(key, [])[:8],
            )
        )

    return {
        "authority": AUTHORITY,
        "sourceAuthority": AUTHORITY,
        "disclaimer": DISCLAIMER,
        "mode": "jsonl",
        "query": query,
        "queryTokens": sorted(query_tokens),
        "graph": _graph_meta(nx, graph, use_gpu),
        "seeds": [
            {"chunkKey": key, "lexicalScore": value}
            for key, value in sorted(seeds.items(), key=lambda item: item[1], reverse=True)
        ],
        "hits": hits,
    }


def rank_arango_context(
    nx: Any,
    query: str,
    *,
    endpoint: str | None = None,
    database: str | None = None,
    username: str | None = None,
    password: str | None = None,
    top_k: int = 8,
    seed_k: int = 5,
    hops: int = 1,
    use_gpu: bool = False,
) -> dict[str, Any]:
    load_alexandria_arango_env(REPO_ROOT)
    resolved_endpoint = (endpoint or alexandria_arango_endpoint()).rstrip("/")
    resolved_database = database or alexandria_arango_database()
    resolved_username = username or alexandria_arango_username()
    resolved_password = password if password is not None else alexandria_arango_password("alexandria_root")
    guard_alexandria_target(resolved_endpoint, resolved_database)

    if top_k < 0:
        raise ValueError("top_k must be >= 0")
    if seed_k < 0:
        raise ValueError("seed_k must be >= 0")
    clamped_hops = max(1, min(3, int(hops)))
    query_tokens = tokenize(query)
    target_meta = {"endpoint": resolved_endpoint, "database": resolved_database}

    if not query.strip() or top_k == 0 or seed_k == 0:
        empty_graph = nx.DiGraph()
        return {
            "authority": AUTHORITY,
            "sourceAuthority": AUTHORITY,
            "disclaimer": DISCLAIMER,
            "mode": "arango",
            "query": query,
            "queryTokens": sorted(query_tokens),
            "target": target_meta,
            "graph": _graph_meta(nx, empty_graph, use_gpu),
            "seeds": [],
            "hits": [],
        }

    target = ArangoHttpTarget(
        endpoint=resolved_endpoint,
        database=resolved_database,
        username=resolved_username,
        password=resolved_password,
    )
    candidate_k = max(seed_k, top_k, 12)
    seed_rows = execute_aql(
        target,
        ARANGO_SEED_AQL,
        bind_vars={
            "q": query,
            "terms": safe_search_terms(query),
            "candidateK": int(candidate_k),
            "hops": clamped_hops,
        },
        timeout=15.0,
    )

    if not seed_rows:
        empty_graph = nx.DiGraph()
        return {
            "authority": AUTHORITY,
            "sourceAuthority": AUTHORITY,
            "disclaimer": DISCLAIMER,
            "mode": "arango",
            "query": query,
            "queryTokens": sorted(query_tokens),
            "target": target_meta,
            "graph": _graph_meta(nx, empty_graph, use_gpu),
            "seeds": [],
            "hits": [],
        }

    chunks_by_key: dict[str, dict[str, Any]] = {}
    bm25_by_key: dict[str, float] = {}
    adj_edges_by_key: dict[str, dict[str, Any]] = {}
    dag_edges_by_key: dict[str, dict[str, Any]] = {}
    dag_neighbors_by_chunk: dict[str, list[dict[str, Any]]] = defaultdict(list)
    dag_neighbor_seen: dict[str, set[tuple[str, str, str]]] = defaultdict(set)

    def _add_chunk(c: Any) -> bool:
        if isinstance(c, dict) and c.get("_key"):
            key = str(c["_key"])
            if key in chunks_by_key:
                return True
            if len(chunks_by_key) < 200:
                chunks_by_key[key] = c
                return True
        return False

    def _make_dag_neighbor(target_node: dict[str, Any], edge: dict[str, Any], direction: str) -> dict[str, Any]:
        return {
            "_key": target_node.get("_key"),
            "_id": target_node.get("_id"),
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

    def _record_dag_neighbor(owner_key: str, entry: dict[str, Any]) -> None:
        dedup_key = (
            str(entry.get("_id") or ""),
            str(entry.get("edgeType") or ""),
            str(entry.get("direction") or ""),
        )
        if dedup_key not in dag_neighbor_seen[owner_key]:
            dag_neighbor_seen[owner_key].add(dedup_key)
            dag_neighbors_by_chunk[owner_key].append(entry)

    # First pass: reserve capacity for seed chunks before expanding adj/dag neighbors
    seed_order: list[str] = []
    valid_seed_rows: list[tuple[str, dict[str, Any], dict[str, Any]]] = []
    for row in seed_rows:
        if not isinstance(row, dict):
            continue
        chunk = row.get("chunk")
        if not isinstance(chunk, dict) or not chunk.get("_key"):
            continue
        ckey = str(chunk["_key"])
        if not _add_chunk(chunk):
            continue
        bm25_by_key[ckey] = float(row.get("bm25Score") or 0.0)
        if ckey not in seed_order:
            seed_order.append(ckey)
        valid_seed_rows.append((ckey, chunk, row))

    # Second pass: expand adjacent and DAG neighbors up to the 200-chunk cap
    for ckey, chunk, row in valid_seed_rows:
        for item in row.get("adj") or []:
            if not isinstance(item, dict):
                continue
            _add_chunk(item.get("chunk"))
            edge = item.get("edge")
            if isinstance(edge, dict) and edge.get("_from") and edge.get("_to"):
                ekey = str(edge.get("_key") or f"{edge['_from']}->{edge['_to']}")
                adj_edges_by_key[ekey] = edge

        for item in row.get("dag") or []:
            if not isinstance(item, dict):
                continue
            node = item.get("node")
            edge = item.get("edge")
            node_added_chunk = False
            if isinstance(node, dict) and str(node.get("_id", "")).startswith("alexandria_chunks/"):
                node_added_chunk = _add_chunk(node)
            if isinstance(edge, dict) and edge.get("_from") and edge.get("_to"):
                ekey = str(edge.get("_key") or f"{edge['_from']}->{edge['_to']}")
                dag_edges_by_key[ekey] = edge
            if isinstance(node, dict) and isinstance(edge, dict):
                seed_id = f"alexandria_chunks/{ckey}"
                if edge.get("_from") == seed_id or edge.get("_to") == seed_id:
                    fwd_direction = "outbound" if edge.get("_from") == seed_id else "inbound"
                    _record_dag_neighbor(ckey, _make_dag_neighbor(node, edge, fwd_direction))
                    if (
                        node_added_chunk
                        and str(node.get("_id", "")).startswith("alexandria_chunks/")
                        and node.get("_key")
                    ):
                        node_key = str(node["_key"])
                        rev_direction = "inbound" if fwd_direction == "outbound" else "outbound"
                        _record_dag_neighbor(node_key, _make_dag_neighbor(chunk, edge, rev_direction))
                elif (
                    node_added_chunk
                    and str(node.get("_id", "")).startswith("alexandria_chunks/")
                    and node.get("_key")
                ):
                    node_key = str(node["_key"])
                    node_id = str(node["_id"])
                    if edge.get("_from") == node_id or edge.get("_to") == node_id:
                        other_id = str((edge.get("_to") if edge.get("_from") == node_id else edge.get("_from")) or "")
                        if other_id.startswith("alexandria_chunks/"):
                            other_key = chunk_key_from_doc_id(other_id)
                            other_chunk = chunks_by_key.get(other_key)
                            if other_chunk is not None:
                                rev_direction = "outbound" if edge.get("_from") == node_id else "inbound"
                                other_direction = "inbound" if rev_direction == "outbound" else "outbound"
                                _record_dag_neighbor(node_key, _make_dag_neighbor(other_chunk, edge, rev_direction))
                                _record_dag_neighbor(other_key, _make_dag_neighbor(node, edge, other_direction))

    chunk_keys = list(chunks_by_key.keys())
    chunk_ids = [f"alexandria_chunks/{k}" for k in chunk_keys]
    doc_keys = sorted({str(c["documentKey"]) for c in chunks_by_key.values() if c.get("documentKey")})

    sub_rows = execute_aql(
        target,
        ARANGO_SUBGRAPH_AQL,
        bind_vars={
            "chunkIds": chunk_ids,
            "chunkKeys": chunk_keys,
            "docKeys": doc_keys,
        },
        timeout=15.0,
    )
    sub = sub_rows[0] if sub_rows and isinstance(sub_rows[0], dict) else {}

    entities_by_key: dict[str, dict[str, Any]] = {}
    chunk_entity_edges: list[dict[str, Any]] = []
    entities_for_chunk: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for item in sub.get("chunkEntities") or []:
        if not isinstance(item, dict):
            continue
        edge = item.get("edge")
        ent = item.get("entity")
        if isinstance(edge, dict) and isinstance(ent, dict) and ent.get("_key"):
            entities_by_key[str(ent["_key"])] = ent
            chunk_entity_edges.append(edge)
            ckey = chunk_key_from_doc_id(str(edge.get("_from", "")))
            entities_for_chunk[ckey].append(ent)

    entity_relations = [r for r in (sub.get("entityRelations") or []) if isinstance(r, dict)]
    doc_by_key = {str(d["_key"]): d for d in (sub.get("documents") or []) if isinstance(d, dict) and d.get("_key")}

    chunks_list = list(chunks_by_key.values())
    graph = build_graph(
        nx,
        chunks_list,
        list(entities_by_key.values()),
        chunk_entity_edges,
        list(adj_edges_by_key.values()),
        [],
        entity_relations,
        query_tokens=query_tokens,
        conductive=True,
        dag_edges=list(dag_edges_by_key.values()),
    )

    seeds: dict[str, float] = {}
    for ckey in seed_order[:seed_k]:
        chunk = chunks_by_key.get(ckey)
        if chunk is None:
            continue
        bm25 = bm25_by_key.get(ckey, 0.0)
        lex = float(lexical_score(query_tokens, chunk))
        weight = bm25 if bm25 > 0.0 else max(lex, 1e-6)
        seeds[ckey] = weight

    pr = personalized_scores(graph, seeds)
    results = sorted(
        chunks_list,
        key=lambda row: (
            pr.get(row["_key"], 0.0),
            bm25_by_key.get(row["_key"], 0.0),
            lexical_score(query_tokens, row),
        ),
        reverse=True,
    )

    hits: list[dict[str, Any]] = []
    for row in results[:top_k]:
        key = str(row["_key"])
        gscore = pr.get(key, 0.0)
        lex = lexical_score(query_tokens, row)
        bm25 = bm25_by_key.get(key, 0.0)
        if gscore <= 0.0 and lex <= 0 and bm25 <= 0.0:
            continue
        ents = sorted(
            entities_for_chunk.get(key, []),
            key=lambda ent: (ent.get("confidence", 0.0), ent.get("entityType", "")),
            reverse=True,
        )
        neighbors = [_compact_chunk(dict(graph.nodes[n])) for n in list(graph.successors(key))[:6] if n in graph.nodes]
        hits.append(
            _build_hit(
                row=row,
                doc=doc_by_key.get(str(row.get("documentKey") or "")),
                graph_score=gscore,
                lex_score=lex,
                bm25_score=bm25,
                entities=ents,
                neighbors=neighbors,
                dag_neighbors=dag_neighbors_by_chunk.get(key, [])[:8],
            )
        )

    return {
        "authority": AUTHORITY,
        "sourceAuthority": AUTHORITY,
        "disclaimer": DISCLAIMER,
        "mode": "arango",
        "query": query,
        "queryTokens": sorted(query_tokens),
        "target": target_meta,
        "graph": _graph_meta(nx, graph, use_gpu),
        "seeds": [
            {
                "chunkKey": key,
                "lexicalScore": lexical_score(query_tokens, chunks_by_key[key]),
                "bm25Score": bm25_by_key.get(key, 0.0),
            }
            for key in seed_order[:seed_k]
            if key in chunks_by_key
        ],
        "hits": hits,
    }


def format_text_packet(packet: dict[str, Any]) -> str:
    graph_info = packet.get("graph") or {}
    lines = [
        f"[AUTHORITY: {packet.get('authority', AUTHORITY)} — {packet.get('disclaimer', DISCLAIMER)}]",
        f"Query: {packet.get('query', '')}",
        f"Mode: {packet.get('mode', 'unknown')} | Graph: {graph_info.get('nodeCount', 0)} nodes, {graph_info.get('edgeCount', 0)} edges | Hits: {len(packet.get('hits', []))}",
        "",
    ]
    for idx, hit in enumerate(packet.get("hits", []), start=1):
        chunk = hit.get("chunk") or {}
        gscore = float(hit.get("graphScore") or 0.0)
        lscore = int(hit.get("lexicalScore") or 0)
        title = hit.get("title") or "(untitled)"
        path = hit.get("path") or ""
        p_start = hit.get("pageStart")
        pages = f"p.{p_start}" if p_start is not None else "p.?"
        kind = hit.get("chunkKind") or "chunk"
        doc_key = hit.get("documentKey") or ""
        lines.append(f"{idx}. [graph={gscore:.4f}, lex={lscore}] {title} ({path} {pages}, kind={kind}, doc={doc_key})")
        snippet = str(chunk.get("text") or "").strip().replace("\n", " ")
        if snippet:
            lines.append(f"   text: {snippet[:300]}")
    return "\n".join(lines) + "\n"


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Rank Alexandria context with lexical/BM25 seeds plus graph/DAG expansion")
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
    ap.add_argument("--seed-k", type=int, default=5)
    ap.add_argument("--hops", type=int, default=1)
    ap.add_argument("--use-gpu", action="store_true")
    ap.add_argument("--format", choices=("json", "text"), default="json")
    ap.add_argument("--json-out", type=Path)
    args = ap.parse_args(argv)
    if args.top_k < 0:
        ap.error("--top-k must be >= 0")
    if args.limit is not None and args.limit < 0:
        ap.error("--limit must be >= 0")
    if args.seed_k < 0:
        ap.error("--seed-k must be >= 0")
    if args.hops < 1:
        ap.error("--hops must be >= 1")
    return args


def main(argv: list[str] | None = None) -> int:
    load_alexandria_arango_env(REPO_ROOT)
    args = parse_args(argv)
    maybe_enable_gpu_backend(bool(args.use_gpu))
    top_k = args.limit if args.limit is not None else args.top_k

    try:
        import networkx as nx  # type: ignore
    except Exception as exc:
        print(json.dumps({"error": f"failed to import networkx: {exc}"}, indent=2), file=sys.stderr)
        return 1

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
            packet = rank_arango_context(
                nx,
                args.query,
                endpoint=endpoint,
                database=database,
                username=username,
                password=password,
                top_k=top_k,
                seed_k=args.seed_k,
                hops=args.hops,
                use_gpu=bool(args.use_gpu),
            )
        except (URLError, OSError, RuntimeError, ValueError) as exc:
            print(json.dumps({"error": f"ArangoDB graph ranking failed: {exc}"}, ensure_ascii=False), file=sys.stderr)
            return 1
    else:
        try:
            packet = rank_jsonl_context(
                nx,
                args.input_dir,
                args.query,
                top_k=top_k,
                seed_k=args.seed_k,
                use_gpu=bool(args.use_gpu),
            )
        except FileNotFoundError as exc:
            print(json.dumps({"error": str(exc)}, ensure_ascii=False), file=sys.stderr)
            return 1

    rendered = format_text_packet(packet) if args.format == "text" else json.dumps(packet, ensure_ascii=False, indent=2)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(rendered + ("\n" if not rendered.endswith("\n") else ""), encoding="utf-8")
    else:
        print(rendered, end="" if rendered.endswith("\n") else "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
