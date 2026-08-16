#!/usr/bin/env python3
"""Build Lean-grounded "gravitational" context from the proven declaration graph.

The tool prefers live ArangoDB collections, but falls back to the repo's
LeanTrail JSONL export. It emits a compact packet of nearby proven declarations
and source excerpts for prover prompts.
"""

from __future__ import annotations

import argparse
import base64
import collections
import json
import math
import os
import re
import sys
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

from igf.config import DEFAULT_GRAPH_MODE, GRAPH_MODE_CHOICES, resolve_graph_mode

_DEFAULT_GRAPH_PROFILE = resolve_graph_mode(DEFAULT_GRAPH_MODE)

DEFAULT_NODES = Path("artifacts/dag/index/decls.jsonl")
DEFAULT_EDGES = Path("artifacts/dag/index/edges.jsonl")
DEFAULT_ARANGO = "http://127.0.0.1:8530"
DEFAULT_DB = "infogeometry"
DEFAULT_NODE_COLLECTION = _DEFAULT_GRAPH_PROFILE.collections.compact_nodes
DEFAULT_EDGE_COLLECTION = _DEFAULT_GRAPH_PROFILE.collections.compact_edges
DEFAULT_RAW_NODE_COLLECTION = _DEFAULT_GRAPH_PROFILE.collections.raw_nodes
DEFAULT_RAW_EDGE_COLLECTION = _DEFAULT_GRAPH_PROFILE.collections.raw_edges
DEFAULT_OVERLAY_NODE_COLLECTION = _DEFAULT_GRAPH_PROFILE.collections.overlay_nodes
DEFAULT_OVERLAY_EDGE_COLLECTION = _DEFAULT_GRAPH_PROFILE.collections.overlay_edges
DEFAULT_EQUIVALENCE_DICTIONARY = Path("reports/dag/equivalence-dictionary.json")
STOPWORDS = {
    "against",
    "attempt",
    "candidate",
    "candidates",
    "formalization",
    "guided",
    "handoff",
    "investigate",
    "kind",
    "leanprogress",
    "local",
    "name",
    "note",
    "packet",
    "proof",
    "proving",
    "remaining",
    "row",
    "research",
    "sample",
    "status",
    "steps",
    "tactic",
    "target",
    "targets",
    "theorem",
    "using",
    "with",
}


def repo_root_from(path: Path) -> Path:
    cur = path.resolve()
    for parent in (cur, *cur.parents):
        if (parent / "lakefile.lean").exists() or (parent / "lakefile.toml").exists():
            return parent
    return cur


def tokenize(text: str) -> set[str]:
    text = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", text)
    return {
        tok.lower()
        for tok in re.split(r"[^A-Za-z0-9_]+", text)
        if len(tok) >= 3 and tok.lower() not in STOPWORDS
    }


def token_text(text: str) -> str:
    """Turn a declaration-ish name into searchable words."""
    text = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", text)
    text = text.replace("_", " ").replace(".", " ")
    return text


def query_phrases(text: str) -> list[str]:
    phrases: list[str] = []
    excluded = {"infogeometry", "deepseek_proof", "goedel_audit", "codex_execution"}
    for piece in re.split(r"\s+", text):
        cleaned = piece.strip("`'\"()[]{}.,:;")
        if len(cleaned) < 5:
            continue
        lowered = cleaned.lower()
        if lowered in excluded or lowered.endswith(".py"):
            continue
        is_identifier_like = (
            (cleaned.startswith("InfoGeometry.") and cleaned.count(".") >= 2)
            or "_" in cleaned
            or bool(re.search(r"[a-z][A-Z]", cleaned))
        )
        if is_identifier_like and ("_" not in cleaned or re.search(r"_(eq|of|is|has|iff|le|lt|ge|gt|mul|add|zero|one)_?", cleaned)):
            phrases.append(lowered)
    return phrases


def load_equivalence_components(path: Path | None) -> list[dict[str, Any]]:
    if not path or not path.exists():
        return []
    data = json.loads(path.read_text(encoding="utf-8"))
    components: list[dict[str, Any]] = []
    if isinstance(data, dict):
        raw_components = data.get("components")
        if isinstance(raw_components, list):
            for component in raw_components:
                members = component.get("members") if isinstance(component, dict) else None
                if isinstance(members, list) and members:
                    relation_kinds = component.get("relationKinds")
                    labels = {"synonym_component", "generated_component"}
                    if isinstance(relation_kinds, dict):
                        labels.update(str(kind) for kind in relation_kinds)
                    components.append(
                        {
                            "id": component.get("id"),
                            "members": [str(member) for member in members],
                            "labels": sorted(labels),
                            "source": str(path),
                        }
                    )
        pairs = data.get("pairs")
        if isinstance(pairs, list):
            for index, pair in enumerate(pairs):
                if not isinstance(pair, dict):
                    continue
                lhs = pair.get("lhs")
                rhs = pair.get("rhs")
                if lhs and rhs:
                    relation_kind = pair.get("relationKind")
                    labels = {"synonym_component", "curated_component"}
                    if relation_kind:
                        labels.add(str(relation_kind))
                    components.append(
                        {
                            "id": pair.get("id") or f"curated-pair-{index + 1}",
                            "members": [str(lhs), str(rhs)],
                            "relation_kind": relation_kind,
                            "labels": sorted(labels),
                            "note": pair.get("note"),
                            "source": str(path),
                        }
                    )
    return components


def expand_query_tokens(
    query_tokens: set[str],
    components: list[dict[str, Any]],
    *,
    max_groups: int,
    max_tokens: int,
) -> tuple[set[str], list[dict[str, Any]]]:
    """Expand query tokens through known equivalence components.

    The expansion is intentionally conservative: a component must share at least
    one token with the query before its member tokens are added. This makes the
    equivalence dictionary a retrieval prior, not a source of truth.
    """
    if not query_tokens or not components or max_groups <= 0 or max_tokens <= 0:
        return set(query_tokens), []

    matches: list[tuple[int, int, dict[str, Any], set[str], set[str]]] = []
    for component in components:
        members = component.get("members") or []
        member_tokens = tokenize(" ".join(token_text(str(member)) for member in members))
        overlap = query_tokens & member_tokens
        if not overlap:
            continue
        matches.append((len(overlap), len(member_tokens), component, overlap, member_tokens))

    matches.sort(key=lambda item: (item[0], -item[1]), reverse=True)
    expanded = set(query_tokens)
    matched_groups: list[dict[str, Any]] = []
    for _overlap_count, _size, component, overlap, member_tokens in matches[:max_groups]:
        added = sorted((member_tokens - expanded))[:max_tokens]
        expanded.update(added)
        matched_groups.append(
            {
                "id": component.get("id"),
                "source": component.get("source"),
                "relation_kind": component.get("relation_kind"),
                "labels": component.get("labels") or ["synonym_component"],
                "note": component.get("note"),
                "matched_tokens": sorted(overlap),
                "added_tokens": added,
                "members": component.get("members") or [],
            }
        )
        if len(expanded) >= len(query_tokens) + max_tokens:
            break
    return expanded, matched_groups


# [lossless-compact] read_jsonl folded into igf.common.json_io.read_jsonl
from igf.common.json_io import read_jsonl


def arango_request(base_url: str, db: str, payload: dict[str, Any]) -> dict[str, Any]:
    url = f"{base_url.rstrip('/')}/_db/{db}/_api/cursor"
    data = json.dumps(payload).encode("utf-8")
    request = urllib.request.Request(
        url,
        data=data,
        method="POST",
        headers={"Content-Type": "application/json"},
    )
    add_arango_auth(request)
    with urllib.request.urlopen(request, timeout=30) as response:
        return json.loads(response.read().decode("utf-8"))


def add_arango_auth(request: urllib.request.Request) -> None:
    """Attach Basic auth when repository Arango credentials are configured."""
    username = os.environ.get("ARANGO_USER") or os.environ.get("ARANGO_USERNAME")
    password = os.environ.get("ARANGO_PASS") or os.environ.get("ARANGO_PASSWORD")
    if not username or password is None:
        return
    token = base64.b64encode(f"{username}:{password}".encode("utf-8")).decode("ascii")
    request.add_header("Authorization", f"Basic {token}")


def arango_cursor_all(base_url: str, db: str, payload: dict[str, Any]) -> list[dict[str, Any]]:
    first = arango_request(base_url, db, payload)
    rows = list(first.get("result") or [])
    cursor_id = first.get("id")
    has_more = bool(first.get("hasMore"))
    while has_more and cursor_id:
        url = f"{base_url.rstrip('/')}/_db/{db}/_api/cursor/{cursor_id}"
        request = urllib.request.Request(url, method="PUT", headers={"Content-Type": "application/json"})
        add_arango_auth(request)
        with urllib.request.urlopen(request, timeout=30) as response:
            payload = json.loads(response.read().decode("utf-8"))
        rows.extend(payload.get("result") or [])
        cursor_id = payload.get("id")
        has_more = bool(payload.get("hasMore"))
    return rows


def load_arango(
    base_url: str,
    db: str,
    nodes_collection: str,
    edges_collection: str,
    limit_nodes: int,
    limit_edges: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    nodes_payload = {
        "query": "FOR n IN @@nodes LIMIT @limit RETURN n",
        "bindVars": {"@nodes": nodes_collection, "limit": limit_nodes},
        "batchSize": min(limit_nodes, 10000),
    }
    edges_payload = {
        "query": "FOR e IN @@edges LIMIT @limit RETURN e",
        "bindVars": {"@edges": edges_collection, "limit": limit_edges},
        "batchSize": min(limit_edges, 10000),
    }
    nodes = arango_cursor_all(base_url, db, nodes_payload)
    edges = arango_cursor_all(base_url, db, edges_payload)
    if not nodes:
        raise RuntimeError("Arango returned no nodes")
    return nodes, edges


def _arango_doc_id(collection: str, key: str) -> str:
    return f"{collection}/{key}"


def _edge_endpoint_key(value: Any) -> str:
    text = str(value or "")
    if "/" in text:
        return text.split("/", 1)[1]
    return text


def normalize_raw_node(node: dict[str, Any], *, raw_nodes_collection: str) -> dict[str, Any]:
    """Convert layered raw_info_nodes rows to the compact retriever shape."""
    decl = node.get("decl") if isinstance(node.get("decl"), dict) else {}
    raw_attrs = node.get("attrs")
    attrs = dict(raw_attrs) if isinstance(raw_attrs, dict) else {}
    if decl.get("doc") and not attrs.get("doc"):
        attrs["doc"] = decl.get("doc")
    if decl.get("kind") and not attrs.get("decl_kind"):
        attrs["decl_kind"] = decl.get("kind")
    name = str(node.get("raw_name") or node.get("name") or decl.get("name") or node.get("_key") or "")
    return {
        **node,
        "id": name,
        "name": name,
        "kind": "Declaration",
        "module": node.get("module") or decl.get("module"),
        "file": decl.get("file") or node.get("file"),
        "line": decl.get("line") or node.get("line"),
        "column": decl.get("column") or node.get("column"),
        "attrs": attrs,
        "_raw_key": node.get("_key"),
        "_raw_doc_id": _arango_doc_id(raw_nodes_collection, str(node.get("_key") or "")),
    }


def normalize_raw_edge(edge: dict[str, Any]) -> dict[str, Any]:
    """Convert layered raw_info_edges rows to the compact retriever shape."""
    return {
        **edge,
        "src": str(edge.get("src") or _edge_endpoint_key(edge.get("_from"))),
        "dst": str(edge.get("dst") or _edge_endpoint_key(edge.get("_to"))),
        "kind": str(edge.get("kind") or "dependency"),
        "weight": float(edge.get("weight") or 1.0),
    }


def node_rep_layer(node: dict[str, Any]) -> str | None:
    attrs = node.get("attrs") if isinstance(node.get("attrs"), dict) else {}
    value = node.get("rep_layer") or attrs.get("rep_layer")
    return str(value) if value not in (None, "") else None


def node_rep_depth(node: dict[str, Any]) -> int | str | None:
    attrs = node.get("attrs") if isinstance(node.get("attrs"), dict) else {}
    value = node.get("rep_depth")
    if value is None:
        value = node.get("rep_depth_nat")
    if value is None:
        value = attrs.get("rep_depth_nat")
    return value if value not in ("", None) else None


def node_rep_depth_slug(node: dict[str, Any]) -> str | None:
    attrs = node.get("attrs") if isinstance(node.get("attrs"), dict) else {}
    value = node.get("rep_depth_slug") or attrs.get("rep_depth_slug")
    return str(value) if value not in (None, "") else None


def node_rep_layer_description(node: dict[str, Any]) -> str | None:
    attrs = node.get("attrs") if isinstance(node.get("attrs"), dict) else {}
    value = node.get("rep_layer_description") or attrs.get("rep_layer_description")
    return str(value) if value not in (None, "") else None


def rep_layer_counts(nodes: list[dict[str, Any]]) -> list[dict[str, Any]]:
    counts: collections.Counter[str | None] = collections.Counter(node_rep_layer(node) for node in nodes)
    depth_by_layer: dict[str | None, set[Any]] = collections.defaultdict(set)
    slug_by_layer: dict[str | None, set[str]] = collections.defaultdict(set)
    for node in nodes:
        layer = node_rep_layer(node)
        depth = node_rep_depth(node)
        slug = node_rep_depth_slug(node)
        if depth is not None:
            depth_by_layer[layer].add(depth)
        if slug:
            slug_by_layer[layer].add(slug)

    def sort_key(item: tuple[str | None, int]) -> tuple[int, str]:
        layer, _count = item
        if layer is None:
            return (-1, "")
        match = re.match(r"L(\d+)_", layer)
        return (int(match.group(1)) if match else 999, layer)

    rows: list[dict[str, Any]] = []
    for layer, count in sorted(counts.items(), key=sort_key):
        rows.append(
            {
                "rep_layer": layer,
                "count": count,
                "rep_depths": sorted(depth_by_layer.get(layer, set()), key=lambda value: str(value)),
                "rep_depth_slugs": sorted(slug_by_layer.get(layer, set())),
            }
        )
    return rows


def load_faithful_arango(
    base_url: str,
    db: str,
    raw_nodes_collection: str,
    raw_edges_collection: str,
    limit_nodes: int,
    limit_edges: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    nodes, edges = load_arango(
        base_url,
        db,
        raw_nodes_collection,
        raw_edges_collection,
        limit_nodes,
        limit_edges,
    )
    normalized_nodes = [normalize_raw_node(node, raw_nodes_collection=raw_nodes_collection) for node in nodes]
    normalized_edges = [normalize_raw_edge(edge) for edge in edges]
    return normalized_nodes, normalized_edges


def load_graph(args: argparse.Namespace) -> tuple[str, list[dict[str, Any]], list[dict[str, Any]]]:
    profile = resolve_graph_mode(args.graph_mode)
    if profile.name in {"faithful", "unified"}:
        try:
            nodes, edges = load_faithful_arango(
                args.arango_url,
                args.arango_db,
                args.raw_nodes_collection,
                args.raw_edges_collection,
                args.limit_nodes,
                args.limit_edges,
            )
            source_name = "arango:unified_layered" if profile.name == "unified" else "arango:faithful_raw"
            return source_name, nodes, edges
        except (RuntimeError, urllib.error.URLError, urllib.error.HTTPError, TimeoutError, OSError) as exc:
            raise SystemExit(f"failed to load {profile.name} Arango graph: {exc}") from exc

    if profile.name == "hybrid":
        try:
            nodes, edges = load_arango(
                args.arango_url,
                args.arango_db,
                args.nodes_collection,
                args.edges_collection,
                args.limit_nodes,
                args.limit_edges,
            )
            return "arango:hybrid_compact_seed", nodes, edges
        except (RuntimeError, urllib.error.URLError, urllib.error.HTTPError, TimeoutError, OSError) as exc:
            if args.source == "arango":
                raise SystemExit(f"failed to load compact Arango graph for hybrid mode: {exc}") from exc

    if args.source in {"auto", "arango"}:
        try:
            nodes, edges = load_arango(
                args.arango_url,
                args.arango_db,
                args.nodes_collection,
                args.edges_collection,
                args.limit_nodes,
                args.limit_edges,
            )
            return "arango", nodes, edges
        except (RuntimeError, urllib.error.URLError, urllib.error.HTTPError, TimeoutError, OSError) as exc:
            if args.source == "arango":
                raise SystemExit(f"failed to load Arango graph: {exc}") from exc

    nodes = read_jsonl(args.nodes)
    edges = read_jsonl(args.edges)
    return "jsonl", nodes, edges


def load_faithful_index(args: argparse.Namespace, names: list[str]) -> dict[str, dict[str, Any]]:
    if not names:
        return {}
    payload = {
        "query": """
        FOR n IN @@raw_nodes
          FILTER n.raw_name IN @names OR n.name IN @names
          LET memberships = (
            FOR m IN @@overlay_edges
              FILTER m.role == "member_of_scc" && m._from == CONCAT(@raw_nodes_name, "/", n._key)
              LIMIT 1
              RETURN m
          )
          RETURN {node: n, membership: FIRST(memberships)}
        """,
        "bindVars": {
            "@raw_nodes": args.raw_nodes_collection,
            "@overlay_edges": args.overlay_edges_collection,
            "raw_nodes_name": args.raw_nodes_collection,
            "names": names,
        },
        "batchSize": min(max(len(names), 1), 1000),
    }
    try:
        rows = arango_cursor_all(args.arango_url, args.arango_db, payload)
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, OSError):
        return {}
    out: dict[str, dict[str, Any]] = {}
    for row in rows:
        node = row.get("node") if isinstance(row, dict) else None
        if not isinstance(node, dict):
            continue
        name = str(node.get("raw_name") or node.get("name") or "")
        out[name] = {
            "raw_key": node.get("_key"),
            "raw_doc_id": _arango_doc_id(args.raw_nodes_collection, str(node.get("_key") or "")),
            "scc_id": node.get("scc_id"),
            "scc_key": node.get("scc_key"),
            "member_of_scc_edge": row.get("membership"),
            "witness_backed": bool(row.get("membership")),
        }
    return out


def lexical_score(node: dict[str, Any], query_tokens: set[str], phrases: list[str]) -> float:
    attrs = node.get("attrs") if isinstance(node.get("attrs"), dict) else {}
    haystack = " ".join(
        str(part or "")
        for part in (
            node.get("id"),
            node.get("name"),
            node.get("module"),
            node.get("module_family"),
            node.get("rep_layer"),
            node.get("rep_depth_slug"),
            attrs.get("decl_kind"),
            attrs.get("rep_layer"),
            attrs.get("rep_depth_slug"),
            attrs.get("rep_layer_description"),
            attrs.get("doc"),
        )
    )
    tokens = tokenize(haystack)
    if not tokens:
        return 0.0
    overlap = query_tokens & tokens
    exact_bonus = 0.0
    lowered = haystack.lower()
    for token in query_tokens:
        if len(token) >= 5 and token in lowered:
            exact_bonus += 0.15
    for phrase in phrases:
        if phrase in lowered:
            exact_bonus += 8.0
    return len(overlap) / math.sqrt(max(len(tokens), 1)) + exact_bonus


def node_mass(node: dict[str, Any]) -> float:
    attrs = node.get("attrs") if isinstance(node.get("attrs"), dict) else {}
    decl_kind = attrs.get("decl_kind")
    kind = node.get("kind")
    mass = 1.0
    if decl_kind == "theorem":
        mass += 2.0
    elif decl_kind in {"lemma", "def"}:
        mass += 1.0
    if kind == "Declaration":
        mass += 0.5
    if attrs.get("doc"):
        mass += min(len(str(attrs["doc"])) / 400.0, 0.75)
    if node.get("line"):
        mass += 0.25
    
    # 🧬 Spectral mass (Weighted Hodge M0)
    fp = node.get("typeFingerprint") or {}
    node_count = fp.get("nodeCount", 0)
    redex_count = fp.get("redexCount", 0)
    if node_count > 0:
        # Redex density represents potential energy/complexity
        density = redex_count / float(node_count)
        mass += density * 1.2
        # Absolute size log-scale boost
        mass += math.log10(node_count + 1) * 0.4
        
    return mass


def build_spectral_synonyms(nodes: list[dict[str, Any]]) -> dict[str, list[str]]:
    """Build a mapping from shapeHash to list of node IDs."""
    synonyms: dict[str, list[str]] = collections.defaultdict(list)
    for node in nodes:
        node_id = node.get("id")
        fp = node.get("typeFingerprint") or {}
        shape_hash = fp.get("shapeHash")
        if node_id and shape_hash and shape_hash != "0":
            synonyms[str(shape_hash)].append(str(node_id))
    return synonyms


def build_adjacency(edges: list[dict[str, Any]]) -> dict[str, list[tuple[str, float, str]]]:
    adjacency: dict[str, list[tuple[str, float, str]]] = collections.defaultdict(list)
    for edge in edges:
        src = edge.get("src")
        dst = edge.get("dst")
        if not src or not dst:
            continue
        weight = float(edge.get("weight") or 1.0)
        kind = str(edge.get("kind") or "edge")
        adjacency[src].append((dst, weight, kind))
        adjacency[dst].append((src, weight, kind))
    return adjacency


def propagate_scores(
    nodes_by_id: dict[str, dict[str, Any]],
    adjacency: dict[str, list[tuple[str, float, str]]],
    seed_scores: dict[str, float],
    max_hops: int,
) -> tuple[dict[str, float], dict[str, int]]:
    scores: dict[str, float] = collections.defaultdict(float)
    distances: dict[str, int] = {}
    queue: collections.deque[tuple[str, float, int]] = collections.deque()
    for node_id, score in seed_scores.items():
        queue.append((node_id, score, 0))
        distances[node_id] = 0

    seen_best: dict[tuple[str, int], float] = {}
    while queue:
        node_id, incoming, depth = queue.popleft()
        if node_id not in nodes_by_id:
            continue
        scores[node_id] += incoming * node_mass(nodes_by_id[node_id])
        if depth >= max_hops:
            continue
        for neighbor, weight, _kind in adjacency.get(node_id, []):
            next_score = incoming * min(weight, 3.0) * 0.55
            key = (neighbor, depth + 1)
            if next_score <= seen_best.get(key, 0.0):
                continue
            seen_best[key] = next_score
            distances[neighbor] = min(distances.get(neighbor, depth + 1), depth + 1)
            queue.append((neighbor, next_score, depth + 1))
    return scores, distances


def scc_anchor_distances(
    nodes_by_id: dict[str, dict[str, Any]],
    edges: list[dict[str, Any]],
    phrases: list[str],
    max_hops: int,
    seed_node_ids: set[str] | None = None,
) -> tuple[set[int], dict[int, int]]:
    """Anchor retrieval on SCCs containing lexical seeds or exact query-phrase hits."""
    seed_sccs: set[int] = set()
    for node_id, node in nodes_by_id.items():
        if seed_node_ids and node_id in seed_node_ids:
            scc_id = node.get("scc_id")
            if isinstance(scc_id, int):
                seed_sccs.add(scc_id)
        haystack = " ".join(
            str(part or "")
            for part in (node.get("id"), node.get("name"), node.get("module"))
        ).lower()
        if any(phrase in haystack for phrase in phrases):
            scc_id = node.get("scc_id")
            if isinstance(scc_id, int):
                seed_sccs.add(scc_id)

    if not seed_sccs:
        return set(), {}

    adjacency: dict[int, set[int]] = collections.defaultdict(set)
    for edge in edges:
        src_scc = edge.get("src_scc")
        dst_scc = edge.get("dst_scc")
        if not isinstance(src_scc, int) or not isinstance(dst_scc, int):
            continue
        adjacency[src_scc].add(dst_scc)
        adjacency[dst_scc].add(src_scc)

    distances: dict[int, int] = {scc_id: 0 for scc_id in seed_sccs}
    queue: collections.deque[tuple[int, int]] = collections.deque((scc_id, 0) for scc_id in seed_sccs)
    while queue:
        scc_id, depth = queue.popleft()
        if depth >= max_hops:
            continue
        for neighbor in adjacency.get(scc_id, set()):
            if neighbor in distances:
                continue
            distances[neighbor] = depth + 1
            queue.append((neighbor, depth + 1))
    return seed_sccs, distances


def remap_source_path(path_text: str | None, repo_root: Path) -> Path | None:
    if not path_text:
        return None
    path = Path(path_text)
    if path.exists():
        return path
    marker = "info-geometry-lean/"
    raw = str(path)
    if marker in raw:
        suffix = raw.split(marker, 1)[1]
        candidate = repo_root / suffix
        if candidate.exists():
            return candidate
    if raw.startswith("/home/goutev/LEAN4/info-geometry-lean/"):
        candidate = repo_root / raw.removeprefix("/home/goutev/LEAN4/info-geometry-lean/")
        if candidate.exists():
            return candidate
    return path


def source_excerpt(node: dict[str, Any], repo_root: Path, radius: int) -> dict[str, Any] | None:
    path = remap_source_path(node.get("file"), repo_root)
    line = node.get("line")
    if not path or not line or not path.exists():
        return None
    line_no = int(line)
    start = max(1, line_no - radius)
    end = line_no + radius
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    excerpt = []
    for number in range(start, min(end, len(lines)) + 1):
        excerpt.append({"line": number, "text": lines[number - 1]})
    return {
        "path": str(path),
        "line": line_no,
        "start": start,
        "end": min(end, len(lines)),
        "lines": excerpt,
    }


def build_context(args: argparse.Namespace) -> dict[str, Any]:
    source, nodes, edges = load_graph(args)
    repo_root = args.repo_root.resolve()
    query_tokens = tokenize(args.query)
    phrases = query_phrases(args.query)
    equivalence_components = load_equivalence_components(args.equivalence_dictionary)
    expanded_query_tokens, synonym_groups = expand_query_tokens(
        query_tokens,
        equivalence_components if args.use_equivalence_expansion else [],
        max_groups=args.max_equivalence_groups,
        max_tokens=args.max_equivalence_tokens,
    )
    nodes_by_id: dict[str, dict[str, Any]] = {}
    for node in nodes:
        node_id = node.get("id") or node.get("name") or node.get("_key")
        if not node_id:
            continue
        node_key = str(node_id)
        raw_attrs = node.get("attrs")
        attrs = dict(raw_attrs) if isinstance(raw_attrs, dict) else {}
        if node.get("doc") and not attrs.get("doc"):
            attrs["doc"] = node.get("doc")
        if node.get("kind") and not attrs.get("decl_kind"):
            attrs["decl_kind"] = node.get("kind")
        normalized = {
            **node,
            "id": node_key,
            "name": str(node.get("name") or node_key),
            "kind": "Declaration",
            "attrs": attrs,
        }
        nodes_by_id[node_key] = normalized
    adjacency = build_adjacency(edges)
    spectral_synonyms = build_spectral_synonyms(nodes)

    lexical = {
        node_id: score
        for node_id, node in nodes_by_id.items()
        if (score := lexical_score(node, expanded_query_tokens, phrases)) >= args.min_seed_score
    }
    
    # 🧬 Spectral boost: boost nodes that share the same shapeHash as top lexical hits
    spectral_boosts: dict[str, float] = collections.defaultdict(float)
    for node_id, score in sorted(lexical.items(), key=lambda x: x[1], reverse=True)[:args.seed_k]:
        node = nodes_by_id.get(node_id)
        if not node: continue
        shape_hash = (node.get("typeFingerprint") or {}).get("shapeHash")
        if shape_hash and shape_hash != "0":
            for twin_id in spectral_synonyms.get(str(shape_hash), []):
                if twin_id != node_id:
                    spectral_boosts[twin_id] += score * 0.4
    
    for node_id, boost in spectral_boosts.items():
        lexical[node_id] = lexical.get(node_id, 0.0) + boost

    seed_scores = dict(sorted(lexical.items(), key=lambda item: item[1], reverse=True)[: args.seed_k])
    seed_sccs: set[int] = set()
    scc_distances: dict[int, int] = {}
    if args.graph_mode == "faithful":
        seed_sccs, scc_distances = scc_anchor_distances(
            nodes_by_id,
            edges,
            phrases,
            args.max_hops,
            seed_node_ids=set(seed_scores),
        )

    if args.graph_mode == "faithful" and args.scc_anchor_first:
        propagated: dict[str, float] = {}
        distances: dict[str, int] = {}
        if not scc_distances and args.require_scc_anchor:
            seed_scores = {}
    else:
        propagated, distances = propagate_scores(nodes_by_id, adjacency, seed_scores, args.max_hops)

    if not propagated and seed_scores:
        propagated = {node_id: score * node_mass(nodes_by_id[node_id]) for node_id, score in seed_scores.items()}

    final_scores = dict(propagated)
    for node_id, score in lexical.items():
        final_scores[node_id] = final_scores.get(node_id, 0.0) + score * args.lexical_anchor_weight
    if scc_distances:
        for node_id, node in nodes_by_id.items():
            scc_id = node.get("scc_id")
            if not isinstance(scc_id, int) or scc_id not in scc_distances:
                continue
            distance = scc_distances[scc_id]
            final_scores[node_id] = final_scores.get(node_id, 0.0) + args.scc_anchor_weight / float(distance + 1)

    ranked = sorted(final_scores.items(), key=lambda item: item[1], reverse=True)
    if args.graph_mode == "faithful" and args.scc_anchor_first and scc_distances:
        ranked = [
            (node_id, score)
            for node_id, score in ranked
            if (
                node_id in seed_scores
                or (
                    isinstance(nodes_by_id[node_id].get("scc_id"), int)
                    and nodes_by_id[node_id].get("scc_id") in scc_distances
                )
            )
        ]
    requested_rep_layers = set(args.rep_layer or [])
    if requested_rep_layers:
        ranked = [
            (node_id, score)
            for node_id, score in ranked
            if node_rep_layer(nodes_by_id[node_id]) in requested_rep_layers
        ]
    faithful_index: dict[str, dict[str, Any]] = {}
    if args.graph_mode == "hybrid":
        candidate_names: list[str] = []
        for node_id, _score in ranked[: max(args.top_k * 8, args.seed_k)]:
            node = nodes_by_id[node_id]
            name = str(node.get("name") or node_id)
            if name:
                candidate_names.append(name)
        faithful_index = load_faithful_index(args, candidate_names)

    items = []
    for node_id, score in ranked:
        node = nodes_by_id[node_id]
        if args.declarations_only and node.get("kind") != "Declaration":
            continue
        excerpt = source_excerpt(node, repo_root, args.source_radius)
        if args.require_source and excerpt is None:
            continue
        attrs = node.get("attrs") or {}
        name = str(node.get("name") or node_id)
        faithful_witness = None
        if args.graph_mode == "faithful":
            faithful_witness = {
                "raw_key": node.get("_raw_key"),
                "raw_doc_id": node.get("_raw_doc_id"),
                "scc_id": node.get("scc_id"),
                "scc_key": node.get("scc_key"),
                "witness_backed": True,
                "mode": "raw_graph_source",
            }
        elif args.graph_mode == "hybrid":
            faithful_witness = faithful_index.get(name)
            if args.require_faithful_witness and not faithful_witness:
                continue
        items.append(
            {
                "id": node_id,
                "name": name,
                "module": node.get("module"),
                "kind": node.get("kind"),
                "decl_kind": attrs.get("decl_kind"),
                "doc": attrs.get("doc") or "",
                "file": node.get("file"),
                "line": node.get("line"),
                "rep_depth": node_rep_depth(node),
                "rep_depth_slug": node_rep_depth_slug(node),
                "rep_layer": node_rep_layer(node),
                "rep_layer_description": node_rep_layer_description(node),
                "module_family": node.get("module_family"),
                "type_fingerprint": node.get("typeFingerprint"),
                "score": round(float(score), 6),
                "distance": distances.get(node_id),
                "source_excerpt": excerpt,
                "faithful_witness": faithful_witness,
                "scc_anchor_distance": (
                    scc_distances.get(node.get("scc_id"))
                    if isinstance(node.get("scc_id"), int)
                    else None
                ),
            }
        )
        if len(items) >= args.top_k:
            break

    return {
        "schema": "info_geometry.gravity_context.v1",
        "query": args.query,
        "query_tokens": sorted(query_tokens),
        "query_phrases": phrases,
        "expanded_query_tokens": sorted(expanded_query_tokens),
        "synonym_expansion": {
            "enabled": bool(args.use_equivalence_expansion),
            "dictionary": str(args.equivalence_dictionary) if args.equivalence_dictionary else None,
            "matched_group_count": len(synonym_groups),
            "matched_groups": synonym_groups,
        },
        "graph_source": source,
        "graph_mode": args.graph_mode,
        "repo_root": str(repo_root),
        "seed_count": len(seed_scores),
        "seed_scc_count": len(seed_sccs),
        "scc_anchor_first": bool(args.scc_anchor_first),
        "require_scc_anchor": bool(args.require_scc_anchor),
        "requested_rep_layers": sorted(requested_rep_layers),
        "node_count": len(nodes),
        "edge_count": len(edges),
        "graph_rep_layer_counts": rep_layer_counts(nodes),
        "result_rep_layer_counts": rep_layer_counts(items),
        "top_k": args.top_k,
        "items": items,
        "prompt_policy": {
            "principle": "proven Lean code is gravitational mass",
            "use": "inject these nearby verified declarations before asking a prover model for tactics",
            "promotion_allowed": False,
            "faithful_witness_required": bool(args.require_faithful_witness),
            "scc_anchor_rule": "lexical/synonym match -> anchored SCC -> bounded quotient expansion -> raw witness descent",
        },
    }


def build_context_from_query(
    query: str,
    *,
    repo_root: Path,
    source: str = "auto",
    nodes: Path = DEFAULT_NODES,
    edges: Path = DEFAULT_EDGES,
    arango_url: str = DEFAULT_ARANGO,
    arango_db: str = DEFAULT_DB,
    nodes_collection: str = DEFAULT_NODE_COLLECTION,
    edges_collection: str = DEFAULT_EDGE_COLLECTION,
    limit_nodes: int = 1_000_000,
    limit_edges: int = 2_000_000,
    seed_k: int = 32,
    top_k: int = 8,
    max_hops: int = 2,
    source_radius: int = 4,
    declarations_only: bool = True,
    require_source: bool = True,
    equivalence_dictionary: Path = DEFAULT_EQUIVALENCE_DICTIONARY,
    use_equivalence_expansion: bool = True,
    max_equivalence_groups: int = 8,
    max_equivalence_tokens: int = 64,
    graph_mode: str = DEFAULT_GRAPH_MODE,
    raw_nodes_collection: str = DEFAULT_RAW_NODE_COLLECTION,
    raw_edges_collection: str = DEFAULT_RAW_EDGE_COLLECTION,
    overlay_nodes_collection: str = DEFAULT_OVERLAY_NODE_COLLECTION,
    overlay_edges_collection: str = DEFAULT_OVERLAY_EDGE_COLLECTION,
    require_faithful_witness: bool = True,
    lexical_anchor_weight: float = 40.0,
    scc_anchor_weight: float = 120.0,
    scc_anchor_first: bool = True,
    require_scc_anchor: bool = True,
    rep_layer: list[str] | None = None,
) -> dict[str, Any]:
    """Programmatic entry point for bounded agents."""
    args = argparse.Namespace(
        query=query,
        repo_root=repo_root,
        source=source,
        nodes=nodes,
        edges=edges,
        arango_url=arango_url,
        arango_db=arango_db,
        nodes_collection=nodes_collection,
        edges_collection=edges_collection,
        limit_nodes=limit_nodes,
        limit_edges=limit_edges,
        seed_k=seed_k,
        top_k=top_k,
        max_hops=max_hops,
        source_radius=source_radius,
        declarations_only=declarations_only,
        require_source=require_source,
        min_seed_score=1.0,
        equivalence_dictionary=equivalence_dictionary,
        use_equivalence_expansion=use_equivalence_expansion,
        max_equivalence_groups=max_equivalence_groups,
        max_equivalence_tokens=max_equivalence_tokens,
        graph_mode=graph_mode,
        raw_nodes_collection=raw_nodes_collection,
        raw_edges_collection=raw_edges_collection,
        overlay_nodes_collection=overlay_nodes_collection,
        overlay_edges_collection=overlay_edges_collection,
        require_faithful_witness=require_faithful_witness,
        lexical_anchor_weight=lexical_anchor_weight,
        scc_anchor_weight=scc_anchor_weight,
        scc_anchor_first=scc_anchor_first,
        require_scc_anchor=require_scc_anchor,
        rep_layer=rep_layer or [],
    )
    return build_context(args)


def write_markdown(packet: dict[str, Any], path: Path) -> None:
    lines = [
        "# Gravitational Lean Context",
        "",
        f"- Query: `{packet['query']}`",
        f"- Graph source: `{packet['graph_source']}`",
        f"- Nodes: `{packet['node_count']}`",
        f"- Edges: `{packet['edge_count']}`",
        f"- Synonym groups: `{packet.get('synonym_expansion', {}).get('matched_group_count', 0)}`",
        f"- Requested layers: `{', '.join(packet.get('requested_rep_layers') or []) or 'all'}`",
        f"- Promotion allowed: `false`",
        "",
    ]
    graph_layers = packet.get("graph_rep_layer_counts") or []
    if graph_layers:
        lines.extend(["## Representation Layers", ""])
        for row in graph_layers:
            layer = row.get("rep_layer") or "unlabeled"
            depths = ", ".join(str(depth) for depth in row.get("rep_depths") or [])
            slugs = ", ".join(str(slug) for slug in row.get("rep_depth_slugs") or [])
            detail = f"; depth `{depths}`" if depths else ""
            if slugs:
                detail += f"; slug `{slugs}`"
            lines.append(f"- `{layer}`: `{row.get('count')}`{detail}")
        lines.append("")
    synonym_expansion = packet.get("synonym_expansion") or {}
    if synonym_expansion.get("matched_groups"):
        lines.extend(["## Synonym Expansion", ""])
        for group in synonym_expansion["matched_groups"]:
            lines.extend(
                [
                    f"- `{group.get('id')}` matched `{', '.join(group.get('matched_tokens') or [])}`; "
                    f"added `{', '.join(group.get('added_tokens') or [])}`",
                ]
            )
        lines.append("")
    for index, item in enumerate(packet["items"], 1):
        lines.extend(
            [
                f"## {index}. `{item['id']}`",
                "",
                f"- Score: `{item['score']}`",
                f"- Distance: `{item['distance']}`",
                f"- Module: `{item.get('module')}`",
                f"- Declaration kind: `{item.get('decl_kind')}`",
                f"- Representation layer: `{item.get('rep_layer')}`",
                f"- Representation depth: `{item.get('rep_depth')}`",
                f"- Representation slug: `{item.get('rep_depth_slug')}`",
                f"- File: `{item.get('file')}`",
                f"- Line: `{item.get('line')}`",
                "",
            ]
        )
        if item.get("rep_layer_description"):
            lines.extend([f"Layer note: {item['rep_layer_description']}", ""])
        if item.get("doc"):
            lines.extend(["Doc:", "", item["doc"], ""])
        witness = item.get("faithful_witness")
        if witness:
            lines.extend(
                [
                    "Faithful witness:",
                    "",
                    f"- Raw doc: `{witness.get('raw_doc_id')}`",
                    f"- SCC: `{witness.get('scc_key') or witness.get('scc_id')}`",
                    f"- Witness backed: `{bool(witness.get('witness_backed'))}`",
                    "",
                ]
            )
        excerpt = item.get("source_excerpt")
        if excerpt:
            lines.append("```lean")
            for row in excerpt["lines"]:
                lines.append(f"-- {row['line']}: {row['text']}")
            lines.extend(["```", ""])
    path.write_text("\n".join(lines), encoding="utf-8")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--query", required=True, help="Goal, theorem name, or concept to retrieve context for.")
    parser.add_argument("--repo-root", type=Path, default=repo_root_from(Path.cwd()))
    parser.add_argument("--source", choices=["auto", "arango", "jsonl"], default="auto")
    parser.add_argument("--nodes", type=Path, default=DEFAULT_NODES)
    parser.add_argument("--edges", type=Path, default=DEFAULT_EDGES)
    parser.add_argument("--arango-url", default=DEFAULT_ARANGO)
    parser.add_argument("--arango-db", default=DEFAULT_DB)
    parser.add_argument("--nodes-collection", default=DEFAULT_NODE_COLLECTION)
    parser.add_argument("--edges-collection", default=DEFAULT_EDGE_COLLECTION)
    parser.add_argument(
        "--graph-mode",
        choices=list(GRAPH_MODE_CHOICES),
        default=DEFAULT_GRAPH_MODE,
        help=(
            "unified is the canonical lane: retrieve from raw_info_nodes/raw_info_edges, anchor on topology_overlay, "
            "and carry compact/Hive layers as sidecars only. faithful keeps the raw-only view; hybrid keeps compact ranking "
            "with raw witnesses; compact is projection-only."
        ),
    )
    parser.add_argument("--raw-nodes-collection", default=DEFAULT_RAW_NODE_COLLECTION)
    parser.add_argument("--raw-edges-collection", default=DEFAULT_RAW_EDGE_COLLECTION)
    parser.add_argument("--overlay-nodes-collection", default=DEFAULT_OVERLAY_NODE_COLLECTION)
    parser.add_argument("--overlay-edges-collection", default=DEFAULT_OVERLAY_EDGE_COLLECTION)
    parser.add_argument("--require-faithful-witness", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--limit-nodes", type=int, default=1_000_000)
    parser.add_argument("--limit-edges", type=int, default=2_000_000)
    parser.add_argument("--seed-k", type=int, default=32)
    parser.add_argument("--min-seed-score", type=float, default=1.0)
    parser.add_argument(
        "--lexical-anchor-weight",
        type=float,
        default=40.0,
        help="Secondary weight added to exact lexical seed scores after SCC anchoring.",
    )
    parser.add_argument(
        "--scc-anchor-weight",
        type=float,
        default=120.0,
        help="Primary weight for nodes in SCCs anchored by exact query identifiers.",
    )
    parser.add_argument(
        "--scc-anchor-first",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="In faithful mode, rank from anchored SCC basins before raw-edge propagation.",
    )
    parser.add_argument(
        "--require-scc-anchor",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="In faithful SCC-first mode, return no graph context if no lexical/synonym SCC anchor exists.",
    )
    parser.add_argument("--top-k", type=int, default=8)
    parser.add_argument(
        "--rep-layer",
        action="append",
        default=[],
        help="Restrict returned declarations to a representation layer such as L4_ModularTransport. Repeatable.",
    )
    parser.add_argument("--max-hops", type=int, default=2)
    parser.add_argument("--source-radius", type=int, default=4)
    parser.add_argument("--equivalence-dictionary", type=Path, default=DEFAULT_EQUIVALENCE_DICTIONARY)
    parser.add_argument("--use-equivalence-expansion", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--max-equivalence-groups", type=int, default=8)
    parser.add_argument("--max-equivalence-tokens", type=int, default=64)
    parser.add_argument("--declarations-only", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--require-source", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--md-out", type=Path)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv or sys.argv[1:])
    packet = build_context(args)
    text = json.dumps(packet, indent=2, ensure_ascii=False)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text + "\n", encoding="utf-8")
    if args.md_out:
        args.md_out.parent.mkdir(parents=True, exist_ok=True)
        write_markdown(packet, args.md_out)
    if not args.json_out:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
