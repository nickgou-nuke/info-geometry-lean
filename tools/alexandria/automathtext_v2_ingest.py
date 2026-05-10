#!/usr/bin/env python3
"""Convert AutoMathText-V2 shards/rows into Alexandria theorem-context graph JSONL.

This is a deterministic v0 intake layer.  It preserves raw fragments, then emits
smaller theorem-context chunks, entities, typed triples, theorem-shape rows, and
binder/de-Bruijn-style expression graph edges.  The output is GraphRAG context
material only: it is not proof authority and must be descended back to raw rows
and Lean build gates before any theorem promotion.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import math
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable, Iterator

SCHEMA_PREFIX = "info_geometry.automathtext_v2"
DEFAULT_OPERATOR_TERMS = (
    "Krein space",
    "indefinite inner product",
    "fundamental symmetry",
    "J-self-adjoint",
    "self-adjoint",
    "adjoint",
    "bounded operator",
    "projection",
    "projector",
    "Moore-Penrose",
    "Drazin",
    "closed range",
    "kernel",
    "range",
    "orthogonal complement",
    "Pontryagin space",
)
OPERATOR_CORRIDOR_TERMS = tuple(term.lower() for term in DEFAULT_OPERATOR_TERMS) + (
    "krein",
    "j-self-adjoint",
    "star projection",
    "positive operator",
    "inverse",
)
THEOREM_MARKERS = (
    "theorem",
    "lemma",
    "proposition",
    "corollary",
    "definition",
    "proof",
    "assume",
    "suppose",
    "there exists",
    "for all",
    "∀",
    "∃",
)
BINDER_RE = re.compile(
    r"(?:(?:for\s+(?:all|every)|∀)\s+|(?:there\s+exists|exists|∃)\s+)([A-Za-z][A-Za-z0-9_']*)",
    re.IGNORECASE,
)
SYMBOL_RE = re.compile(r"\b[A-Z][A-Za-z0-9_']{0,32}\b|[$][^$]{1,120}[$]")
LATEX_RE = re.compile(r"\$[^$]{1,400}\$|\\\([^)]{1,400}\\\)|\\\[[\s\S]{1,800}?\\\]")
WORD_RE = re.compile(r"[A-Za-z][A-Za-z0-9_\-']*")


@dataclass(frozen=True)
class Fragment:
    key: str
    source_dataset: str
    source_config: str | None
    source_domain: str | None
    source_id: str
    url: str | None
    language: str | None
    text: str
    tokens: int | None
    score: float | None
    meta: dict[str, Any]
    ingestion_run_id: str
    ancestry_hash: str
    parent_id: str | None


def stable_hash(*parts: Any, size: int = 16) -> str:
    payload = json.dumps(parts, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
    return hashlib.blake2b(payload.encode("utf-8"), digest_size=size).hexdigest()


def load_jsonl(path: Path) -> Iterator[dict[str, Any]]:
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            row = json.loads(line)
            if isinstance(row, dict):
                yield row


def load_parquet(path: Path, *, limit: int | None = None) -> Iterator[dict[str, Any]]:
    try:
        import pyarrow.parquet as pq  # type: ignore
    except ImportError as exc:
        raise SystemExit("Parquet input requires pyarrow. Use --input-jsonl or install pyarrow in the venv.") from exc
    parquet = pq.ParquetFile(path)
    count = 0
    for batch in parquet.iter_batches():
        for row in batch.to_pylist():
            if isinstance(row, dict):
                yield row
                count += 1
                if limit is not None and count >= limit:
                    return


def iter_rows(paths: list[Path], *, limit: int | None) -> Iterator[tuple[Path, dict[str, Any]]]:
    count = 0
    for path in paths:
        suffix = path.suffix.lower()
        if suffix in {".jsonl", ".json"}:
            source_iter = load_jsonl(path) if suffix == ".jsonl" else iter(json.loads(path.read_text(encoding="utf-8")))
        elif suffix == ".parquet":
            source_iter = load_parquet(path, limit=None if limit is None else limit - count)
        else:
            continue
        for row in source_iter:
            yield path, row
            count += 1
            if limit is not None and count >= limit:
                return


def parse_meta(raw: Any) -> dict[str, Any]:
    if isinstance(raw, dict):
        return raw
    if isinstance(raw, str) and raw.strip():
        try:
            obj = json.loads(raw)
            return obj if isinstance(obj, dict) else {"raw": raw}
        except Exception:
            return {"raw": raw}
    return {}


def coerce_float(value: Any) -> float | None:
    try:
        if value is None:
            return None
        out = float(value)
        if math.isnan(out) or math.isinf(out):
            return None
        return out
    except Exception:
        return None


def coerce_int(value: Any) -> int | None:
    try:
        if value is None:
            return None
        return int(value)
    except Exception:
        return None


def row_to_fragment(row: dict[str, Any], *, source_path: Path, dataset: str, run_id: str) -> Fragment | None:
    text = str(row.get("text") or row.get("content") or row.get("problem") or row.get("prompt") or "").strip()
    if not text:
        return None
    source_path = Path(str(row.get("__automath_source_file") or row.get("_alexandria_source_file") or source_path))
    meta = parse_meta(row.get("meta"))
    source_id = str(row.get("id") or row.get("source_id") or row.get("url") or stable_hash(source_path.as_posix(), text[:256]))
    source_config = str(meta.get("domain") or row.get("config") or source_path.parts[-3] if len(source_path.parts) >= 3 else "") or None
    source_domain = str(meta.get("source") or row.get("source") or row.get("domain_prefix") or "") or None
    key = "frag_" + stable_hash(dataset, source_config, source_id, text[:512])
    ancestry_hash = stable_hash("raw_fragment", dataset, source_path.as_posix(), source_config, source_id, text, size=32)
    parent_id = row.get("parent_id") or row.get("parent") or meta.get("parent_id") or meta.get("parent")
    return Fragment(
        key=key,
        source_dataset=dataset,
        source_config=source_config,
        source_domain=source_domain,
        source_id=source_id,
        url=str(row.get("url")) if row.get("url") else None,
        language=str(row.get("language") or row.get("lang") or "") or None,
        text=text,
        tokens=coerce_int(row.get("tokens")),
        score=coerce_float(row.get("score") or meta.get("score") or meta.get("ori_score")),
        meta=meta,
        ingestion_run_id=run_id,
        ancestry_hash=ancestry_hash,
        parent_id=str(parent_id) if parent_id else None,
    )


def split_chunks(text: str, *, max_chars: int, overlap_chars: int) -> list[str]:
    paras = [p.strip() for p in re.split(r"\n\s*\n", text) if p.strip()]
    chunks: list[str] = []
    current = ""
    for para in paras or [text]:
        if len(para) > max_chars:
            start = 0
            while start < len(para):
                chunks.append(para[start : start + max_chars].strip())
                start += max(1, max_chars - overlap_chars)
            continue
        if current and len(current) + 2 + len(para) > max_chars:
            chunks.append(current.strip())
            tail = current[-overlap_chars:].strip() if overlap_chars > 0 else ""
            current = (tail + "\n\n" + para).strip() if tail else para
        else:
            current = (current + "\n\n" + para).strip() if current else para
    if current:
        chunks.append(current.strip())
    return [c for c in chunks if c]


def chunk_kind(text: str) -> str:
    low = text.lower()[:500]
    for kind in ("theorem", "lemma", "proposition", "corollary", "definition", "proof", "example"):
        if re.search(rf"\b{kind}\b", low):
            return kind
    if LATEX_RE.search(text):
        return "formula"
    return "prose"


def normalized_entity(surface: str) -> str:
    return re.sub(r"\s+", " ", surface.strip().lower())


def entity_type(surface: str) -> str:
    low = surface.lower()
    if "space" in low:
        return "space"
    if "operator" in low or "projection" in low or "projector" in low or "adjoint" in low:
        return "operator"
    if surface.startswith("$"):
        return "notation"
    if surface[:1].isupper() and len(surface) <= 4:
        return "symbol"
    return "concept"


def extract_entities(text: str, extra_terms: list[str]) -> list[dict[str, Any]]:
    found: dict[str, dict[str, Any]] = {}
    terms = list(DEFAULT_OPERATOR_TERMS) + extra_terms
    low = text.lower()
    for term in terms:
        if term.lower() in low:
            norm = normalized_entity(term)
            found[norm] = {
                "entityType": entity_type(term),
                "surface": term,
                "normalized": norm,
                "confidence": 0.95,
                "method": "seed_lexicon",
            }
    for match in SYMBOL_RE.finditer(text):
        surface = match.group(0).strip()
        if len(surface) < 2:
            continue
        norm = normalized_entity(surface)
        found.setdefault(
            norm,
            {
                "entityType": entity_type(surface),
                "surface": surface,
                "normalized": norm,
                "confidence": 0.55,
                "method": "symbol_regex",
            },
        )
    return list(found.values())


def theorem_like_score(text: str) -> float:
    low = text.lower()
    score = 0.0
    for marker in THEOREM_MARKERS:
        if marker in low or marker in text:
            score += 0.12
    if "->" in text or "→" in text or "implies" in low:
        score += 0.18
    if LATEX_RE.search(text):
        score += 0.12
    return min(score, 1.0)


def proof_like_score(text: str) -> float:
    low = text.lower()
    markers = ["proof", "therefore", "hence", "by lemma", "it follows", "we obtain", "qed"]
    return min(sum(0.16 for m in markers if m in low), 1.0)


def extract_binder_graph(chunk_key: str, text: str) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[str]]:
    nodes: list[dict[str, Any]] = []
    edges: list[dict[str, Any]] = []
    binders: list[tuple[str, str]] = []
    for depth, match in enumerate(BINDER_RE.finditer(text)):
        var = match.group(1)
        binder_key = "expr_" + stable_hash(chunk_key, "binder", depth, var)
        nodes.append(
            {
                "_key": binder_key,
                "schema": f"{SCHEMA_PREFIX}.expr_node.v1",
                "kind": "binder",
                "surface": var,
                "binderDepth": depth + 1,
                "source_chunk": chunk_key,
            }
        )
        binders.append((var, binder_key))
    words = list(WORD_RE.finditer(text))[:400]
    for idx, match in enumerate(words):
        surface = match.group(0)
        for rev_depth, (var, binder_key) in enumerate(reversed(binders)):
            if surface == var:
                bvar_key = "expr_" + stable_hash(chunk_key, "bvar", idx, surface, binder_key)
                debruijn_idx = rev_depth
                nodes.append(
                    {
                        "_key": bvar_key,
                        "schema": f"{SCHEMA_PREFIX}.expr_node.v1",
                        "kind": "bvar",
                        "surface": surface,
                        "deBruijnIdx": debruijn_idx,
                        "source_chunk": chunk_key,
                    }
                )
                edges.append(
                    {
                        "_key": "expr_edge_" + stable_hash(chunk_key, bvar_key, binder_key, "bound_by"),
                        "_from": f"automath_expr_nodes/{bvar_key}",
                        "_to": f"automath_expr_nodes/{binder_key}",
                        "schema": f"{SCHEMA_PREFIX}.expr_edge.v1",
                        "predicate": "bound_by",
                        "deBruijnIdx": debruijn_idx,
                        "binderDepth": len(binders),
                        "source_chunk": chunk_key,
                        "authority": "heuristic_text_binder_graph",
                    }
                )
                break
    return nodes, edges, [var for var, _ in binders]


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]], *, gzip_output: bool = False) -> int:
    if gzip_output and path.suffix != ".gz":
        path = path.with_suffix(path.suffix + ".gz")
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    opener = gzip.open if gzip_output else open
    with opener(path, "wt", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
            count += 1
    return count


def row_text(row: dict[str, Any]) -> str:
    return str(row.get("text") or row.get("content") or row.get("problem") or row.get("prompt") or "")


def operator_corridor_hits(text: str) -> list[str]:
    low = text.lower()
    return [term for term in OPERATOR_CORRIDOR_TERMS if term in low]


def has_theorem_marker(text: str) -> bool:
    low = text.lower()
    return any(marker in low or marker in text for marker in THEOREM_MARKERS)


def with_ancestry(
    row: dict[str, Any],
    *,
    ancestry_hash: str,
    parent_ancestry_hash: str | None,
    ancestry_path: list[str],
) -> dict[str, Any]:
    """Attach uniform chain-of-custody metadata to a graph row."""
    row["ancestry_hash"] = ancestry_hash
    row["parent_ancestry_hash"] = parent_ancestry_hash
    row["ancestry_path"] = ancestry_path
    return row


def lexical_tokens(text: str, *, limit: int = 80) -> list[str]:
    seen: dict[str, None] = {}
    for match in WORD_RE.finditer(text):
        token = match.group(0).lower().strip("-_'")
        if len(token) >= 3:
            seen.setdefault(token, None)
        if len(seen) >= limit:
            break
    return list(seen)


def _doc_key(fragment: dict[str, Any]) -> str:
    return "doc_" + stable_hash("alexandria_doc", fragment.get("_key") or fragment.get("key"), fragment.get("source_id"))


def _section_key(fragment: dict[str, Any]) -> str:
    return "section_" + stable_hash("alexandria_section", _doc_key(fragment), fragment.get("source_id"))


def build_alexandria_rows(
    *,
    fragments: list[dict[str, Any]],
    chunks: list[dict[str, Any]],
    entities: list[dict[str, Any]],
    triples: list[dict[str, Any]],
    dataset: str,
    run_id: str,
) -> dict[str, list[dict[str, Any]]]:
    """Project AutoMathText v0 rows onto the existing Alexandria ranker schema.

    The `automath_*` rows remain the full epistemic ancestry graph.  These
    `alexandria_*` rows are a compatibility projection for `graph_context_rank.py`:
    chunks/entities/mention edges/adjacent chunk flow/entity relation candidates.
    """
    fragment_by_key = {str(row.get("_key") or row.get("key")): row for row in fragments}
    chunk_by_key = {str(row.get("_key") or row.get("key")): row for row in chunks}
    entity_by_key = {str(row.get("_key") or row.get("key")): row for row in entities}

    documents: list[dict[str, Any]] = []
    sections: list[dict[str, Any]] = []
    document_section_edges: list[dict[str, Any]] = []
    for fragment in fragments:
        fkey = str(fragment.get("_key") or fragment.get("key"))
        doc_key = _doc_key(fragment)
        section_key = _section_key(fragment)
        source_domain = fragment.get("source_domain") or fragment.get("source_config")
        source_name = fragment.get("meta", {}).get("source") if isinstance(fragment.get("meta"), dict) else None
        documents.append(
            {
                "_key": doc_key,
                "key": doc_key,
                "schema": "info_geometry.alexandria.automathtext_v2.v1",
                "sourceKind": "automathtext_v2_fragment",
                "sourceDataset": dataset,
                "sourceDomain": source_domain,
                "sourceName": source_name,
                "domainPrefix": fragment.get("source_config"),
                "originalId": fragment.get("source_id"),
                "title": str(fragment.get("source_id") or fkey),
                "url": fragment.get("url"),
                "score": fragment.get("score"),
                "tokens": fragment.get("tokens"),
                "textHash": fragment.get("text_hash") or stable_hash(fragment.get("text", ""), size=32),
                "meta": fragment.get("meta", {}),
                "ancestry_hash": fragment.get("ancestry_hash"),
                "ancestry_path": fragment.get("ancestry_path", []),
                "authority": "raw_text_context_only",
                "ingestion_run_id": run_id,
            }
        )
        sections.append(
            {
                "_key": section_key,
                "key": section_key,
                "documentKey": doc_key,
                "title": "AutoMathText fragment",
                "level": 1,
                "ordinal": 1,
                "sourceDomain": source_domain,
                "ancestry_hash": fragment.get("ancestry_hash"),
                "ancestry_path": fragment.get("ancestry_path", []),
                "authority": "raw_text_context_only",
            }
        )
        document_section_edges.append(
            {
                "_key": "docsec_" + stable_hash(doc_key, section_key),
                "_from": f"alexandria_documents/{doc_key}",
                "_to": f"alexandria_sections/{section_key}",
                "relationType": "contains_section",
                "ordinal": 1,
                "weight": 1.0,
                "authority": "raw_text_context_only",
            }
        )

    chunk_ordinals: dict[str, int] = {}
    alex_chunks: list[dict[str, Any]] = []
    for chunk in chunks:
        ckey = str(chunk.get("_key") or chunk.get("key"))
        fragment = fragment_by_key.get(str(chunk.get("source_fragment") or chunk.get("fragment_key")), {})
        fkey = str(fragment.get("_key") or fragment.get("key") or chunk.get("source_fragment") or chunk.get("fragment_key"))
        chunk_ordinals[fkey] = chunk_ordinals.get(fkey, 0) + 1
        doc_key = _doc_key(fragment) if fragment else "doc_" + stable_hash("missing_fragment", fkey)
        section_key = _section_key(fragment) if fragment else "section_" + stable_hash("missing_fragment", fkey)
        provenance = {
            "schema": "info_geometry.alexandria.automathtext_v2.v1",
            "sourceDataset": dataset,
            "sourceDomain": fragment.get("source_domain") or fragment.get("source_config"),
            "domainPrefix": fragment.get("source_config"),
            "sourceName": fragment.get("meta", {}).get("source") if isinstance(fragment.get("meta"), dict) else None,
            "originalId": fragment.get("source_id"),
            "url": fragment.get("url"),
            "sourceFragment": fkey,
        }
        alex_chunks.append(
            {
                "_key": ckey,
                "key": ckey,
                "documentKey": doc_key,
                "sectionKey": section_key,
                "title": "AutoMathText fragment",
                "ordinal": chunk_ordinals[fkey],
                "chunkKind": chunk.get("chunkKind", "chunk"),
                "text": chunk.get("text", ""),
                "tokens": lexical_tokens(str(chunk.get("text", ""))),
                "latex_spans": chunk.get("latex_spans", []),
                "code_spans": [],
                "theorem_like_score": chunk.get("theorem_like_score", 0.0),
                "proof_like_score": chunk.get("proof_like_score", 0.0),
                "quality_score": chunk.get("quality_score"),
                "provenance": provenance,
                "source_fragment": fkey,
                "ancestry_hash": chunk.get("ancestry_hash"),
                "parent_ancestry_hash": chunk.get("parent_ancestry_hash"),
                "ancestry_path": chunk.get("ancestry_path", []),
                "authority": "raw_text_context_only",
            }
        )

    section_chunk_edges: list[dict[str, Any]] = []
    for chunk in alex_chunks:
        section_chunk_edges.append(
            {
                "_key": "secchunk_" + stable_hash(chunk["sectionKey"], chunk["_key"]),
                "_from": f"alexandria_sections/{chunk['sectionKey']}",
                "_to": f"alexandria_chunks/{chunk['_key']}",
                "relationType": "contains_chunk",
                "ordinal": chunk.get("ordinal", 0),
                "weight": 1.0,
                "authority": "raw_text_context_only",
            }
        )

    alex_entities: dict[str, dict[str, Any]] = {}
    chunk_entity_edges: list[dict[str, Any]] = []
    entity_mentions_by_chunk: dict[str, list[str]] = {}
    for triple in triples:
        if triple.get("predicate") != "mentions":
            continue
        ckey = str(triple.get("_from", "")).split("/", 1)[-1]
        ekey = str(triple.get("_to", "")).split("/", 1)[-1]
        entity = entity_by_key.get(ekey)
        if not entity or ckey not in chunk_by_key:
            continue
        alex_entities.setdefault(
            ekey,
            {
                "_key": ekey,
                "key": ekey,
                "chunkKey": ckey,
                "entityType": entity.get("entityType"),
                "surface": entity.get("surface"),
                "normalized": entity.get("normalized"),
                "confidence": entity.get("confidence", triple.get("confidence", 0.5)),
                "domain": fragment_by_key.get(str(chunk_by_key[ckey].get("source_fragment")), {}).get("source_domain"),
                "sourceDataset": dataset,
                "source_chunk": ckey,
                "source_fragment": entity.get("source_fragment"),
                "ancestry_hash": entity.get("ancestry_hash"),
                "ancestry_path": entity.get("ancestry_path", []),
                "authority": "raw_text_entity_candidate",
            },
        )
        chunk_entity_edges.append(
            {
                "_key": "chunkent_" + stable_hash(ckey, ekey, triple.get("_key")),
                "_from": f"alexandria_chunks/{ckey}",
                "_to": f"alexandria_entities/{ekey}",
                "relationType": "mentions",
                "entityType": entity.get("entityType"),
                "confidence": triple.get("confidence", entity.get("confidence", 0.5)),
                "weight": triple.get("confidence", entity.get("confidence", 0.5)),
                "authority": "raw_text_context_only",
                "ancestry_hash": triple.get("ancestry_hash"),
                "ancestry_path": triple.get("ancestry_path", []),
            }
        )
        entity_mentions_by_chunk.setdefault(ckey, []).append(ekey)

    adjacent_edges: list[dict[str, Any]] = []
    automath_debruijn_edges: list[dict[str, Any]] = []
    for triple in triples:
        if triple.get("predicate") != "next_chunk":
            continue
        src = str(triple.get("_from", "")).split("/", 1)[-1]
        dst = str(triple.get("_to", "")).split("/", 1)[-1]
        if src not in chunk_by_key or dst not in chunk_by_key:
            continue
        src_tokens = set(lexical_tokens(str(chunk_by_key[src].get("text", ""))))
        dst_tokens = set(lexical_tokens(str(chunk_by_key[dst].get("text", ""))))
        overlap = sorted(src_tokens & dst_tokens)[:12]
        adjacent_edges.append(
            {
                "_key": "chunkadj_" + stable_hash(src, dst),
                "_from": f"alexandria_chunks/{src}",
                "_to": f"alexandria_chunks/{dst}",
                "relationType": "next_chunk",
                "weight": 1.0,
                "authority": "raw_text_context_only",
            }
        )
        automath_debruijn_edges.append(
            {
                "_key": "dbj_" + stable_hash(src, dst, overlap),
                "_from": f"alexandria_chunks/{src}",
                "_to": f"alexandria_chunks/{dst}",
                "edgeKind": "debruijn_sequence",
                "relationType": "logical_flow",
                "direction": "semantic_sequence_overlap" if overlap else "document_order",
                "exact_debruijn_overlap": False,
                "k_mer_size": 3,
                "overlap_symbols": overlap,
                "state_size": 2,
                "transition_probability": 0.45 + min(0.2, 0.05 * len(overlap)),
                "weight": 0.45 + min(0.2, 0.05 * len(overlap)),
                "sourceDocumentKey": alex_chunks[0].get("documentKey") if alex_chunks else None,
                "authority": "heuristic_text_binder_graph",
            }
        )

    entity_relation_edges: list[dict[str, Any]] = []
    for ckey, ekeys in sorted(entity_mentions_by_chunk.items()):
        unique = list(dict.fromkeys(ekeys))[:10]
        if len(unique) < 2:
            continue
        chunk_text = str(chunk_by_key.get(ckey, {}).get("text", ""))
        lowered = chunk_text.lower()
        relation_type = "uses_candidate"
        weight = 0.42
        if " if " in f" {lowered} " and " then " in f" {lowered} ":
            relation_type = "implies_candidate"
            weight = 0.62
        elif "definition" in lowered or "defined" in lowered:
            relation_type = "defines_candidate"
            weight = 0.58
        elif "assume" in lowered or "suppose" in lowered:
            relation_type = "assumes_candidate"
            weight = 0.5
        for src in unique:
            for dst in unique:
                if src == dst:
                    continue
                entity_relation_edges.append(
                    {
                        "_key": "rel_" + stable_hash(ckey, src, dst, relation_type),
                        "_from": f"alexandria_entities/{src}",
                        "_to": f"alexandria_entities/{dst}",
                        "chunkKey": ckey,
                        "relationType": relation_type,
                        "evidence": chunk_text[:240],
                        "weight": weight,
                        "authority": "raw_text_context_only_candidate",
                    }
                )

    return {
        "alexandria_documents": documents,
        "alexandria_sections": sections,
        "alexandria_chunks": alex_chunks,
        "alexandria_entities": list(alex_entities.values()),
        "alexandria_document_section_edges": document_section_edges,
        "alexandria_section_chunk_edges": section_chunk_edges,
        "alexandria_chunk_entity_edges": chunk_entity_edges,
        "alexandria_chunk_adjacent_edges": adjacent_edges,
        "alexandria_entity_relation_edges": entity_relation_edges,
        "automath_debruijn_edges": automath_debruijn_edges,
    }


def build_outputs(
    *,
    input_paths: list[Path],
    output_dir: Path,
    dataset: str,
    run_id: str,
    max_rows: int | None,
    max_chars: int,
    overlap_chars: int,
    entity_term: list[str],
    gzip_output: bool = False,
) -> dict[str, Any]:
    fragments: list[dict[str, Any]] = []
    chunks: list[dict[str, Any]] = []
    entities: dict[str, dict[str, Any]] = {}
    triples: list[dict[str, Any]] = []
    expr_nodes: list[dict[str, Any]] = []
    expr_edges: list[dict[str, Any]] = []
    theorem_shapes: list[dict[str, Any]] = []
    ancestry_edges: list[dict[str, Any]] = []
    overlay_nodes: dict[str, dict[str, Any]] = {}
    overlay_edges: list[dict[str, Any]] = []

    for source_path, row in iter_rows(input_paths, limit=max_rows):
        effective_source_path = Path(str(row.get("__automath_source_file") or row.get("_alexandria_source_file") or source_path))
        fragment = row_to_fragment(row, source_path=effective_source_path, dataset=dataset, run_id=run_id)
        if fragment is None:
            continue
        fragment_row = {"schema": f"{SCHEMA_PREFIX}.fragment.v1", **asdict(fragment)}
        fragment_row["_key"] = fragment.key
        fragment_row["source_file"] = effective_source_path.as_posix()
        fragment_row["ancestry_path"] = [fragment.ancestry_hash]
        fragment_row["parent_ancestry_hash"] = None
        fragment_row["authority"] = "raw_text_context_only"
        fragments.append(fragment_row)
        previous_chunk_key: str | None = None
        for idx, chunk_text in enumerate(split_chunks(fragment.text, max_chars=max_chars, overlap_chars=overlap_chars)):
            chunk_key = "chunk_" + stable_hash(fragment.key, idx, chunk_text[:256])
            chunk_ancestry_hash = stable_hash(fragment.ancestry_hash, "chunk", idx, chunk_text, size=32)
            latex_spans = [m.group(0) for m in LATEX_RE.finditer(chunk_text)][:20]
            kind = chunk_kind(chunk_text)
            chunk_row = {
                "_key": chunk_key,
                "schema": f"{SCHEMA_PREFIX}.chunk.v1",
                "fragment_key": fragment.key,
                "chunk_index": idx,
                "chunkKind": kind,
                "text": chunk_text,
                "text_hash": stable_hash(chunk_text, size=32),
                "latex_spans": latex_spans,
                "theorem_like_score": theorem_like_score(chunk_text),
                "proof_like_score": proof_like_score(chunk_text),
                "quality_score": fragment.score,
                "source_fragment": fragment.key,
                "ancestry_hash": chunk_ancestry_hash,
                "parent_ancestry_hash": fragment.ancestry_hash,
                "ancestry_path": [fragment.ancestry_hash, chunk_ancestry_hash],
                "ingestion_run_id": run_id,
                "authority": "raw_text_context_only",
            }
            chunks.append(chunk_row)
            ancestry_edges.append(
                {
                    "_key": "ancestry_" + stable_hash(fragment.key, chunk_key, "fragment_to_chunk"),
                    "_from": f"automath_fragments/{fragment.key}",
                    "_to": f"automath_chunks/{chunk_key}",
                    "schema": f"{SCHEMA_PREFIX}.ancestry_edge.v1",
                    "role": "fragment_to_chunk",
                    "source_ancestry_hash": fragment.ancestry_hash,
                    "target_ancestry_hash": chunk_ancestry_hash,
                    "ancestry_path": [fragment.ancestry_hash, chunk_ancestry_hash],
                    "authority": "raw_witness_descent",
                }
            )
            triples.append(
                {
                    "_key": "triple_" + stable_hash(fragment.key, chunk_key, "has_chunk"),
                    "_from": f"automath_fragments/{fragment.key}",
                    "_to": f"automath_chunks/{chunk_key}",
                    "schema": f"{SCHEMA_PREFIX}.triple.v1",
                    "predicate": "has_chunk",
                    "confidence": 1.0,
                    "extraction_method": "deterministic_chunking_v0",
                    "source_fragment": fragment.key,
                    "authority": "raw_text_context_only",
                }
            )
            if previous_chunk_key:
                triples.append(
                    {
                        "_key": "triple_" + stable_hash(previous_chunk_key, chunk_key, "next_chunk"),
                        "_from": f"automath_chunks/{previous_chunk_key}",
                        "_to": f"automath_chunks/{chunk_key}",
                        "schema": f"{SCHEMA_PREFIX}.triple.v1",
                        "predicate": "next_chunk",
                        "confidence": 1.0,
                        "extraction_method": "document_order_v0",
                        "source_fragment": fragment.key,
                        "authority": "raw_text_context_only",
                    }
                )
            previous_chunk_key = chunk_key

            chunk_entities = extract_entities(chunk_text, entity_term)
            for ent in chunk_entities:
                ent_key = "ent_" + stable_hash(ent["entityType"], ent["normalized"])
                entities.setdefault(
                    ent_key,
                    {
                        "_key": ent_key,
                        "schema": f"{SCHEMA_PREFIX}.entity.v1",
                        **ent,
                        "source_chunk": chunk_key,
                        "source_fragment": fragment.key,
                        "ancestry_hash": stable_hash(chunk_ancestry_hash, "entity", ent_key, size=32),
                        "parent_ancestry_hash": chunk_ancestry_hash,
                        "ancestry_path": [
                            fragment.ancestry_hash,
                            chunk_ancestry_hash,
                            stable_hash(chunk_ancestry_hash, "entity", ent_key, size=32),
                        ],
                        "authority": "raw_text_entity_candidate",
                    },
                )
                triples.append(
                    {
                        "_key": "triple_" + stable_hash(chunk_key, ent_key, "mentions"),
                        "_from": f"automath_chunks/{chunk_key}",
                        "_to": f"automath_entities/{ent_key}",
                        "schema": f"{SCHEMA_PREFIX}.triple.v1",
                        "predicate": "mentions",
                        "confidence": ent.get("confidence", 0.5),
                        "extraction_method": ent.get("method", "entity_extraction_v0"),
                        "source_chunk": chunk_key,
                        "source_fragment": fragment.key,
                        "witness_text": chunk_text[:240],
                        "authority": "raw_text_context_only",
                    }
                )

            nodes, edges, binder_vars = extract_binder_graph(chunk_key, chunk_text)
            for node in nodes:
                node["parent_ancestry_hash"] = chunk_ancestry_hash
                node["ancestry_hash"] = stable_hash(chunk_ancestry_hash, "expr_node", node["_key"], size=32)
                node["ancestry_path"] = [fragment.ancestry_hash, chunk_ancestry_hash, node["ancestry_hash"]]
                ancestry_edges.append(
                    {
                        "_key": "ancestry_" + stable_hash(chunk_key, node["_key"], "chunk_to_expr_node"),
                        "_from": f"automath_chunks/{chunk_key}",
                        "_to": f"automath_expr_nodes/{node['_key']}",
                        "schema": f"{SCHEMA_PREFIX}.ancestry_edge.v1",
                        "role": "chunk_to_expr_node",
                        "source_ancestry_hash": chunk_ancestry_hash,
                        "target_ancestry_hash": node["ancestry_hash"],
                        "ancestry_path": node["ancestry_path"],
                        "authority": "raw_witness_descent",
                    }
                )
            expr_nodes.extend(nodes)
            expr_edges.extend(edges)
            if chunk_row["theorem_like_score"] >= 0.12 or kind in {"theorem", "lemma", "proposition", "definition", "corollary"}:
                alpha_hash = stable_hash(
                    kind,
                    [e.get("normalized") for e in chunk_entities[:12]],
                    len(binder_vars),
                    bool(latex_spans),
                    "->" in chunk_text or "→" in chunk_text,
                    size=20,
                )
                shape_key = "shape_" + stable_hash(chunk_key, alpha_hash)
                shape_ancestry_hash = stable_hash(chunk_ancestry_hash, "theorem_shape", alpha_hash, size=32)
                theorem_shapes.append(
                    {
                        "_key": shape_key,
                        "schema": f"{SCHEMA_PREFIX}.theorem_shape.v1",
                        "source_chunk": chunk_key,
                        "source_fragment": fragment.key,
                        "formal_system": "informal_or_latex",
                        "normalized_statement": re.sub(r"\s+", " ", chunk_text[:1200]).strip(),
                        "binder_signature": ["binder" for _ in binder_vars],
                        "binder_variables": binder_vars,
                        "debruijn_histogram": [sum(1 for e in edges if e.get("deBruijnIdx") == i) for i in range(max(1, len(binder_vars)))],
                        "head_symbol": "implication" if ("->" in chunk_text or "→" in chunk_text or "implies" in chunk_text.lower()) else kind,
                        "entity_keys": ["ent_" + stable_hash(e["entityType"], e["normalized"]) for e in chunk_entities],
                        "formula_hash": stable_hash(latex_spans, size=20) if latex_spans else None,
                        "alpha_hash": alpha_hash,
                        "ancestry_hash": shape_ancestry_hash,
                        "parent_ancestry_hash": chunk_ancestry_hash,
                        "ancestry_path": [fragment.ancestry_hash, chunk_ancestry_hash, shape_ancestry_hash],
                        "authority": "theorem_shape_candidate",
                    }
                )
                ancestry_edges.append(
                    {
                        "_key": "ancestry_" + stable_hash(chunk_key, shape_key, "chunk_to_theorem_shape"),
                        "_from": f"automath_chunks/{chunk_key}",
                        "_to": f"automath_theorem_shapes/{shape_key}",
                        "schema": f"{SCHEMA_PREFIX}.ancestry_edge.v1",
                        "role": "chunk_to_theorem_shape",
                        "source_ancestry_hash": chunk_ancestry_hash,
                        "target_ancestry_hash": shape_ancestry_hash,
                        "ancestry_path": [fragment.ancestry_hash, chunk_ancestry_hash, shape_ancestry_hash],
                        "authority": "raw_witness_descent",
                    }
                )
                triples.append(
                    {
                        "_key": "triple_" + stable_hash(chunk_key, shape_key, "has_theorem_shape"),
                        "_from": f"automath_chunks/{chunk_key}",
                        "_to": f"automath_theorem_shapes/{shape_key}",
                        "schema": f"{SCHEMA_PREFIX}.triple.v1",
                        "predicate": "has_theorem_shape",
                        "confidence": chunk_row["theorem_like_score"],
                        "extraction_method": "theorem_shape_heuristic_v0",
                        "source_chunk": chunk_key,
                        "source_fragment": fragment.key,
                        "authority": "theorem_shape_candidate",
                    }
                )
                basin_key = "basin_" + stable_hash("alpha", alpha_hash[:12])
                overlay_nodes.setdefault(
                    basin_key,
                    {
                        "_key": basin_key,
                        "schema": f"{SCHEMA_PREFIX}.overlay_node.v1",
                        "overlay_kind": "theorem_shape_alpha_basin",
                        "representative": alpha_hash,
                        "authority": "retrieval_overlay_only",
                    },
                )
                overlay_edges.append(
                    {
                        "_key": "overlay_edge_" + stable_hash(shape_key, basin_key, "member_of_alpha_basin"),
                        "_from": f"automath_theorem_shapes/{shape_key}",
                        "_to": f"automath_overlay_nodes/{basin_key}",
                        "schema": f"{SCHEMA_PREFIX}.overlay_edge.v1",
                        "role": "member_of_alpha_basin",
                        "witness_chunk_keys": [chunk_key],
                        "authority": "retrieval_overlay_only",
                    }
                )

    ancestry_path_by_ref: dict[str, list[str]] = {}
    ancestry_hash_by_ref: dict[str, str] = {}
    for collection, rows in [
        ("automath_fragments", fragments),
        ("automath_chunks", chunks),
        ("automath_entities", list(entities.values())),
        ("automath_expr_nodes", expr_nodes),
        ("automath_theorem_shapes", theorem_shapes),
        ("automath_overlay_nodes", list(overlay_nodes.values())),
    ]:
        for row in rows:
            key = row.get("_key") or row.get("key")
            if not key:
                continue
            ref = f"{collection}/{key}"
            if row.get("ancestry_hash"):
                ancestry_hash_by_ref[ref] = str(row["ancestry_hash"])
            if isinstance(row.get("ancestry_path"), list):
                ancestry_path_by_ref[ref] = list(row["ancestry_path"])

    for triple in triples:
        if triple.get("ancestry_hash"):
            continue
        from_ref = str(triple.get("_from", ""))
        parent_path = ancestry_path_by_ref.get(from_ref, [])
        parent_hash = ancestry_hash_by_ref.get(from_ref)
        edge_hash = stable_hash(
            "triple",
            triple.get("_from"),
            triple.get("predicate"),
            triple.get("_to"),
            size=32,
        )
        with_ancestry(
            triple,
            ancestry_hash=edge_hash,
            parent_ancestry_hash=parent_hash,
            ancestry_path=[*parent_path, edge_hash] if parent_path else [edge_hash],
        )

    for edge in expr_edges:
        if edge.get("ancestry_hash"):
            continue
        from_ref = str(edge.get("_from", ""))
        parent_path = ancestry_path_by_ref.get(from_ref, [])
        parent_hash = ancestry_hash_by_ref.get(from_ref)
        edge_hash = stable_hash("expr_edge", edge.get("_from"), edge.get("predicate"), edge.get("_to"), size=32)
        with_ancestry(
            edge,
            ancestry_hash=edge_hash,
            parent_ancestry_hash=parent_hash,
            ancestry_path=[*parent_path, edge_hash] if parent_path else [edge_hash],
        )

    for node in overlay_nodes.values():
        if node.get("ancestry_hash"):
            continue
        node_hash = stable_hash("overlay_node", node.get("_key"), node.get("representative"), size=32)
        with_ancestry(
            node,
            ancestry_hash=node_hash,
            parent_ancestry_hash=None,
            ancestry_path=[node_hash],
        )

    for edge in overlay_edges:
        if edge.get("ancestry_hash"):
            continue
        witness_chunks = edge.get("witness_chunk_keys") or []
        first_witness = witness_chunks[0] if witness_chunks else None
        parent_ref = f"automath_chunks/{first_witness}" if first_witness else str(edge.get("_from", ""))
        parent_path = ancestry_path_by_ref.get(parent_ref, [])
        parent_hash = ancestry_hash_by_ref.get(parent_ref)
        edge_hash = stable_hash("overlay_edge", edge.get("_from"), edge.get("role"), edge.get("_to"), witness_chunks, size=32)
        with_ancestry(
            edge,
            ancestry_hash=edge_hash,
            parent_ancestry_hash=parent_hash,
            ancestry_path=[*parent_path, edge_hash] if parent_path else [edge_hash],
        )

    for edge in ancestry_edges:
        if edge.get("ancestry_hash"):
            continue
        parent_hash = edge.get("source_ancestry_hash")
        parent_path = list(edge.get("ancestry_path") or [])
        edge_hash = stable_hash("ancestry_edge", edge.get("_from"), edge.get("role"), edge.get("_to"), size=32)
        with_ancestry(
            edge,
            ancestry_hash=edge_hash,
            parent_ancestry_hash=str(parent_hash) if parent_hash else None,
            ancestry_path=[*parent_path, edge_hash] if parent_path else [edge_hash],
        )

    counts = {
        "fragments": write_jsonl(output_dir / "automath_fragments.jsonl", fragments, gzip_output=gzip_output),
        "chunks": write_jsonl(output_dir / "automath_chunks.jsonl", chunks, gzip_output=gzip_output),
        "entities": write_jsonl(output_dir / "automath_entities.jsonl", entities.values(), gzip_output=gzip_output),
        "triples": write_jsonl(output_dir / "automath_triples.jsonl", triples, gzip_output=gzip_output),
        "expr_nodes": write_jsonl(output_dir / "automath_expr_nodes.jsonl", expr_nodes, gzip_output=gzip_output),
        "expr_edges": write_jsonl(output_dir / "automath_expr_edges.jsonl", expr_edges, gzip_output=gzip_output),
        "theorem_shapes": write_jsonl(output_dir / "automath_theorem_shapes.jsonl", theorem_shapes, gzip_output=gzip_output),
        "ancestry_edges": write_jsonl(output_dir / "automath_ancestry_edges.jsonl", ancestry_edges, gzip_output=gzip_output),
        "overlay_nodes": write_jsonl(output_dir / "automath_overlay_nodes.jsonl", overlay_nodes.values(), gzip_output=gzip_output),
        "overlay_edges": write_jsonl(output_dir / "automath_overlay_edges.jsonl", overlay_edges, gzip_output=gzip_output),
    }
    alexandria_rows = build_alexandria_rows(
        fragments=fragments,
        chunks=chunks,
        entities=list(entities.values()),
        triples=triples,
        dataset=dataset,
        run_id=run_id,
    )
    alexandria_counts = {
        "documents": write_jsonl(output_dir / "alexandria_documents.jsonl", alexandria_rows["alexandria_documents"], gzip_output=gzip_output),
        "sections": write_jsonl(output_dir / "alexandria_sections.jsonl", alexandria_rows["alexandria_sections"], gzip_output=gzip_output),
        "chunks": write_jsonl(output_dir / "alexandria_chunks.jsonl", alexandria_rows["alexandria_chunks"], gzip_output=gzip_output),
        "entities": write_jsonl(output_dir / "alexandria_entities.jsonl", alexandria_rows["alexandria_entities"], gzip_output=gzip_output),
        "document_section_edges": write_jsonl(output_dir / "alexandria_document_section_edges.jsonl", alexandria_rows["alexandria_document_section_edges"], gzip_output=gzip_output),
        "section_chunk_edges": write_jsonl(output_dir / "alexandria_section_chunk_edges.jsonl", alexandria_rows["alexandria_section_chunk_edges"], gzip_output=gzip_output),
        "chunk_entity_edges": write_jsonl(output_dir / "alexandria_chunk_entity_edges.jsonl", alexandria_rows["alexandria_chunk_entity_edges"], gzip_output=gzip_output),
        "chunk_adjacent_edges": write_jsonl(output_dir / "alexandria_chunk_adjacent_edges.jsonl", alexandria_rows["alexandria_chunk_adjacent_edges"], gzip_output=gzip_output),
        "entity_relation_edges": write_jsonl(output_dir / "alexandria_entity_relation_edges.jsonl", alexandria_rows["alexandria_entity_relation_edges"], gzip_output=gzip_output),
        "debruijn_edges": write_jsonl(output_dir / "automath_debruijn_edges.jsonl", alexandria_rows["automath_debruijn_edges"], gzip_output=gzip_output),
    }
    summary = {
        "schema": f"{SCHEMA_PREFIX}.ingest_summary.v1",
        "dataset": dataset,
        "run_id": run_id,
        "input_paths": [p.as_posix() for p in input_paths],
        "output_dir": output_dir.as_posix(),
        "counts": counts,
        "alexandria_counts": alexandria_counts,
        "authority": {
            "graph_context_only": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
        "output": {"gzip": gzip_output},
    }
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / "summary.json").write_text(json.dumps(summary, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (output_dir / "automathtext_ingest_summary.json").write_text(
        json.dumps(summary, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return summary


def merge_counts(summaries: list[dict[str, Any]]) -> dict[str, int]:
    keys = [
        "fragments",
        "chunks",
        "entities",
        "triples",
        "expr_nodes",
        "expr_edges",
        "theorem_shapes",
        "ancestry_edges",
        "overlay_nodes",
        "overlay_edges",
    ]
    return {key: sum(int(summary.get("counts", {}).get(key, 0)) for summary in summaries) for key in keys}


def write_shard_input(path: Path, rows: list[tuple[Path, dict[str, Any]]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for source_path, row in rows:
            out = dict(row)
            out["__automath_source_file"] = source_path.as_posix()
            handle.write(json.dumps(out, ensure_ascii=True, sort_keys=True) + "\n")


def build_sharded_outputs(
    *,
    input_paths: list[Path],
    output_dir: Path,
    dataset: str,
    run_id: str,
    max_rows: int | None,
    max_chars: int,
    overlap_chars: int,
    entity_term: list[str],
    shard_rows: int,
    filter_operator_corridor: bool = False,
    require_theorem_marker: bool = False,
    gzip_output: bool = False,
) -> dict[str, Any]:
    if shard_rows <= 0:
        raise ValueError("shard_rows must be positive")
    output_dir.mkdir(parents=True, exist_ok=True)
    shard_root = output_dir / "shards"
    input_root = output_dir / "_shard_inputs"
    shard_summaries: list[dict[str, Any]] = []
    buffer: list[tuple[Path, dict[str, Any]]] = []
    source_rows = 0
    kept_rows = 0
    rejected_rows = 0
    term_hits: dict[str, int] = {}

    def flush(shard_index: int) -> None:
        nonlocal buffer
        if not buffer:
            return
        shard_name = f"shard_{shard_index:06d}"
        shard_input = input_root / f"{shard_name}.jsonl"
        write_shard_input(shard_input, buffer)
        shard_summary = build_outputs(
            input_paths=[shard_input],
            output_dir=shard_root / shard_name,
            dataset=dataset,
            run_id=f"{run_id}_{shard_name}",
            max_rows=None,
            max_chars=max_chars,
            overlap_chars=overlap_chars,
            entity_term=entity_term,
            gzip_output=gzip_output,
        )
        shard_summary["shard"] = shard_name
        shard_summary["source_rows"] = len(buffer)
        (shard_root / shard_name / "summary.json").write_text(
            json.dumps(shard_summary, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        shard_summaries.append(shard_summary)
        buffer = []

    shard_index = 0
    for source_path, row in iter_rows(input_paths, limit=max_rows):
        source_rows += 1
        hits = operator_corridor_hits(row_text(row)) if filter_operator_corridor else []
        if filter_operator_corridor and not hits:
            rejected_rows += 1
            continue
        if require_theorem_marker and not has_theorem_marker(row_text(row)):
            rejected_rows += 1
            continue
        for term in hits:
            term_hits[term] = term_hits.get(term, 0) + 1
        buffer.append((source_path, row))
        kept_rows += 1
        if len(buffer) >= shard_rows:
            flush(shard_index)
            shard_index += 1
    flush(shard_index)

    counts = merge_counts(shard_summaries)
    counts["source_rows"] = source_rows
    counts["kept_rows"] = kept_rows
    counts["rejected_rows"] = rejected_rows
    counts["shards"] = len(shard_summaries)
    summary = {
        "schema": f"{SCHEMA_PREFIX}.sharded_ingest_summary.v1",
        "dataset": dataset,
        "run_id": run_id,
        "input_paths": [p.as_posix() for p in input_paths],
        "output_dir": output_dir.as_posix(),
        "shards_dir": shard_root.as_posix(),
        "shard_rows": shard_rows,
        "counts": counts,
        "filter": {
            "operator_corridor": filter_operator_corridor,
            "require_theorem_marker": require_theorem_marker,
            "terms": list(OPERATOR_CORRIDOR_TERMS) if filter_operator_corridor else [],
            "term_hits": dict(sorted(term_hits.items())),
        },
        "output": {"gzip": gzip_output},
        "shards": [
            {
                "shard": summary["shard"],
                "output_dir": summary["output_dir"],
                "source_rows": summary["source_rows"],
                "counts": summary["counts"],
            }
            for summary in shard_summaries
        ],
        "authority": {
            "graph_context_only": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
    }
    (output_dir / "summary.json").write_text(json.dumps(summary, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return summary


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", action="append", type=Path, default=[], help="Input .jsonl/.json/.parquet file. Can repeat.")
    parser.add_argument("--input-dir", type=Path, help="Directory scanned recursively for .parquet/.jsonl files.")
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--dataset", default="OpenSQZ/AutoMathText-V2")
    parser.add_argument("--run-id", default=None)
    parser.add_argument("--max-rows", type=int)
    parser.add_argument("--max-chars", type=int, default=2400)
    parser.add_argument("--overlap-chars", type=int, default=240)
    parser.add_argument("--entity-term", action="append", default=[])
    parser.add_argument("--shard-rows", type=int, help="Write bounded shards with at most this many source rows each.")
    parser.add_argument("--filter-operator-corridor", action="store_true", help="Keep only rows mentioning operator-corridor terms before graph expansion.")
    parser.add_argument("--require-theorem-marker", action="store_true", help="When filtering, also require theorem/lemma/proof-style markers.")
    parser.add_argument("--gzip", dest="gzip_output", action="store_true", help="Write JSONL graph outputs as .jsonl.gz.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    paths = list(args.input)
    if args.input_dir:
        paths.extend(sorted([*args.input_dir.rglob("*.jsonl"), *args.input_dir.rglob("*.parquet")]))
    if not paths:
        raise SystemExit("No input files supplied. Use --input or --input-dir.")
    run_id = args.run_id or "automathtext_v2_" + stable_hash([p.as_posix() for p in paths], args.max_rows, size=8)
    if args.shard_rows:
        summary = build_sharded_outputs(
            input_paths=paths,
            output_dir=args.out_dir,
            dataset=args.dataset,
            run_id=run_id,
            max_rows=args.max_rows,
            max_chars=args.max_chars,
            overlap_chars=args.overlap_chars,
            entity_term=args.entity_term,
            shard_rows=args.shard_rows,
            filter_operator_corridor=args.filter_operator_corridor,
            require_theorem_marker=args.require_theorem_marker,
            gzip_output=args.gzip_output,
        )
    else:
        summary = build_outputs(
            input_paths=paths,
            output_dir=args.out_dir,
            dataset=args.dataset,
            run_id=run_id,
            max_rows=args.max_rows,
            max_chars=args.max_chars,
            overlap_chars=args.overlap_chars,
            entity_term=args.entity_term,
            gzip_output=args.gzip_output,
        )
    print(json.dumps(summary, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
