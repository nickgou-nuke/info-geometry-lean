"""Shared planner types, constants, and helpers."""

from __future__ import annotations

import json
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, cast
from urllib.parse import unquote, urlparse


JsonObj = dict[str, Any]


DECL_NAME_EXACT_KEYS = ("declName",)

DECL_NAME_REQUEST_KEYS = (
    "requestedDecl",
    "name",
    "declarationName",
    "declaration",
    "theoremName",
)

DECL_NAME_KEYS = DECL_NAME_EXACT_KEYS + DECL_NAME_REQUEST_KEYS

DECL_NAME_CONTAINERS = (
    "request",
    "requestMeta",
    "params",
    "input",
    "meta",
    "payload",
)

DECL_LOCATION_FILE_KEYS = (
    "file",
    "sourceFile",
    "path",
    "uri",
    "documentUri",
    "sourceUri",
)

DECL_LOCATION_MODULE_KEYS = (
    "module",
    "declModule",
    "moduleName",
)

DECL_LOCATION_LINE_KEYS = (
    "line",
    "posLine",
    "startLine",
    "targetLine",
)

DECL_MATCH_RELIABILITY = {
    "exactDecl": 1.00,
    "requestField": 0.90,
    "locationFallback": 0.70,
    "fingerprintFallback": 0.52,
    "unmatched": 0.0,
}

DECL_LOCATION_RANGE_MAX_DELTA = 120


HEAD_SOURCE_WEIGHT = {
    "exprSemantic": 1.00,
    "textHeuristic": 0.55,
    "unavailable": 0.20,
}

DIAG_PROVENANCE_WEIGHT = {
    "leanTag": 1.00,
    "messagePattern": 0.75,
    "bridgeRule": 0.60,
    "fallback": 0.40,
}

VIOLATION_LEVEL_WEIGHT = {
    "error": 1.00,
    "warning": 0.70,
    "info": 0.45,
}

VACUITY_TAGS = {
    "wrapper-candidate",
    "dead-candidate",
    "rfl-like",
    "proof-infrastructure",
}

THEOREM_LIKE_KINDS = {"theorem", "lemma"}

DECL_MATCH_CONTEXT_KINDS = {"theorem", "lemma", "def", "abbrev"}

REPLACEMENT_CLUSTER_PARTICIPATION_LIMIT = 3


@dataclass
class Signal:
    name: str
    contribution: float
    reliability: float
    evidence: str


@dataclass
class RankedEntry:
    key: str
    score: float
    confidence: float
    payload: dict[str, Any]


def clamp01(x: float) -> float:
    if x < 0.0:
        return 0.0
    if x > 1.0:
        return 1.0
    return x


def safe_mean(values: list[float], default: float = 0.0) -> float:
    if not values:
        return default
    return sum(values) / len(values)


def relpath_or_self(path: Path, root: Path) -> str:
    try:
        return str(path.resolve().relative_to(root.resolve()))
    except Exception:
        return str(path)


def parse_uri_or_path(value: str | None, root: Path) -> str | None:
    if not value:
        return None
    if value.startswith("file://"):
        parsed = urlparse(value)
        fs_path = Path(unquote(parsed.path))
        return relpath_or_self(fs_path, root)
    path = Path(value)
    if path.is_absolute():
        return relpath_or_self(path, root)
    return str(path)


def coerce_int(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float) and value.is_integer():
        return int(value)
    if isinstance(value, str):
        s = value.strip()
        if s.lstrip("-").isdigit():
            try:
                return int(s)
            except ValueError:
                return None
    return None


def arity_shape(value: int | None) -> str:
    if value is None:
        return "arity:?"
    if value <= 0:
        return "arity:0"
    if value == 1:
        return "arity:1"
    return "arity:2+"


def binder_shape(value: int | None) -> str:
    if value is None:
        return "binder:?"
    if value <= 0:
        return "binder:0"
    if value == 1:
        return "binder:1"
    return "binder:2+"


def is_valid_decl_name(value: Any) -> bool:
    if not isinstance(value, str):
        return False
    s = value.strip()
    if not s:
        return False
    if s.startswith("file://"):
        return False
    if "/" in s or s.endswith(".lean"):
        return False
    if s.lower() in {"null", "none", "true", "false"}:
        return False
    return True


def normalize_expr_record(
    record: Any,
    *,
    fallback_head: Any,
    fallback_source: Any,
    fallback_fingerprint: Any,
) -> JsonObj:
    semantic_head = fallback_head if isinstance(fallback_head, str) and fallback_head else None
    head_source = fallback_source if isinstance(fallback_source, str) and fallback_source else "unavailable"
    fingerprint_v1 = (
        fallback_fingerprint if isinstance(fallback_fingerprint, str) and fallback_fingerprint else None
    )
    expr_kind: str | None = None
    app_arity: int | None = None
    binder_depth: int | None = None
    arg_heads: list[str] = []

    if isinstance(record, dict):
        rec = cast(JsonObj, record)
        sem_any = rec.get("semanticHead")
        src_any = rec.get("fingerprintSource")
        fp_any = rec.get("fingerprintV1")
        kind_any = rec.get("exprKind")
        if isinstance(sem_any, str) and sem_any:
            semantic_head = sem_any
        if isinstance(src_any, str) and src_any:
            head_source = src_any
        if isinstance(fp_any, str) and fp_any:
            fingerprint_v1 = fp_any
        if isinstance(kind_any, str) and kind_any:
            expr_kind = kind_any
        app_arity = coerce_int(rec.get("appArity"))
        binder_depth = coerce_int(rec.get("binderDepth"))
        arg_head_any = rec.get("argHeadFingerprints")
        if isinstance(arg_head_any, list):
            for item in arg_head_any:
                if isinstance(item, str) and item:
                    arg_heads.append(item)

    if expr_kind is None:
        if head_source == "exprSemantic":
            expr_kind = "unknown"
        else:
            expr_kind = None

    return {
        "semanticHead": semantic_head,
        "headSource": head_source,
        "fingerprintV1": fingerprint_v1,
        "exprKind": expr_kind,
        "appArity": app_arity,
        "binderDepth": binder_depth,
        "arityShape": arity_shape(app_arity),
        "binderShape": binder_shape(binder_depth),
        "argHeadFingerprints": arg_heads,
    }


def make_cluster_key(
    *,
    fingerprint_v1: str | None,
    semantic_head: str | None,
    expr_kind: str | None,
    arity_shape_value: str | None,
    binder_shape_value: str | None,
) -> str:
    fp = fingerprint_v1 or "none"
    head = semantic_head or "none"
    kind = expr_kind or "none"
    ar = arity_shape_value or "arity:?"
    bd = binder_shape_value or "binder:?"
    return f"fp:{fp}|head:{head}|kind:{kind}|{ar}|{bd}"


def dedup_preserve_order(items: Iterable[str]) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


def top_counts(counter: Counter[str], limit: int = 8) -> list[list[str | int]]:
    return [[k, int(v)] for k, v in counter.most_common(limit)]


def keys_from_counts(value: Any, *, limit: int = 8) -> set[str]:
    out: set[str] = set()
    if isinstance(value, list):
        for row in value[:limit]:
            if isinstance(row, (list, tuple)) and row:
                key = row[0]
                if isinstance(key, str) and key:
                    out.add(key)
    return out


def first_count_key(value: Any) -> str | None:
    if isinstance(value, list):
        for row in value:
            if isinstance(row, (list, tuple)) and row:
                key = row[0]
                if isinstance(key, str) and key:
                    return key
    return None


def top_count_keys(value: Any, *, limit: int = 3) -> list[str]:
    out: list[str] = []
    if isinstance(value, list):
        for row in value:
            if len(out) >= limit:
                break
            if isinstance(row, (list, tuple)) and row:
                key = row[0]
                if isinstance(key, str) and key and key not in out:
                    out.append(key)
    return out


def jaccard_overlap(lhs: Iterable[str], rhs: Iterable[str]) -> float:
    left = set(lhs)
    right = set(rhs)
    if not left or not right:
        return 0.0
    inter = left & right
    union = left | right
    if not union:
        return 0.0
    return len(inter) / len(union)


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def load_jsonl(path: Path) -> list[JsonObj]:
    rows: list[JsonObj] = []
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            s = line.strip()
            if not s:
                continue
            rows.append(cast(JsonObj, json.loads(s)))
    return rows


def resolve_existing(*paths: Path) -> Path | None:
    for p in paths:
        if p.exists():
            return p
    return None


def load_decl_index(path: Path) -> dict[str, JsonObj]:
    out: dict[str, JsonObj] = {}
    for row in load_jsonl(path):
        out[row["name"]] = row
    return out


def load_edges(path: Path) -> tuple[dict[str, list[tuple[str, str]]], dict[str, list[tuple[str, str]]]]:
    from collections import defaultdict

    forward: dict[str, list[tuple[str, str]]] = defaultdict(list)
    reverse: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for row in load_jsonl(path):
        src = row.get("src")
        dst = row.get("dst")
        kind = row.get("kind", "value")
        if not src or not dst:
            continue
        forward[src].append((dst, kind))
        reverse[dst].append((src, kind))
    return dict(forward), dict(reverse)


def load_module_regions(path: Path, root: Path) -> tuple[dict[str, str], dict[str, str]]:
    raw = load_json(path)
    module_to_region: dict[str, str] = {}
    file_to_region: dict[str, str] = {}
    for node in raw.get("nodes", []):
        module = node.get("id")
        region = node.get("region", "unknown")
        path_str = node.get("path")
        if module:
            module_to_region[module] = region
        if path_str:
            rel = parse_uri_or_path(path_str, root)
            if rel:
                file_to_region[rel] = region
    return module_to_region, file_to_region


def load_owner_index(path: Path) -> list[JsonObj]:
    raw = load_json(path)
    entries: list[JsonObj] = []
    for row in raw.get("files", []):
        if row.get("kind") == "owner":
            entries.append(row)
    return entries


def load_proof_hole_counts(path: Path) -> dict[str, int]:
    out: dict[str, int] = {}
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            s = line.strip()
            if not s:
                continue
            parts = s.split("\t")
            if len(parts) < 2:
                continue
            try:
                count = int(parts[0].strip())
            except ValueError:
                continue
            out[parts[1].strip()] = count
    return out


def source_weight(source: str | None) -> float:
    return HEAD_SOURCE_WEIGHT.get(source or "unavailable", HEAD_SOURCE_WEIGHT["unavailable"])


def diag_weight(diag_provs: list[str]) -> float:
    if not diag_provs:
        return DIAG_PROVENANCE_WEIGHT["fallback"]
    vals = [DIAG_PROVENANCE_WEIGHT.get(p, DIAG_PROVENANCE_WEIGHT["fallback"]) for p in diag_provs]
    return safe_mean(vals, default=DIAG_PROVENANCE_WEIGHT["fallback"])


def summarize_signals(signals: list[Signal]) -> tuple[float, float, list[JsonObj]]:
    if not signals:
        return 0.0, 0.0, []
    score = clamp01(sum(max(0.0, s.contribution) for s in signals))
    denom = sum(abs(s.contribution) for s in signals)
    confidence = 0.0
    if denom > 0:
        confidence = clamp01(sum(abs(s.contribution) * s.reliability for s in signals) / denom)
    provenance: list[JsonObj] = [
        {
            "signal": s.name,
            "contribution": round(s.contribution, 4),
            "reliability": round(s.reliability, 4),
            "evidence": s.evidence,
        }
        for s in signals
    ]
    return score, confidence, provenance


def file_domain(file_path: str | None) -> str | None:
    if not file_path:
        return None
    parts = Path(file_path).parts
    if len(parts) >= 3 and parts[0] == "lean" and parts[1] == "InfoGeometry":
        return parts[2]
    return None
