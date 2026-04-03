#!/usr/bin/env python3
"""Planning-only vacuity planner skeleton.

This tool aggregates read-only compiler bridge payloads, vacuity reports,
dependency metadata, and ownership metadata to produce ranked planning outputs:

- ranked vacuity candidates
- ranked owner candidates
- ranked replacement candidates

Boundary:
- no mutation surface
- no automatic replacement
- no proof repair
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, cast
from urllib.parse import unquote, urlparse

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from pathing import normalize_user_path, repo_root
else:
    from tools.pathing import normalize_user_path, repo_root


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


def _find_first_key_value(node: Any, key: str) -> Any:
    if isinstance(node, dict):
        node_dict = cast(JsonObj, node)
        if key in node_dict:
            return node_dict.get(key)
        for child in node_dict.values():
            found = _find_first_key_value(child, key)
            if found is not None:
                return found
    elif isinstance(node, list):
        for child in cast(list[Any], node):
            found = _find_first_key_value(child, key)
            if found is not None:
                return found
    return None


def extract_decl_field(payload: JsonObj) -> tuple[str | None, str]:
    for key in DECL_NAME_KEYS:
        value = _find_first_key_value(payload, key)
        if is_valid_decl_name(value):
            decl = str(value).strip()
            if key in DECL_NAME_EXACT_KEYS:
                return decl, "exactDecl"
            return decl, "requestField"
    return None, "unmatched"


def extract_decl_name(payload: JsonObj) -> str | None:
    decl, _ = extract_decl_field(payload)
    return decl


def extract_location_hints(
    payload: JsonObj,
    *,
    source_file: str | None,
    root: Path,
) -> tuple[str | None, str | None, int | None]:
    file_hint: str | None = None
    for key in DECL_LOCATION_FILE_KEYS:
        raw = _find_first_key_value(payload, key)
        if isinstance(raw, str) and raw:
            parsed = parse_uri_or_path(raw, root)
            if parsed:
                file_hint = parsed
                break
    if not file_hint:
        file_hint = source_file

    module_hint: str | None = None
    for key in DECL_LOCATION_MODULE_KEYS:
        raw = _find_first_key_value(payload, key)
        if isinstance(raw, str) and raw:
            module_hint = raw.strip()
            break

    line_hint: int | None = None
    for key in DECL_LOCATION_LINE_KEYS:
        raw = _find_first_key_value(payload, key)
        parsed = coerce_int(raw)
        if parsed is not None:
            line_hint = parsed
            break
    if line_hint is None:
        position_any = _find_first_key_value(payload, "position")
        if isinstance(position_any, dict):
            line_hint = coerce_int(cast(JsonObj, position_any).get("line"))

    return file_hint, module_hint, line_hint


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


def _dedup_preserve_order(items: Iterable[str]) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


def build_decl_match_context(
    theorem_entries: list[JsonObj],
    decls: dict[str, JsonObj],
    root: Path,
) -> dict[str, Any]:
    theorem_names: set[str] = set()
    theorem_meta: dict[str, JsonObj] = {}
    by_file_module_line: dict[tuple[str, str, int], list[str]] = defaultdict(list)
    by_file_line: dict[tuple[str, int], list[str]] = defaultdict(list)
    by_file_module: dict[tuple[str, str], list[str]] = defaultdict(list)
    by_file_module_ordered: dict[tuple[str, str], list[tuple[int, str]]] = defaultdict(list)
    by_file_ordered: dict[str, list[tuple[int, str]]] = defaultdict(list)

    for row in theorem_entries:
        if row.get("kind") != "theorem":
            continue
        name_any = row.get("name")
        if not isinstance(name_any, str) or not name_any:
            continue
        name = name_any
        theorem_names.add(name)

        file_any = row.get("file")
        file_rel = parse_uri_or_path(file_any, root) if isinstance(file_any, str) else None
        module_any = row.get("module")
        module = module_any.strip() if isinstance(module_any, str) and module_any.strip() else None

        line_any = row.get("line")
        line = coerce_int(line_any)
        if line is None:
            decl_row = decls.get(name)
            if isinstance(decl_row, dict):
                line = coerce_int(decl_row.get("line"))
                if not file_rel:
                    decl_file_any = decl_row.get("file")
                    if isinstance(decl_file_any, str):
                        file_rel = parse_uri_or_path(decl_file_any, root)
                if not module:
                    decl_module_any = decl_row.get("module")
                    if isinstance(decl_module_any, str) and decl_module_any.strip():
                        module = decl_module_any.strip()

        theorem_meta[name] = {"file": file_rel, "module": module, "line": line}

        if isinstance(file_rel, str) and isinstance(module, str):
            by_file_module[(file_rel, module)].append(name)
            if isinstance(line, int) and line >= 0:
                by_file_module_line[(file_rel, module, line)].append(name)
                by_file_module_ordered[(file_rel, module)].append((line, name))
        if isinstance(file_rel, str) and isinstance(line, int) and line >= 0:
            by_file_line[(file_rel, line)].append(name)
            by_file_ordered[file_rel].append((line, name))

    for ordered in by_file_module_ordered.values():
        ordered.sort(key=lambda item: (item[0], item[1]))
    for ordered in by_file_ordered.values():
        ordered.sort(key=lambda item: (item[0], item[1]))

    cluster_to_decl: dict[str, Counter[str]] = defaultdict(Counter)
    return {
        "theoremNames": theorem_names,
        "theoremMeta": theorem_meta,
        "byFileModuleLine": by_file_module_line,
        "byFileLine": by_file_line,
        "byFileModule": by_file_module,
        "byFileModuleOrdered": by_file_module_ordered,
        "byFileOrdered": by_file_ordered,
        "clusterToDecl": cluster_to_decl,
    }


def _unique_decl(candidates: Iterable[str]) -> str | None:
    uniq = _dedup_preserve_order(candidates)
    if len(uniq) == 1:
        return uniq[0]
    return None


def _line_candidates(line_hint: int | None) -> list[int]:
    if line_hint is None:
        return []
    out: list[int] = []
    if line_hint >= 0:
        out.append(line_hint)
        out.append(line_hint + 1)
    if line_hint > 0:
        out.append(line_hint - 1)
    seen: set[int] = set()
    deduped: list[int] = []
    for value in out:
        if value in seen:
            continue
        seen.add(value)
        deduped.append(value)
    return deduped


def _resolve_nearest_decl_from_ordered(
    ordered: list[tuple[int, str]],
    line_hint: int,
    *,
    max_delta: int,
) -> str | None:
    if not ordered:
        return None

    by_line: dict[int, set[str]] = defaultdict(set)
    lines: list[int] = []
    seen_lines: set[int] = set()
    for line, decl in ordered:
        by_line[line].add(decl)
        if line not in seen_lines:
            seen_lines.add(line)
            lines.append(line)

    lines.sort()
    if not lines:
        return None

    best_decl: str | None = None
    best_dist: int | None = None

    for probe_line in _line_candidates(line_hint):
        nearest_line = lines[0]
        for value in lines:
            if value <= probe_line:
                nearest_line = value
            else:
                break

        names = sorted(by_line.get(nearest_line, set()))
        if len(names) != 1:
            continue

        dist = abs(nearest_line - probe_line)
        if best_dist is None or dist < best_dist:
            best_dist = dist
            best_decl = names[0]

    if best_decl is None or best_dist is None:
        return None
    if best_dist > max_delta:
        return None
    return best_decl


def _resolve_decl_by_location(
    *,
    file_hint: str | None,
    module_hint: str | None,
    line_hint: int | None,
    match_ctx: dict[str, Any],
) -> str | None:
    if not isinstance(file_hint, str) or not file_hint:
        return None

    by_file_module_line = cast(dict[tuple[str, str, int], list[str]], match_ctx.get("byFileModuleLine", {}))
    by_file_line = cast(dict[tuple[str, int], list[str]], match_ctx.get("byFileLine", {}))
    by_file_module = cast(dict[tuple[str, str], list[str]], match_ctx.get("byFileModule", {}))
    by_file_module_ordered = cast(
        dict[tuple[str, str], list[tuple[int, str]]],
        match_ctx.get("byFileModuleOrdered", {}),
    )
    by_file_ordered = cast(dict[str, list[tuple[int, str]]], match_ctx.get("byFileOrdered", {}))

    if isinstance(module_hint, str) and module_hint and line_hint is not None:
        for line in _line_candidates(line_hint):
            exact = _unique_decl(by_file_module_line.get((file_hint, module_hint, line), []))
            if exact:
                return exact

    if line_hint is not None:
        for line in _line_candidates(line_hint):
            by_line = _unique_decl(by_file_line.get((file_hint, line), []))
            if by_line:
                return by_line

    if line_hint is not None and isinstance(module_hint, str) and module_hint:
        nearest_mod = _resolve_nearest_decl_from_ordered(
            by_file_module_ordered.get((file_hint, module_hint), []),
            line_hint,
            max_delta=DECL_LOCATION_RANGE_MAX_DELTA,
        )
        if nearest_mod:
            return nearest_mod

    if line_hint is not None:
        nearest_file = _resolve_nearest_decl_from_ordered(
            by_file_ordered.get(file_hint, []),
            line_hint,
            max_delta=DECL_LOCATION_RANGE_MAX_DELTA,
        )
        if nearest_file:
            return nearest_file

    if isinstance(module_hint, str) and module_hint:
        by_mod = _unique_decl(by_file_module.get((file_hint, module_hint), []))
        if by_mod:
            return by_mod

    return None


def _payload_cluster_keys(payload: JsonObj) -> list[str]:
    out: list[str] = []

    def add_cluster(*, head: Any, head_source: Any, head_fingerprint: Any, expr_record: Any) -> None:
        norm = normalize_expr_record(
            expr_record,
            fallback_head=head,
            fallback_source=head_source,
            fallback_fingerprint=head_fingerprint,
        )
        cluster = make_cluster_key(
            fingerprint_v1=cast(str | None, norm.get("fingerprintV1")),
            semantic_head=cast(str | None, norm.get("semanticHead")),
            expr_kind=cast(str | None, norm.get("exprKind")),
            arity_shape_value=cast(str | None, norm.get("arityShape")),
            binder_shape_value=cast(str | None, norm.get("binderShape")),
        )
        out.append(cluster)

    add_cluster(
        head=payload.get("theoremTypeHead"),
        head_source=payload.get("theoremTypeHeadSource", "unavailable"),
        head_fingerprint=payload.get("theoremTypeHeadFingerprint"),
        expr_record=payload.get("theoremTypeExprFingerprint"),
    )

    goals_any = payload.get("goals")
    if isinstance(goals_any, list):
        for goal_any in goals_any:
            if not isinstance(goal_any, dict):
                continue
            goal = cast(JsonObj, goal_any)
            add_cluster(
                head=goal.get("targetHead"),
                head_source=goal.get("targetHeadSource", "unavailable"),
                head_fingerprint=goal.get("targetHeadFingerprint"),
                expr_record=goal.get("targetExprFingerprint"),
            )
            locals_any = goal.get("locals")
            if not isinstance(locals_any, list):
                continue
            for local_any in locals_any:
                if not isinstance(local_any, dict):
                    continue
                local = cast(JsonObj, local_any)
                add_cluster(
                    head=local.get("typeHead"),
                    head_source=local.get("typeHeadSource", "unavailable"),
                    head_fingerprint=local.get("typeHeadFingerprint"),
                    expr_record=local.get("typeExprFingerprint"),
                )

    return _dedup_preserve_order(out)


def _resolve_decl_by_fingerprint(
    payload: JsonObj,
    *,
    file_hint: str | None,
    module_hint: str | None,
    match_ctx: dict[str, Any],
) -> str | None:
    cluster_to_decl = cast(dict[str, Counter[str]], match_ctx.get("clusterToDecl", {}))
    theorem_meta = cast(dict[str, JsonObj], match_ctx.get("theoremMeta", {}))
    if not cluster_to_decl:
        return None

    aggregate: Counter[str] = Counter()
    for cluster in _payload_cluster_keys(payload):
        counts = cluster_to_decl.get(cluster)
        if not counts:
            continue
        for decl_name, count in counts.items():
            meta = theorem_meta.get(decl_name, {})
            if isinstance(file_hint, str) and file_hint:
                meta_file = meta.get("file")
                if isinstance(meta_file, str) and meta_file and meta_file != file_hint:
                    continue
            if isinstance(module_hint, str) and module_hint:
                meta_module = meta.get("module")
                if isinstance(meta_module, str) and meta_module and meta_module != module_hint:
                    continue
            aggregate[decl_name] += int(count)

    if not aggregate:
        return None
    return aggregate.most_common(1)[0][0]


def resolve_decl_match(
    payload: JsonObj,
    *,
    source_file: str | None,
    root: Path,
    match_ctx: dict[str, Any],
) -> tuple[str | None, str, float]:
    theorem_names = cast(set[str], match_ctx.get("theoremNames", set()))

    explicit_decl, explicit_prov = extract_decl_field(payload)
    if isinstance(explicit_decl, str) and explicit_decl:
        if not theorem_names or explicit_decl in theorem_names:
            rel = DECL_MATCH_RELIABILITY.get(explicit_prov, DECL_MATCH_RELIABILITY["requestField"])
            return explicit_decl, explicit_prov, rel

    file_hint, module_hint, line_hint = extract_location_hints(payload, source_file=source_file, root=root)
    by_location = _resolve_decl_by_location(
        file_hint=file_hint,
        module_hint=module_hint,
        line_hint=line_hint,
        match_ctx=match_ctx,
    )
    if isinstance(by_location, str) and by_location:
        return by_location, "locationFallback", DECL_MATCH_RELIABILITY["locationFallback"]

    by_fingerprint = _resolve_decl_by_fingerprint(
        payload,
        file_hint=file_hint,
        module_hint=module_hint,
        match_ctx=match_ctx,
    )
    if isinstance(by_fingerprint, str) and by_fingerprint:
        return by_fingerprint, "fingerprintFallback", DECL_MATCH_RELIABILITY["fingerprintFallback"]

    return None, "unmatched", DECL_MATCH_RELIABILITY["unmatched"]


def seed_decl_match_context(match_ctx: dict[str, Any], observations: list[JsonObj]) -> None:
    cluster_to_decl = cast(dict[str, Counter[str]], match_ctx.get("clusterToDecl", {}))
    if not cluster_to_decl:
        return
    for obs in observations:
        decl_any = obs.get("declName")
        if not isinstance(decl_any, str) or not decl_any:
            continue
        prov_any = obs.get("declMatchProvenance")
        prov = prov_any if isinstance(prov_any, str) else "unmatched"
        if prov == "unmatched":
            continue
        cluster_key = make_cluster_key(
            fingerprint_v1=obs.get("fingerprintV1") if isinstance(obs.get("fingerprintV1"), str) else None,
            semantic_head=obs.get("semanticHead") if isinstance(obs.get("semanticHead"), str) else None,
            expr_kind=obs.get("exprKind") if isinstance(obs.get("exprKind"), str) else None,
            arity_shape_value=obs.get("arityShape") if isinstance(obs.get("arityShape"), str) else None,
            binder_shape_value=obs.get("binderShape") if isinstance(obs.get("binderShape"), str) else None,
        )
        cluster_to_decl[cluster_key][decl_any] += 1


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


def collect_bridge_json_paths(raw_inputs: list[str], root: Path) -> list[Path]:
    candidates: list[Path] = []
    seen: set[Path] = set()

    def add_file(p: Path) -> None:
        q = p.resolve()
        if q in seen:
            return
        seen.add(q)
        candidates.append(q)

    def collect_from_path(p: Path) -> None:
        if p.is_file() and p.suffix == ".json":
            add_file(p)
            return
        if p.is_dir():
            for child in sorted(p.rglob("*.json")):
                add_file(child)

    if raw_inputs:
        for item in raw_inputs:
            if any(ch in item for ch in "*?[]"):
                for match in sorted(root.glob(item)):
                    collect_from_path(match)
                continue
            resolved = normalize_user_path(item, root / item)
            collect_from_path(resolved)
        return candidates

    auto_dirs = [
        root / ".artifacts" / "ci" / "compiler_bridge_smoke",
        root / "reports" / "vacuity",
    ]
    auto_files = [
        root / "reports" / "bridge_payload_demo.json",
        root / "reports" / "vacuity" / "bridge_payload_demo.json",
    ]
    for d in auto_dirs:
        collect_from_path(d)
    for f in auto_files:
        collect_from_path(f)
    return candidates


def extract_bridge_payload_objects(data: Any) -> list[JsonObj]:
    found: list[JsonObj] = []

    def visit(node: Any) -> None:
        if isinstance(node, dict):
            node_dict = cast(JsonObj, node)
            if isinstance(node_dict.get("goals"), list) and isinstance(node_dict.get("diagnostics", []), list):
                found.append(node_dict)
            for key in ("result", "payload", "data", "entries", "responses"):
                if key in node_dict:
                    visit(node_dict[key])
        elif isinstance(node, list):
            for item in cast(list[Any], node):
                visit(item)

    visit(data)
    return found


def observe_bridge_payload(
    payload: JsonObj,
    payload_path: Path,
    root: Path,
    match_ctx: dict[str, Any] | None = None,
) -> list[JsonObj]:
    response_meta = payload.get("responseMeta", {})
    session = response_meta.get("sessionId", {}).get("value")
    source_file = parse_uri_or_path(session, root)
    if match_ctx is not None:
        decl_name, decl_match_provenance, decl_match_reliability = resolve_decl_match(
            payload,
            source_file=source_file,
            root=root,
            match_ctx=match_ctx,
        )
    else:
        decl_name, prov = extract_decl_field(payload)
        decl_match_provenance = prov
        decl_match_reliability = DECL_MATCH_RELIABILITY.get(prov, DECL_MATCH_RELIABILITY["unmatched"])

    diag_provs: list[str] = []
    for diag_any in payload.get("diagnostics", []):
        if isinstance(diag_any, dict):
            diag = cast(JsonObj, diag_any)
            prov = diag.get("classificationProvenance")
            if isinstance(prov, str):
                diag_provs.append(prov)

    base_diag_weight = diag_weight(diag_provs)

    def make_observation(
        *,
        surface: str,
        head: Any,
        head_source: Any,
        head_fingerprint: Any,
        expr_record: Any,
    ) -> JsonObj:
        norm = normalize_expr_record(
            expr_record,
            fallback_head=head,
            fallback_source=head_source,
            fallback_fingerprint=head_fingerprint,
        )
        s_weight = source_weight(cast(str | None, norm.get("headSource")))
        obs_conf = clamp01(0.7 * s_weight + 0.3 * base_diag_weight)
        return {
            "payloadFile": relpath_or_self(payload_path, root),
            "sourceFile": source_file,
            "declName": decl_name,
            "declMatchProvenance": decl_match_provenance,
            "declMatchReliability": round(decl_match_reliability, 4),
            "surface": surface,
            "head": norm.get("semanticHead"),
            "headSource": norm.get("headSource"),
            "fingerprint": norm.get("fingerprintV1"),
            "semanticHead": norm.get("semanticHead"),
            "fingerprintV1": norm.get("fingerprintV1"),
            "exprKind": norm.get("exprKind"),
            "appArity": norm.get("appArity"),
            "binderDepth": norm.get("binderDepth"),
            "arityShape": norm.get("arityShape"),
            "binderShape": norm.get("binderShape"),
            "argHeadFingerprints": norm.get("argHeadFingerprints", []),
            "observationConfidence": round(obs_conf, 4),
            "diagnosticProvenance": list(diag_provs),
        }

    out: list[JsonObj] = []
    for goal_any in payload.get("goals", []):
        if not isinstance(goal_any, dict):
            continue
        goal = cast(JsonObj, goal_any)
        out.append(
            make_observation(
                surface="target",
                head=goal.get("targetHead"),
                head_source=goal.get("targetHeadSource", "unavailable"),
                head_fingerprint=goal.get("targetHeadFingerprint"),
                expr_record=goal.get("targetExprFingerprint"),
            )
        )
        for local_any in goal.get("locals", []):
            if not isinstance(local_any, dict):
                continue
            local = cast(JsonObj, local_any)
            out.append(
                make_observation(
                    surface="local",
                    head=local.get("typeHead"),
                    head_source=local.get("typeHeadSource", "unavailable"),
                    head_fingerprint=local.get("typeHeadFingerprint"),
                    expr_record=local.get("typeExprFingerprint"),
                )
            )

    has_validate_decl_shape = any(
        key in payload
        for key in (
            "theoremType",
            "theoremTypeHead",
            "theoremTypeHeadSource",
            "theoremTypeHeadFingerprint",
            "theoremTypeExprFingerprint",
        )
    )
    if has_validate_decl_shape:
        out.append(
            make_observation(
                surface="theoremType",
                head=payload.get("theoremTypeHead"),
                head_source=payload.get("theoremTypeHeadSource", "unavailable"),
                head_fingerprint=payload.get("theoremTypeHeadFingerprint"),
                expr_record=payload.get("theoremTypeExprFingerprint"),
            )
        )

    if match_ctx is not None:
        seed_decl_match_context(match_ctx, out)

    return out


def normalize_bridge_observations(
    observations: list[JsonObj],
) -> tuple[JsonObj, dict[str, JsonObj], dict[str, JsonObj]]:
    semantic_groups: dict[tuple[str, str], JsonObj] = {}
    fingerprint_groups: dict[tuple[str, str], JsonObj] = {}
    shape_groups: dict[tuple[str, str, str, str, str], JsonObj] = {}
    file_signals: dict[str, JsonObj] = defaultdict(
        lambda: {
            "semanticCount": 0,
            "fingerprintCount": 0,
            "confSamples": [],
            "fingerprintCounts": Counter(),
            "semanticHeadCounts": Counter(),
            "exprKindCounts": Counter(),
            "arityShapeCounts": Counter(),
            "binderShapeCounts": Counter(),
            "clusterKeyCounts": Counter(),
        }
    )
    decl_signals: dict[str, JsonObj] = defaultdict(
        lambda: {
            "semanticCount": 0,
            "fingerprintCount": 0,
            "confSamples": [],
            "mappingReliabilitySamples": [],
            "fingerprintCounts": Counter(),
            "semanticHeadCounts": Counter(),
            "exprKindCounts": Counter(),
            "arityShapeCounts": Counter(),
            "binderShapeCounts": Counter(),
            "clusterKeyCounts": Counter(),
            "matchProvenanceCounts": Counter(),
            "sourceFiles": set(),
            "surfaceCounts": Counter(),
        }
    )

    for obs in observations:
        surface = str(obs.get("surface") or "unknown")
        head = obs.get("semanticHead") or obs.get("head")
        source = str(obs.get("headSource") or "unavailable")
        fingerprint = obs.get("fingerprintV1") or obs.get("fingerprint")
        expr_kind_any = obs.get("exprKind")
        expr_kind = expr_kind_any if isinstance(expr_kind_any, str) and expr_kind_any else "unknown"
        arity_shape_any = obs.get("arityShape")
        arity_shape_value = arity_shape_any if isinstance(arity_shape_any, str) and arity_shape_any else "arity:?"
        binder_shape_any = obs.get("binderShape")
        binder_shape_value = (
            binder_shape_any if isinstance(binder_shape_any, str) and binder_shape_any else "binder:?"
        )
        source_file = obs.get("sourceFile")
        decl_name = obs.get("declName")
        diag_provs = [str(p) for p in obs.get("diagnosticProvenance", [])]
        cluster_key = make_cluster_key(
            fingerprint_v1=fingerprint if isinstance(fingerprint, str) else None,
            semantic_head=head if isinstance(head, str) else None,
            expr_kind=expr_kind,
            arity_shape_value=arity_shape_value,
            binder_shape_value=binder_shape_value,
        )

        conf_any = obs.get("observationConfidence")
        if isinstance(conf_any, (int, float)):
            obs_conf = clamp01(float(conf_any))
        else:
            s_weight = source_weight(source)
            d_weight = diag_weight(diag_provs)
            obs_conf = clamp01(0.7 * s_weight + 0.3 * d_weight)

        if source_file:
            fstats = file_signals[source_file]
            fstats["confSamples"].append(obs_conf)
            if source == "exprSemantic" and head:
                fstats["semanticCount"] += 1
            if source == "exprSemantic" and fingerprint:
                fstats["fingerprintCount"] += 1
            if source == "exprSemantic" and isinstance(head, str) and head:
                cast(Counter[str], fstats["semanticHeadCounts"])[head] += 1
            if source == "exprSemantic" and isinstance(fingerprint, str) and fingerprint:
                cast(Counter[str], fstats["fingerprintCounts"])[fingerprint] += 1
            if source == "exprSemantic" and expr_kind:
                cast(Counter[str], fstats["exprKindCounts"])[expr_kind] += 1
            if source == "exprSemantic" and arity_shape_value:
                cast(Counter[str], fstats["arityShapeCounts"])[arity_shape_value] += 1
            if source == "exprSemantic" and binder_shape_value:
                cast(Counter[str], fstats["binderShapeCounts"])[binder_shape_value] += 1
            if source == "exprSemantic":
                cast(Counter[str], fstats["clusterKeyCounts"])[cluster_key] += 1

        if isinstance(decl_name, str) and decl_name:
            dstats = decl_signals[decl_name]
            decl_match_prov_any = obs.get("declMatchProvenance")
            decl_match_prov = decl_match_prov_any if isinstance(decl_match_prov_any, str) else "unmatched"
            decl_rel_any = obs.get("declMatchReliability")
            if isinstance(decl_rel_any, (int, float)):
                decl_rel = clamp01(float(decl_rel_any))
            else:
                decl_rel = DECL_MATCH_RELIABILITY.get(decl_match_prov, DECL_MATCH_RELIABILITY["unmatched"])
            effective_conf = clamp01(obs_conf * max(0.2, decl_rel))

            dstats["confSamples"].append(effective_conf)
            dstats["mappingReliabilitySamples"].append(decl_rel)
            cast(Counter[str], dstats["matchProvenanceCounts"])[decl_match_prov] += 1
            cast(Counter[str], dstats["surfaceCounts"])[surface] += 1
            if source_file:
                cast(set[str], dstats["sourceFiles"]).add(source_file)
            if source == "exprSemantic" and head:
                dstats["semanticCount"] += 1
            if source == "exprSemantic" and fingerprint:
                dstats["fingerprintCount"] += 1
            if source == "exprSemantic" and isinstance(head, str) and head:
                cast(Counter[str], dstats["semanticHeadCounts"])[head] += 1
            if source == "exprSemantic" and isinstance(fingerprint, str) and fingerprint:
                cast(Counter[str], dstats["fingerprintCounts"])[fingerprint] += 1
            if source == "exprSemantic" and expr_kind:
                cast(Counter[str], dstats["exprKindCounts"])[expr_kind] += 1
            if source == "exprSemantic" and arity_shape_value:
                cast(Counter[str], dstats["arityShapeCounts"])[arity_shape_value] += 1
            if source == "exprSemantic" and binder_shape_value:
                cast(Counter[str], dstats["binderShapeCounts"])[binder_shape_value] += 1
            if source == "exprSemantic":
                cast(Counter[str], dstats["clusterKeyCounts"])[cluster_key] += 1

        if source == "exprSemantic" and isinstance(head, str) and head:
            gkey = (surface, head)
            group = semantic_groups.setdefault(
                gkey,
                {
                    "surface": surface,
                    "head": head,
                    "count": 0,
                    "files": set(),
                    "fingerprints": Counter(),
                    "diagProvenance": Counter(),
                    "confSamples": [],
                },
            )
            group["count"] += 1
            if source_file:
                group["files"].add(source_file)
            if isinstance(fingerprint, str) and fingerprint:
                group["fingerprints"][fingerprint] += 1
            for prov in diag_provs:
                group["diagProvenance"][prov] += 1
            group["confSamples"].append(obs_conf)

        if source == "exprSemantic" and isinstance(fingerprint, str) and fingerprint:
            fkey = (surface, fingerprint)
            group2 = fingerprint_groups.setdefault(
                fkey,
                {
                    "surface": surface,
                    "fingerprint": fingerprint,
                    "count": 0,
                    "heads": Counter(),
                    "files": set(),
                    "diagProvenance": Counter(),
                    "confSamples": [],
                },
            )
            group2["count"] += 1
            if isinstance(head, str) and head:
                group2["heads"][head] += 1
            if source_file:
                group2["files"].add(source_file)
            for prov in diag_provs:
                group2["diagProvenance"][prov] += 1
            group2["confSamples"].append(obs_conf)

        if source == "exprSemantic":
            shape_key = (
                str(fingerprint or "none"),
                str(head or "none"),
                expr_kind,
                arity_shape_value,
                binder_shape_value,
            )
            shape_group = shape_groups.setdefault(
                shape_key,
                {
                    "fingerprintV1": shape_key[0],
                    "semanticHead": shape_key[1],
                    "exprKind": shape_key[2],
                    "arityShape": shape_key[3],
                    "binderShape": shape_key[4],
                    "clusterKey": cluster_key,
                    "count": 0,
                    "files": set(),
                    "decls": set(),
                    "diagProvenance": Counter(),
                    "confSamples": [],
                    "surfaceCounts": Counter(),
                },
            )
            shape_group["count"] += 1
            if isinstance(source_file, str) and source_file:
                shape_group["files"].add(source_file)
            if isinstance(decl_name, str) and decl_name:
                shape_group["decls"].add(decl_name)
            for prov in diag_provs:
                shape_group["diagProvenance"][prov] += 1
            shape_group["confSamples"].append(obs_conf)
            shape_group["surfaceCounts"][surface] += 1

    semantic_out: list[JsonObj] = []
    for group in semantic_groups.values():
        diag_hist = dict(group["diagProvenance"])
        avg_diag = safe_mean(
            [DIAG_PROVENANCE_WEIGHT.get(k, DIAG_PROVENANCE_WEIGHT["fallback"]) for k in group["diagProvenance"]],
            default=DIAG_PROVENANCE_WEIGHT["fallback"],
        )
        semantic_out.append(
            {
                "surface": group["surface"],
                "head": group["head"],
                "count": group["count"],
                "files": sorted(group["files"]),
                "fingerprints": group["fingerprints"].most_common(),
                "groupConfidence": round(safe_mean(group["confSamples"], default=0.0), 4),
                "confidenceProvenance": [
                    {
                        "signal": "headSource",
                        "weight": HEAD_SOURCE_WEIGHT["exprSemantic"],
                        "evidence": "exprSemantic",
                    },
                    {
                        "signal": "diagnosticProvenance",
                        "weight": round(avg_diag, 4),
                        "evidence": json.dumps(diag_hist, sort_keys=True),
                    },
                ],
            }
        )

    fingerprint_out: list[JsonObj] = []
    for group in fingerprint_groups.values():
        diag_hist = dict(group["diagProvenance"])
        avg_diag = safe_mean(
            [DIAG_PROVENANCE_WEIGHT.get(k, DIAG_PROVENANCE_WEIGHT["fallback"]) for k in group["diagProvenance"]],
            default=DIAG_PROVENANCE_WEIGHT["fallback"],
        )
        fingerprint_out.append(
            {
                "surface": group["surface"],
                "fingerprint": group["fingerprint"],
                "count": group["count"],
                "heads": group["heads"].most_common(),
                "files": sorted(group["files"]),
                "groupConfidence": round(safe_mean(group["confSamples"], default=0.0), 4),
                "confidenceProvenance": [
                    {
                        "signal": "headSource",
                        "weight": HEAD_SOURCE_WEIGHT["exprSemantic"],
                        "evidence": "exprSemantic",
                    },
                    {
                        "signal": "diagnosticProvenance",
                        "weight": round(avg_diag, 4),
                        "evidence": json.dumps(diag_hist, sort_keys=True),
                    },
                ],
            }
        )

    shape_out: list[JsonObj] = []
    for group in shape_groups.values():
        diag_hist = dict(group["diagProvenance"])
        avg_diag = safe_mean(
            [DIAG_PROVENANCE_WEIGHT.get(k, DIAG_PROVENANCE_WEIGHT["fallback"]) for k in group["diagProvenance"]],
            default=DIAG_PROVENANCE_WEIGHT["fallback"],
        )
        shape_out.append(
            {
                "clusterKey": group["clusterKey"],
                "fingerprintV1": group["fingerprintV1"],
                "semanticHead": group["semanticHead"],
                "exprKind": group["exprKind"],
                "arityShape": group["arityShape"],
                "binderShape": group["binderShape"],
                "count": group["count"],
                "files": sorted(group["files"]),
                "declarations": sorted(group["decls"]),
                "surfaceCounts": dict(group["surfaceCounts"]),
                "groupConfidence": round(safe_mean(group["confSamples"], default=0.0), 4),
                "confidenceProvenance": [
                    {
                        "signal": "headSource",
                        "weight": HEAD_SOURCE_WEIGHT["exprSemantic"],
                        "evidence": "exprSemantic",
                    },
                    {
                        "signal": "diagnosticProvenance",
                        "weight": round(avg_diag, 4),
                        "evidence": json.dumps(diag_hist, sort_keys=True),
                    },
                ],
            }
        )

    semantic_out.sort(key=lambda x: (-x["count"], -x["groupConfidence"], x["surface"], x["head"]))
    fingerprint_out.sort(key=lambda x: (-x["count"], -x["groupConfidence"], x["surface"], x["fingerprint"]))
    shape_out.sort(
        key=lambda x: (
            -x["count"],
            -x["groupConfidence"],
            str(x.get("exprKind") or ""),
            str(x.get("semanticHead") or ""),
            str(x.get("fingerprintV1") or ""),
        )
    )

    file_signal_out: dict[str, JsonObj] = {}
    for fpath, stats in file_signals.items():
        file_signal_out[fpath] = {
            "semanticCount": stats["semanticCount"],
            "fingerprintCount": stats["fingerprintCount"],
            "avgConfidence": round(safe_mean(stats["confSamples"], default=0.0), 4),
            "fingerprintCounts": top_counts(cast(Counter[str], stats["fingerprintCounts"])),
            "semanticHeadCounts": top_counts(cast(Counter[str], stats["semanticHeadCounts"])),
            "exprKindCounts": top_counts(cast(Counter[str], stats["exprKindCounts"])),
            "arityShapeCounts": top_counts(cast(Counter[str], stats["arityShapeCounts"])),
            "binderShapeCounts": top_counts(cast(Counter[str], stats["binderShapeCounts"])),
            "clusterKeys": top_counts(cast(Counter[str], stats["clusterKeyCounts"])),
        }

    decl_signal_out: dict[str, JsonObj] = {}
    for decl, stats in decl_signals.items():
        decl_signal_out[decl] = {
            "semanticCount": stats["semanticCount"],
            "fingerprintCount": stats["fingerprintCount"],
            "avgConfidence": round(safe_mean(stats["confSamples"], default=0.0), 4),
            "avgMappingReliability": round(safe_mean(stats["mappingReliabilitySamples"], default=0.0), 4),
            "fingerprintCounts": top_counts(cast(Counter[str], stats["fingerprintCounts"])),
            "semanticHeadCounts": top_counts(cast(Counter[str], stats["semanticHeadCounts"])),
            "exprKindCounts": top_counts(cast(Counter[str], stats["exprKindCounts"])),
            "arityShapeCounts": top_counts(cast(Counter[str], stats["arityShapeCounts"])),
            "binderShapeCounts": top_counts(cast(Counter[str], stats["binderShapeCounts"])),
            "clusterKeys": top_counts(cast(Counter[str], stats["clusterKeyCounts"])),
            "matchProvenanceCounts": dict(cast(Counter[str], stats["matchProvenanceCounts"])),
            "sourceFiles": sorted(cast(set[str], stats["sourceFiles"])),
            "surfaceCounts": dict(cast(Counter[str], stats["surfaceCounts"])),
        }

    summary: JsonObj = {
        "payloadObservationCount": len(observations),
        "semanticHeadGroupCount": len(semantic_out),
        "fingerprintGroupCount": len(fingerprint_out),
        "shapeClusterGroupCount": len(shape_out),
        "declarationSignalCount": len(decl_signal_out),
        "declarationMatchProvenance": dict(
            Counter(
                str(obs.get("declMatchProvenance") or "unmatched")
                for obs in observations
            )
        ),
        "semanticHeadGroups": semantic_out,
        "fingerprintGroups": fingerprint_out,
        "shapeClusters": shape_out,
    }
    return summary, file_signal_out, decl_signal_out


def file_domain(file_path: str | None) -> str | None:
    if not file_path:
        return None
    parts = Path(file_path).parts
    if len(parts) >= 3 and parts[0] == "lean" and parts[1] == "InfoGeometry":
        return parts[2]
    return None


def rank_vacuity_candidates(
    theorem_entries: list[JsonObj],
    module_region: dict[str, str],
    file_region: dict[str, str],
    hole_counts: dict[str, int],
    bridge_file_signals: dict[str, JsonObj],
    bridge_decl_signals: dict[str, JsonObj],
    top_k: int,
) -> list[JsonObj]:
    ranked: list[RankedEntry] = []

    for row in theorem_entries:
        if row.get("kind") != "theorem":
            continue
        tags = set(row.get("tags") or [])
        raw_violations = row.get("violations")
        violations = raw_violations if isinstance(raw_violations, list) else []
        if not (tags & VACUITY_TAGS or violations):
            continue

        name = str(row.get("name") or "")
        if not name:
            continue

        file_path = row.get("file") if isinstance(row.get("file"), str) else None
        module = row.get("module") if isinstance(row.get("module"), str) else None
        if module:
            region = module_region.get(module, file_region.get(file_path or "", "unknown"))
        else:
            region = file_region.get(file_path or "", "unknown")

        signals: list[Signal] = []

        if "wrapper-candidate" in tags:
            signals.append(Signal("tag.wrapper-candidate", 0.34, 0.82, "wrapper-candidate"))
        if "dead-candidate" in tags:
            signals.append(Signal("tag.dead-candidate", 0.28, 0.84, "dead-candidate"))
        if "rfl-like" in tags:
            signals.append(Signal("tag.rfl-like", 0.18, 0.74, "rfl-like"))
        if "proof-infrastructure" in tags:
            signals.append(Signal("tag.proof-infrastructure", 0.10, 0.72, "proof-infrastructure"))

        levels: list[str] = []
        for violation_any in violations:
            if isinstance(violation_any, dict):
                violation = cast(JsonObj, violation_any)
                level = violation.get("level")
                if isinstance(level, str):
                    levels.append(level)
        if "error" in levels:
            signals.append(Signal("violation.error", 0.20, VIOLATION_LEVEL_WEIGHT["error"], "error-level violation present"))
        elif "warning" in levels:
            signals.append(Signal("violation.warning", 0.12, VIOLATION_LEVEL_WEIGHT["warning"], "warning-level violation present"))

        if int(row.get("reverse_type", 0)) == 0:
            signals.append(Signal("graph.zero-reverse-type", 0.06, 0.70, "reverse_type = 0"))
        if int(row.get("reverse_value", 0)) == 0:
            signals.append(Signal("graph.zero-reverse-value", 0.05, 0.68, "reverse_value = 0"))
        if bool(row.get("is_sink", False)):
            signals.append(Signal("graph.sink", 0.03, 0.62, "is_sink = true"))

        if isinstance(file_path, str):
            hole_count = hole_counts.get(file_path, 0)
            if hole_count > 0:
                hole_boost = min(0.18, 0.04 * hole_count)
                signals.append(
                    Signal(
                        "proof-holes.by-file",
                        hole_boost,
                        0.88,
                        f"explicit proof holes in file: {hole_count}",
                    )
                )

        semantic_profile: JsonObj | None = None
        profile_scope = "none"
        profile_mapping = "none"
        profile_mapping_reliability = 0.0

        decl_signal = bridge_decl_signals.get(name)
        if isinstance(decl_signal, dict):
            semantic_profile = dict(decl_signal)
            profile_scope = "declaration"
            match_counts_any = decl_signal.get("matchProvenanceCounts")
            if isinstance(match_counts_any, dict) and match_counts_any:
                match_counts = {
                    str(k): int(v)
                    for k, v in match_counts_any.items()
                    if isinstance(v, (int, float))
                }
                if match_counts:
                    top_match = max(match_counts.items(), key=lambda item: item[1])[0]
                    profile_mapping = top_match
                else:
                    profile_mapping = "declaration"
            else:
                profile_mapping = "declaration"
            profile_mapping_reliability = clamp01(float(decl_signal.get("avgMappingReliability", 0.0)))
            if profile_mapping_reliability <= 0.0:
                profile_mapping_reliability = 0.70
        elif isinstance(file_path, str):
            file_signal = bridge_file_signals.get(file_path)
            if isinstance(file_signal, dict):
                semantic_profile = dict(file_signal)
                profile_scope = "file"
                profile_mapping = "file-fallback"
                profile_mapping_reliability = 0.62

        if semantic_profile is not None:
            sem_count = int(semantic_profile.get("semanticCount", 0))
            fp_count = int(semantic_profile.get("fingerprintCount", 0))
            bridge_conf = clamp01(float(semantic_profile.get("avgConfidence", 0.0)))
            scoped_conf = clamp01(bridge_conf * profile_mapping_reliability)
            sem_scale = 0.13 if profile_scope == "declaration" else 0.09
            fp_scale = 0.08 if profile_scope == "declaration" else 0.05
            if sem_count > 0:
                sem_boost = sem_scale * min(1.0, sem_count / 3.0)
                signals.append(
                    Signal(
                        f"bridge.{profile_scope}.semantic-shape",
                        sem_boost,
                        scoped_conf,
                        f"{profile_mapping}: semantic observations={sem_count}",
                    )
                )
            if fp_count > 0:
                fp_boost = fp_scale * min(1.0, fp_count / 3.0)
                signals.append(
                    Signal(
                        f"bridge.{profile_scope}.fingerprint-shape",
                        fp_boost,
                        scoped_conf,
                        f"{profile_mapping}: fingerprint observations={fp_count}",
                    )
                )

        cluster_counts = semantic_profile.get("clusterKeys") if semantic_profile else None
        cluster_key = None
        if isinstance(cluster_counts, list) and cluster_counts:
            first = cluster_counts[0]
            if isinstance(first, (list, tuple)) and first and isinstance(first[0], str):
                cluster_key = first[0]
        if not cluster_key:
            cluster_key = make_cluster_key(
                fingerprint_v1=None,
                semantic_head=name,
                expr_kind="unknown",
                arity_shape_value="arity:?",
                binder_shape_value="binder:?",
            )

        score, confidence, provenance = summarize_signals(signals)
        semantic_profile_summary: JsonObj | None = None
        if semantic_profile is not None:
            semantic_profile_summary = {
                "scope": profile_scope,
                "mapping": profile_mapping,
                "mappingReliability": round(profile_mapping_reliability, 4),
                "semanticCount": int(semantic_profile.get("semanticCount", 0)),
                "fingerprintCount": int(semantic_profile.get("fingerprintCount", 0)),
                "avgConfidence": round(float(semantic_profile.get("avgConfidence", 0.0)), 4),
                "avgMappingReliability": round(float(semantic_profile.get("avgMappingReliability", 0.0)), 4),
                "semanticHeadCounts": semantic_profile.get("semanticHeadCounts", []),
                "fingerprintCounts": semantic_profile.get("fingerprintCounts", []),
                "exprKindCounts": semantic_profile.get("exprKindCounts", []),
                "arityShapeCounts": semantic_profile.get("arityShapeCounts", []),
                "binderShapeCounts": semantic_profile.get("binderShapeCounts", []),
                "clusterKeys": semantic_profile.get("clusterKeys", []),
                "matchProvenanceCounts": semantic_profile.get("matchProvenanceCounts", {}),
            }
        payload: JsonObj = {
            "name": name,
            "file": file_path,
            "module": module,
            "region": region,
            "tags": sorted(tags),
            "violations": violations,
            "semanticClusterKey": cluster_key,
            "semanticProfile": semantic_profile_summary,
            "score": round(score, 4),
            "confidence": round(confidence, 4),
            "confidenceProvenance": provenance,
        }
        ranked.append(RankedEntry(key=name, score=score, confidence=confidence, payload=payload))

    ranked.sort(key=lambda x: (-x.score, -x.confidence, x.key))
    out: list[JsonObj] = []
    for i, entry in enumerate(ranked[:top_k], start=1):
        row = dict(entry.payload)
        row["rank"] = i
        out.append(row)
    return out


def rank_owner_candidates(
    vacuity_candidates: list[JsonObj],
    owner_entries: list[JsonObj],
    file_region: dict[str, str],
    top_k: int,
) -> list[JsonObj]:
    agg_score: dict[str, float] = defaultdict(float)
    agg_signals: dict[str, list[Signal]] = defaultdict(list)
    support: dict[str, set[str]] = defaultdict(set)

    owner_by_file: dict[str, JsonObj] = {str(e.get("file")): e for e in owner_entries if e.get("file")}

    for cand in vacuity_candidates:
        cand_name = str(cand.get("name"))
        cand_file = cand.get("file")
        cand_region = cand.get("region") or file_region.get(str(cand_file), "unknown")
        cand_domain = file_domain(str(cand_file) if isinstance(cand_file, str) else None)
        cand_score = float(cand.get("score", 0.0))

        for owner_file, owner in owner_by_file.items():
            owner_region = file_region.get(owner_file, "unknown")
            owner_domain = file_domain(owner_file)

            local_signals: list[Signal] = []
            if cand_file == owner_file:
                local_signals.append(Signal("owner.exact-file", 0.75 * cand_score, 0.95, f"{cand_name} is in owner file"))
            if cand_region != "unknown" and cand_region == owner_region:
                local_signals.append(Signal("owner.same-region", 0.35 * cand_score, 0.76, f"shared region: {cand_region}"))
            if cand_domain and owner_domain and cand_domain == owner_domain:
                local_signals.append(Signal("owner.same-domain", 0.20 * cand_score, 0.72, f"shared domain: {cand_domain}"))

            if not local_signals:
                continue

            base = sum(max(0.0, s.contribution) for s in local_signals)
            agg_score[owner_file] += base
            agg_signals[owner_file].extend(local_signals)
            support[owner_file].add(cand_name)

    ranked: list[RankedEntry] = []
    for owner_file, _score in agg_score.items():
        signals = agg_signals[owner_file]
        final_score, confidence, provenance = summarize_signals(signals)
        owner = owner_by_file[owner_file]
        owner_region = file_region.get(owner_file, "unknown")
        payload: JsonObj = {
            "ownerFile": owner_file,
            "region": owner_region,
            "sourceDepth": owner.get("source_depth"),
            "targetDepth": owner.get("target_depth"),
            "notes": owner.get("notes", ""),
            "supportingVacuityCandidates": sorted(support[owner_file]),
            "score": round(final_score, 4),
            "confidence": round(confidence, 4),
            "confidenceProvenance": provenance,
        }
        ranked.append(RankedEntry(key=owner_file, score=final_score, confidence=confidence, payload=payload))

    ranked.sort(key=lambda x: (-x.score, -x.confidence, x.key))
    out: list[JsonObj] = []
    for i, entry in enumerate(ranked[:top_k], start=1):
        row = dict(entry.payload)
        row["rank"] = i
        out.append(row)
    return out


def rank_declaration_plans(
    vacuity_candidates: list[JsonObj],
    owner_candidates: list[JsonObj],
    replacement_candidates: list[JsonObj],
    bridge_decl_signals: dict[str, JsonObj],
    top_k: int,
) -> list[JsonObj]:
    owner_by_file: dict[str, JsonObj] = {
        str(row.get("ownerFile")): row
        for row in owner_candidates
        if isinstance(row.get("ownerFile"), str)
    }
    replacements = [row for row in replacement_candidates if isinstance(row, dict)]

    ranked: list[RankedEntry] = []

    for cand in vacuity_candidates:
        cand_name = cand.get("name")
        if not isinstance(cand_name, str) or not cand_name:
            continue

        cand_file = cand.get("file") if isinstance(cand.get("file"), str) else None
        cand_region = cand.get("region") if isinstance(cand.get("region"), str) else "unknown"
        cand_score = clamp01(float(cand.get("score", 0.0)))
        cand_conf = clamp01(float(cand.get("confidence", 0.0)))
        cand_profile_any = cand.get("semanticProfile")
        cand_profile = cast(JsonObj, cand_profile_any) if isinstance(cand_profile_any, dict) else {}

        plan_signals: list[Signal] = [
            Signal(
                "candidate.vacuity-prior",
                0.32 * cand_score,
                max(0.45, cand_conf),
                f"candidate score={cand_score:.4f}",
            )
        ]

        owner_best: JsonObj | None = None
        owner_best_score = 0.0
        owner_best_conf = 0.0
        owner_best_prov: list[JsonObj] = []
        for owner in owner_by_file.values():
            owner_file = owner.get("ownerFile")
            if not isinstance(owner_file, str):
                continue
            owner_region = owner.get("region") if isinstance(owner.get("region"), str) else "unknown"
            owner_support_any = owner.get("supportingVacuityCandidates")
            owner_support = (
                set(owner_support_any)
                if isinstance(owner_support_any, list)
                else set()
            )

            owner_signals: list[Signal] = []
            if cand_file and cand_file == owner_file:
                owner_signals.append(
                    Signal(
                        "owner.same-file",
                        0.28 * cand_score,
                        0.95,
                        f"candidate file matches owner file: {owner_file}",
                    )
                )
            if cand_region != "unknown" and cand_region == owner_region:
                owner_signals.append(
                    Signal(
                        "owner.same-region",
                        0.14 * cand_score,
                        0.78,
                        f"candidate region matches owner region: {cand_region}",
                    )
                )
            if cand_name in owner_support:
                owner_signals.append(
                    Signal(
                        "owner.support-link",
                        0.22 * cand_score,
                        0.86,
                        f"owner already supported by candidate {cand_name}",
                    )
                )

            if not owner_signals:
                continue
            local_score, local_conf, local_prov = summarize_signals(owner_signals)
            if local_score > owner_best_score or (
                abs(local_score - owner_best_score) < 1e-9 and local_conf > owner_best_conf
            ):
                owner_best = owner
                owner_best_score = local_score
                owner_best_conf = local_conf
                owner_best_prov = local_prov

        if owner_best is not None:
            owner_file = cast(str, owner_best.get("ownerFile"))
            plan_signals.append(
                Signal(
                    "owner.best-corridor",
                    0.24 * owner_best_score,
                    owner_best_conf,
                    f"selected owner={owner_file}",
                )
            )

        cand_clusters = keys_from_counts(cand_profile.get("clusterKeys"))
        cand_heads = keys_from_counts(cand_profile.get("semanticHeadCounts"))
        cand_fps = keys_from_counts(cand_profile.get("fingerprintCounts"))

        corridor_rows: list[JsonObj] = []
        for repl in replacements:
            repl_decl = repl.get("replacementDecl")
            if not isinstance(repl_decl, str) or not repl_decl:
                continue
            repl_support_any = repl.get("supportingVacuityCandidates")
            repl_support = set(repl_support_any) if isinstance(repl_support_any, list) else set()
            repl_region = repl.get("region") if isinstance(repl.get("region"), str) else "unknown"
            owner_corridor_any = repl.get("ownerCorridor")
            owner_corridor = set(owner_corridor_any) if isinstance(owner_corridor_any, list) else set()

            repl_signals: list[Signal] = []
            if cand_name in repl_support:
                repl_signals.append(
                    Signal(
                        "replacement.support-link",
                        0.30 * cand_score,
                        0.90,
                        f"replacement already supported by candidate {cand_name}",
                    )
                )
            if cand_region != "unknown" and cand_region == repl_region:
                repl_signals.append(
                    Signal(
                        "replacement.same-region",
                        0.10 * cand_score,
                        0.74,
                        f"replacement region matches candidate region: {cand_region}",
                    )
                )
            if owner_best is not None:
                owner_file = cast(str, owner_best.get("ownerFile"))
                if owner_file in owner_corridor:
                    repl_signals.append(
                        Signal(
                            "replacement.owner-corridor",
                            0.16 * cand_score,
                            0.84,
                            f"replacement corridor includes selected owner {owner_file}",
                        )
                    )

            repl_decl_profile = bridge_decl_signals.get(repl_decl)
            if isinstance(repl_decl_profile, dict):
                repl_clusters = keys_from_counts(repl_decl_profile.get("clusterKeys"))
                repl_heads = keys_from_counts(repl_decl_profile.get("semanticHeadCounts"))
                repl_fps = keys_from_counts(repl_decl_profile.get("fingerprintCounts"))
                cluster_overlap = jaccard_overlap(cand_clusters, repl_clusters)
                head_overlap = jaccard_overlap(cand_heads, repl_heads)
                fp_overlap = jaccard_overlap(cand_fps, repl_fps)
                overlap = 0.5 * cluster_overlap + 0.3 * head_overlap + 0.2 * fp_overlap
                if overlap > 0.0:
                    repl_signals.append(
                        Signal(
                            "replacement.decl-shape-overlap",
                            0.18 * cand_score * overlap,
                            0.80,
                            (
                                "bridge declaration overlap "
                                f"(cluster={cluster_overlap:.3f}, head={head_overlap:.3f}, fp={fp_overlap:.3f})"
                            ),
                        )
                    )

            repl_prior_score = clamp01(float(repl.get("score", 0.0)))
            repl_prior_conf = clamp01(float(repl.get("confidence", 0.0)))
            if repl_prior_score > 0.0:
                repl_signals.append(
                    Signal(
                        "replacement.rank-prior",
                        0.14 * repl_prior_score,
                        max(0.40, repl_prior_conf),
                        f"replacement ranking prior={repl_prior_score:.4f}",
                    )
                )

            if not repl_signals:
                continue
            repl_score, repl_conf, repl_prov = summarize_signals(repl_signals)
            if repl_score <= 0.0:
                continue
            corridor_rows.append(
                {
                    "replacementDecl": repl_decl,
                    "region": repl_region,
                    "score": round(repl_score, 4),
                    "confidence": round(repl_conf, 4),
                    "confidenceProvenance": repl_prov,
                }
            )

        corridor_rows.sort(
            key=lambda row: (
                -float(row.get("score", 0.0)),
                -float(row.get("confidence", 0.0)),
                str(row.get("replacementDecl", "")),
            )
        )
        probable_corridor = corridor_rows[:3]

        if probable_corridor:
            best_repl = probable_corridor[0]
            plan_signals.append(
                Signal(
                    "replacement.best-corridor",
                    0.24 * clamp01(float(best_repl.get("score", 0.0))),
                    clamp01(float(best_repl.get("confidence", 0.0))),
                    f"selected replacement={best_repl.get('replacementDecl')}",
                )
            )
            if len(probable_corridor) > 1:
                plan_signals.append(
                    Signal(
                        "replacement.alternatives",
                        min(0.06, 0.02 * (len(probable_corridor) - 1)),
                        0.62,
                        f"alternative corridor count={len(probable_corridor)}",
                    )
                )

        score, confidence, provenance = summarize_signals(plan_signals)

        owner_payload: JsonObj | None = None
        if owner_best is not None:
            owner_payload = {
                "ownerFile": owner_best.get("ownerFile"),
                "region": owner_best.get("region"),
                "score": round(owner_best_score, 4),
                "confidence": round(owner_best_conf, 4),
                "confidenceProvenance": owner_best_prov,
            }

        payload: JsonObj = {
            "candidate": cand_name,
            "candidateFile": cand_file,
            "candidateRegion": cand_region,
            "candidateScore": round(cand_score, 4),
            "candidateConfidence": round(cand_conf, 4),
            "probable_owner": owner_payload,
            "probable_replacement_corridor": probable_corridor,
            "score": round(score, 4),
            "confidence": round(confidence, 4),
            "confidenceProvenance": provenance,
        }
        ranked.append(RankedEntry(key=cand_name, score=score, confidence=confidence, payload=payload))

    ranked.sort(key=lambda x: (-x.score, -x.confidence, x.key))
    out: list[JsonObj] = []
    for i, entry in enumerate(ranked[:top_k], start=1):
        row = dict(entry.payload)
        row["rank"] = i
        out.append(row)
    return out


def rank_fingerprint_corridors(
    vacuity_candidates: list[JsonObj],
    replacement_candidates: list[JsonObj],
    bridge_decl_signals: dict[str, JsonObj],
    top_k: int,
) -> list[JsonObj]:
    buckets: dict[str, JsonObj] = {}

    def ensure_bucket(cluster_key: str) -> JsonObj:
        bucket = buckets.get(cluster_key)
        if isinstance(bucket, dict):
            return bucket
        bucket = {
            "clusterKey": cluster_key,
            "vacuityCandidates": [],
            "replacementCandidates": [],
            "scoreSamples": [],
            "confidenceSamples": [],
            "regionCounts": Counter(),
        }
        buckets[cluster_key] = bucket
        return bucket

    for cand in vacuity_candidates:
        cluster_any = cand.get("semanticClusterKey")
        if not isinstance(cluster_any, str) or not cluster_any:
            continue
        bucket = ensure_bucket(cluster_any)
        name = cand.get("name")
        if not isinstance(name, str) or not name:
            continue
        score = clamp01(float(cand.get("score", 0.0)))
        confidence = clamp01(float(cand.get("confidence", 0.0)))
        region = cand.get("region") if isinstance(cand.get("region"), str) else "unknown"
        cast(list[JsonObj], bucket["vacuityCandidates"]).append(
            {
                "name": name,
                "score": round(score, 4),
                "confidence": round(confidence, 4),
                "region": region,
            }
        )
        cast(list[float], bucket["scoreSamples"]).append(score)
        cast(list[float], bucket["confidenceSamples"]).append(confidence)
        cast(Counter[str], bucket["regionCounts"])[region] += 1

    for repl in replacement_candidates:
        repl_decl = repl.get("replacementDecl")
        if not isinstance(repl_decl, str) or not repl_decl:
            continue
        profile = bridge_decl_signals.get(repl_decl)
        if not isinstance(profile, dict):
            continue
        cluster_key = first_count_key(profile.get("clusterKeys"))
        if not isinstance(cluster_key, str) or not cluster_key:
            continue
        bucket = ensure_bucket(cluster_key)
        score = clamp01(float(repl.get("score", 0.0)))
        confidence = clamp01(float(repl.get("confidence", 0.0)))
        region = repl.get("region") if isinstance(repl.get("region"), str) else "unknown"
        cast(list[JsonObj], bucket["replacementCandidates"]).append(
            {
                "replacementDecl": repl_decl,
                "score": round(score, 4),
                "confidence": round(confidence, 4),
                "region": region,
            }
        )
        cast(list[float], bucket["scoreSamples"]).append(score)
        cast(list[float], bucket["confidenceSamples"]).append(confidence)
        cast(Counter[str], bucket["regionCounts"])[region] += 1

    ranked: list[RankedEntry] = []
    for cluster_key, bucket in buckets.items():
        vac_rows = cast(list[JsonObj], bucket["vacuityCandidates"])
        repl_rows = cast(list[JsonObj], bucket["replacementCandidates"])
        vac_rows.sort(key=lambda row: (-float(row.get("score", 0.0)), str(row.get("name", ""))))
        repl_rows.sort(
            key=lambda row: (-float(row.get("score", 0.0)), str(row.get("replacementDecl", "")))
        )

        vac_count = len(vac_rows)
        repl_count = len(repl_rows)
        if vac_count == 0 and repl_count == 0:
            continue

        coverage = min(1.0, vac_count / 3.0)
        corridor_depth = min(1.0, repl_count / 3.0)
        signal_strength = safe_mean(cast(list[float], bucket["scoreSamples"]), default=0.0)
        score = clamp01(0.42 * coverage + 0.28 * corridor_depth + 0.30 * signal_strength)
        confidence = clamp01(safe_mean(cast(list[float], bucket["confidenceSamples"]), default=0.0))

        payload: JsonObj = {
            "clusterKey": cluster_key,
            "vacuityCount": vac_count,
            "replacementCount": repl_count,
            "vacuityCandidates": vac_rows[:5],
            "replacementCandidates": repl_rows[:5],
            "regions": dict(cast(Counter[str], bucket["regionCounts"])),
            "score": round(score, 4),
            "confidence": round(confidence, 4),
            "confidenceProvenance": [
                {
                    "signal": "corridor.vacuity-coverage",
                    "contribution": round(0.42 * coverage, 4),
                    "reliability": 0.82,
                    "evidence": f"vacuity candidates={vac_count}",
                },
                {
                    "signal": "corridor.replacement-depth",
                    "contribution": round(0.28 * corridor_depth, 4),
                    "reliability": 0.80,
                    "evidence": f"replacement candidates={repl_count}",
                },
                {
                    "signal": "corridor.signal-strength",
                    "contribution": round(0.30 * signal_strength, 4),
                    "reliability": 0.78,
                    "evidence": f"mean candidate score={signal_strength:.4f}",
                },
            ],
        }
        ranked.append(RankedEntry(key=cluster_key, score=score, confidence=confidence, payload=payload))

    ranked.sort(key=lambda x: (-x.score, -x.confidence, x.key))
    out: list[JsonObj] = []
    for i, entry in enumerate(ranked[:top_k], start=1):
        row = dict(entry.payload)
        row["rank"] = i
        out.append(row)
    return out


def rank_replacement_candidates(
    vacuity_candidates: list[JsonObj],
    forward_edges: dict[str, list[tuple[str, str]]],
    decls: dict[str, JsonObj],
    theorem_by_name: dict[str, JsonObj],
    file_region: dict[str, str],
    owner_candidates: list[JsonObj],
    top_k: int,
) -> list[JsonObj]:
    owner_by_region: dict[str, list[str]] = defaultdict(list)
    for owner in owner_candidates:
        owner_file = owner.get("ownerFile")
        if not isinstance(owner_file, str):
            continue
        reg = file_region.get(owner_file, "unknown")
        owner_by_region[reg].append(owner_file)

    agg_score: dict[str, float] = defaultdict(float)
    agg_signals: dict[str, list[Signal]] = defaultdict(list)
    support: dict[str, set[str]] = defaultdict(set)

    for cand in vacuity_candidates:
        src_name = str(cand.get("name") or "")
        src_file = cand.get("file")
        src_region = cand.get("region") or file_region.get(str(src_file), "unknown")
        src_score = float(cand.get("score", 0.0))
        if not src_name:
            continue

        for dst, edge_kind in forward_edges.get(src_name, []):
            decl = decls.get(dst)
            if not decl:
                continue

            dst_kind = str(decl.get("kind", ""))
            if dst_kind not in {"theorem", "def", "lemma", "abbrev"}:
                continue

            dst_file = parse_uri_or_path(decl.get("file"), repo_root())
            dst_region = file_region.get(dst_file or "", "unknown")

            signals: list[Signal] = []
            if edge_kind == "value":
                signals.append(Signal("edge.value", 0.55 * src_score, 0.84, f"value-edge from {src_name}"))
            else:
                signals.append(Signal("edge.type", 0.35 * src_score, 0.74, f"type-edge from {src_name}"))

            dst_meta = theorem_by_name.get(dst)
            if dst_meta:
                dst_tags = set(dst_meta.get("tags") or [])
                if "dead-candidate" in dst_tags:
                    signals.append(Signal("dst.dead-penalty", -0.12 * src_score, 0.86, "destination tagged dead-candidate"))
                elif "wrapper-candidate" in dst_tags:
                    signals.append(Signal("dst.wrapper-penalty", -0.08 * src_score, 0.80, "destination tagged wrapper-candidate"))
                elif "statement-bearing" in dst_tags:
                    signals.append(Signal("dst.statement-bearing", 0.14 * src_score, 0.78, "destination tagged statement-bearing"))

            if src_region != "unknown" and src_region == dst_region:
                signals.append(Signal("region.match", 0.06 * src_score, 0.70, f"shared region: {src_region}"))

            if owner_by_region.get(dst_region):
                signals.append(Signal("owner.corridor-present", 0.05 * src_score, 0.68, f"owner corridor in region {dst_region}"))

            if not signals:
                continue

            local_score = sum(s.contribution for s in signals)
            if local_score <= 0:
                continue

            agg_score[dst] += local_score
            agg_signals[dst].extend(signals)
            support[dst].add(src_name)

    ranked: list[RankedEntry] = []
    for dst, _score in agg_score.items():
        decl = decls[dst]
        dst_file = parse_uri_or_path(decl.get("file"), repo_root())
        dst_region = file_region.get(dst_file or "", "unknown")
        score_clamped, confidence, provenance = summarize_signals(agg_signals[dst])
        payload: JsonObj = {
            "replacementDecl": dst,
            "kind": decl.get("kind"),
            "file": dst_file,
            "module": decl.get("module"),
            "region": dst_region,
            "ownerCorridor": owner_by_region.get(dst_region, [])[:3],
            "supportingVacuityCandidates": sorted(support[dst]),
            "score": round(score_clamped, 4),
            "confidence": round(confidence, 4),
            "confidenceProvenance": provenance,
        }
        ranked.append(RankedEntry(key=dst, score=score_clamped, confidence=confidence, payload=payload))

    ranked.sort(key=lambda x: (-x.score, -x.confidence, x.key))
    out: list[JsonObj] = []
    for i, entry in enumerate(ranked[:top_k], start=1):
        row = dict(entry.payload)
        row["rank"] = i
        out.append(row)
    return out


def make_markdown_report(report: JsonObj) -> str:
    lines: list[str] = []
    lines.append("# Vacuity Planner Report")
    lines.append("")
    lines.append("## Boundary")
    lines.append("")
    boundary = report.get("boundary", {})
    lines.append(f"- plannerMode: {boundary.get('plannerMode')}")
    lines.append(f"- mutationSurface: {boundary.get('mutationSurface')}")
    lines.append(f"- automaticReplacement: {boundary.get('automaticReplacement')}")
    lines.append(f"- proofRepair: {boundary.get('proofRepair')}")
    lines.append("")

    lines.append("## Input Coverage")
    lines.append("")
    inputs = report.get("inputs", {})
    lines.append(f"- theoremSignificanceEntries: {inputs.get('theoremSignificanceEntries', 0)}")
    lines.append(f"- declarationCount: {inputs.get('declarationCount', 0)}")
    lines.append(f"- edgeCount: {inputs.get('edgeCount', 0)}")
    lines.append(f"- ownerEntries: {inputs.get('ownerEntries', 0)}")
    lines.append(f"- bridgePayloadFiles: {inputs.get('bridgePayloadFiles', 0)}")
    lines.append(f"- bridgePayloadObjects: {inputs.get('bridgePayloadObjects', 0)}")
    lines.append("")

    norm = report.get("normalization", {})
    lines.append("## Normalization Snapshot")
    lines.append("")
    lines.append("### Top exprSemantic head groups")
    lines.append("")
    lines.append("| rank | surface | head | count | confidence |")
    lines.append("|---:|---|---|---:|---:|")
    for i, row in enumerate(norm.get("semanticHeadGroups", [])[:10], start=1):
        lines.append(
            f"| {i} | {row.get('surface')} | {row.get('head')} | {row.get('count')} | {row.get('groupConfidence')} |"
        )
    if not norm.get("semanticHeadGroups"):
        lines.append("| - | - | - | 0 | 0.0 |")
    lines.append("")

    lines.append("### Top fingerprint groups")
    lines.append("")
    lines.append("| rank | surface | fingerprint | count | confidence |")
    lines.append("|---:|---|---|---:|---:|")
    for i, row in enumerate(norm.get("fingerprintGroups", [])[:10], start=1):
        lines.append(
            f"| {i} | {row.get('surface')} | {row.get('fingerprint')} | {row.get('count')} | {row.get('groupConfidence')} |"
        )
    if not norm.get("fingerprintGroups"):
        lines.append("| - | - | - | 0 | 0.0 |")
    lines.append("")

    def emit_ranked_table(title: str, rows: list[JsonObj], cols: list[tuple[str, str]]) -> None:
        lines.append(f"## {title}")
        lines.append("")
        header = "| " + " | ".join(label for _, label in cols) + " |"
        sep = "|" + "|".join("---" for _ in cols) + "|"
        lines.append(header)
        lines.append(sep)
        for row in rows[:20]:
            values = [str(row.get(key, "")) for key, _ in cols]
            lines.append("| " + " | ".join(values) + " |")
        if not rows:
            lines.append("| - | - | - | - |")
        lines.append("")

    emit_ranked_table(
        "Ranked Vacuity Candidates",
        report.get("rankedVacuityCandidates", []),
        [("rank", "rank"), ("name", "declaration"), ("score", "score"), ("confidence", "confidence")],
    )
    emit_ranked_table(
        "Ranked Owner Candidates",
        report.get("rankedOwnerCandidates", []),
        [("rank", "rank"), ("ownerFile", "ownerFile"), ("score", "score"), ("confidence", "confidence")],
    )
    emit_ranked_table(
        "Ranked Replacement Candidates",
        report.get("rankedReplacementCandidates", []),
        [("rank", "rank"), ("replacementDecl", "replacementDecl"), ("score", "score"), ("confidence", "confidence")],
    )

    lines.append("## Ranked Fingerprint Corridors")
    lines.append("")
    lines.append("| rank | clusterKey | vacuityCount | replacementCount | score | confidence |")
    lines.append("|---:|---|---:|---:|---:|---:|")
    for row in report.get("rankedFingerprintCorridors", [])[:20]:
        lines.append(
            "| "
            + " | ".join(
                [
                    str(row.get("rank", "")),
                    str(row.get("clusterKey", "")),
                    str(row.get("vacuityCount", 0)),
                    str(row.get("replacementCount", 0)),
                    str(row.get("score", "")),
                    str(row.get("confidence", "")),
                ]
            )
            + " |"
        )
    if not report.get("rankedFingerprintCorridors"):
        lines.append("| - | - | 0 | 0 | 0.0 | 0.0 |")
    lines.append("")

    lines.append("## Ranked Declaration Plans")
    lines.append("")
    lines.append("| rank | candidate | probable_owner | probable_replacement | score | confidence |")
    lines.append("|---:|---|---|---|---:|---:|")
    for row in report.get("rankedDeclarationPlans", [])[:20]:
        owner_any = row.get("probable_owner")
        owner_file = owner_any.get("ownerFile") if isinstance(owner_any, dict) else ""
        corridor_any = row.get("probable_replacement_corridor")
        repl = ""
        if isinstance(corridor_any, list) and corridor_any:
            first = corridor_any[0]
            if isinstance(first, dict):
                repl = str(first.get("replacementDecl", ""))
        lines.append(
            "| "
            + " | ".join(
                [
                    str(row.get("rank", "")),
                    str(row.get("candidate", "")),
                    str(owner_file),
                    repl,
                    str(row.get("score", "")),
                    str(row.get("confidence", "")),
                ]
            )
            + " |"
        )
    if not report.get("rankedDeclarationPlans"):
        lines.append("| - | - | - | - | - | - |")
    lines.append("")

    lines.append("## Confidence Provenance Weights")
    lines.append("")
    lines.append("- headSourceWeight: " + json.dumps(HEAD_SOURCE_WEIGHT, sort_keys=True))
    lines.append("- diagnosticProvenanceWeight: " + json.dumps(DIAG_PROVENANCE_WEIGHT, sort_keys=True))
    lines.append("- violationLevelWeight: " + json.dumps(VIOLATION_LEVEL_WEIGHT, sort_keys=True))
    lines.append("")

    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    root = repo_root()

    parser = argparse.ArgumentParser(description="Planning-only vacuity planner skeleton")
    parser.add_argument("--bridge-input", action="append", default=[], help="JSON file/dir/glob with bridge payload data")
    parser.add_argument(
        "--theorem-significance",
        type=Path,
        default=root / "reports" / "theorem-significance.json",
        help="JSON report from tools/theorem_significance.py",
    )
    parser.add_argument(
        "--decls",
        type=Path,
        default=resolve_existing(
            root / "index" / "decls.jsonl",
            root / "artifacts" / "dag" / "index" / "decls.jsonl",
            root / ".build" / "index" / "decls.jsonl",
        )
        or (root / "index" / "decls.jsonl"),
        help="Declaration metadata JSONL",
    )
    parser.add_argument(
        "--edges",
        type=Path,
        default=resolve_existing(
            root / "index" / "edges.jsonl",
            root / "artifacts" / "dag" / "index" / "edges.jsonl",
            root / ".build" / "index" / "edges.jsonl",
        )
        or (root / "index" / "edges.jsonl"),
        help="Dependency edge metadata JSONL",
    )
    parser.add_argument(
        "--module-graph",
        type=Path,
        default=root / "docs-map" / "module_graph.json",
        help="Module graph JSON",
    )
    parser.add_argument(
        "--owner-index",
        type=Path,
        default=root / "reports" / "dag" / "representation-depth-index.json",
        help="Ownership index JSON",
    )
    parser.add_argument(
        "--proof-holes-by-file",
        type=Path,
        default=root / "reports" / "vacuity" / "wholecode-explicit-proof-holes-20260309.by-file.txt",
        help="Optional proof-hole count by file",
    )
    parser.add_argument(
        "--out-json",
        type=Path,
        default=root / "reports" / "vacuity-planner.json",
        help="Planner JSON output",
    )
    parser.add_argument(
        "--out-md",
        type=Path,
        default=root / "reports" / "vacuity-planner.md",
        help="Planner Markdown output",
    )
    parser.add_argument("--top-k", type=int, default=50, help="Maximum rows per ranked output")
    return parser.parse_args()


def main() -> None:
    root = repo_root()
    args = parse_args()

    theorem_significance_path = normalize_user_path(str(args.theorem_significance), args.theorem_significance)
    decls_path = normalize_user_path(str(args.decls), args.decls)
    edges_path = normalize_user_path(str(args.edges), args.edges)
    module_graph_path = normalize_user_path(str(args.module_graph), args.module_graph)
    owner_index_path = normalize_user_path(str(args.owner_index), args.owner_index)
    proof_holes_path = normalize_user_path(str(args.proof_holes_by_file), args.proof_holes_by_file)
    out_json_path = normalize_user_path(str(args.out_json), args.out_json)
    out_md_path = normalize_user_path(str(args.out_md), args.out_md)

    theorem_entries_raw = load_json(theorem_significance_path)
    if not isinstance(theorem_entries_raw, list):
        raise RuntimeError(f"Expected list in theorem significance report: {theorem_significance_path}")
    theorem_entries: list[JsonObj] = [cast(JsonObj, row) for row in theorem_entries_raw if isinstance(row, dict)]

    decls = load_decl_index(decls_path)
    forward_edges, _ = load_edges(edges_path)
    module_region, file_region = load_module_regions(module_graph_path, root)
    owner_entries = load_owner_index(owner_index_path)

    hole_counts: dict[str, int] = {}
    if proof_holes_path.exists():
        hole_counts = load_proof_hole_counts(proof_holes_path)

    decl_match_ctx = build_decl_match_context(theorem_entries, decls, root)

    bridge_json_paths = collect_bridge_json_paths(args.bridge_input, root)
    bridge_payload_count = 0
    observations: list[JsonObj] = []
    for p in bridge_json_paths:
        try:
            parsed = load_json(p)
        except Exception:
            continue
        payloads = extract_bridge_payload_objects(parsed)
        bridge_payload_count += len(payloads)
        for payload in payloads:
            observations.extend(observe_bridge_payload(payload, p, root, decl_match_ctx))

    normalization, bridge_file_signals, bridge_decl_signals = normalize_bridge_observations(observations)

    theorem_by_name = {
        str(row.get("name")): row for row in theorem_entries if isinstance(row, dict) and row.get("name")
    }

    vacuity_candidates = rank_vacuity_candidates(
        theorem_entries=theorem_entries,
        module_region=module_region,
        file_region=file_region,
        hole_counts=hole_counts,
        bridge_file_signals=bridge_file_signals,
        bridge_decl_signals=bridge_decl_signals,
        top_k=args.top_k,
    )

    owner_candidates = rank_owner_candidates(
        vacuity_candidates=vacuity_candidates,
        owner_entries=owner_entries,
        file_region=file_region,
        top_k=args.top_k,
    )

    replacement_candidates = rank_replacement_candidates(
        vacuity_candidates=vacuity_candidates,
        forward_edges=forward_edges,
        decls=decls,
        theorem_by_name=theorem_by_name,
        file_region=file_region,
        owner_candidates=owner_candidates,
        top_k=args.top_k,
    )

    fingerprint_corridors = rank_fingerprint_corridors(
        vacuity_candidates=vacuity_candidates,
        replacement_candidates=replacement_candidates,
        bridge_decl_signals=bridge_decl_signals,
        top_k=args.top_k,
    )

    declaration_plans = rank_declaration_plans(
        vacuity_candidates=vacuity_candidates,
        owner_candidates=owner_candidates,
        replacement_candidates=replacement_candidates,
        bridge_decl_signals=bridge_decl_signals,
        top_k=args.top_k,
    )

    report: JsonObj = {
        "schema": "ig.vacuity-planner.v0",
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "boundary": {
            "plannerMode": "planning-only",
            "mutationSurface": False,
            "automaticReplacement": False,
            "proofRepair": False,
        },
        "inputs": {
            "theoremSignificancePath": relpath_or_self(theorem_significance_path, root),
            "declsPath": relpath_or_self(decls_path, root),
            "edgesPath": relpath_or_self(edges_path, root),
            "moduleGraphPath": relpath_or_self(module_graph_path, root),
            "ownerIndexPath": relpath_or_self(owner_index_path, root),
            "proofHolesByFilePath": relpath_or_self(proof_holes_path, root) if proof_holes_path.exists() else None,
            "bridgeInputPaths": [relpath_or_self(p, root) for p in bridge_json_paths],
            "theoremSignificanceEntries": len(theorem_entries),
            "declarationCount": len(decls),
            "edgeCount": sum(len(v) for v in forward_edges.values()),
            "ownerEntries": len(owner_entries),
            "bridgePayloadFiles": len(bridge_json_paths),
            "bridgePayloadObjects": bridge_payload_count,
            "bridgeDeclarationSignalCount": len(bridge_decl_signals),
        },
        "normalization": normalization,
        "rankedVacuityCandidates": vacuity_candidates,
        "rankedOwnerCandidates": owner_candidates,
        "rankedReplacementCandidates": replacement_candidates,
        "rankedFingerprintCorridors": fingerprint_corridors,
        "rankedDeclarationPlans": declaration_plans,
        "confidenceWeights": {
            "headSource": HEAD_SOURCE_WEIGHT,
            "diagnosticProvenance": DIAG_PROVENANCE_WEIGHT,
            "violationLevel": VIOLATION_LEVEL_WEIGHT,
        },
    }

    out_json_path.parent.mkdir(parents=True, exist_ok=True)
    with out_json_path.open("w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)

    out_md_path.parent.mkdir(parents=True, exist_ok=True)
    with out_md_path.open("w", encoding="utf-8") as f:
        f.write(make_markdown_report(report))

    print(f"[vacuity-planner] JSON report -> {out_json_path}")
    print(f"[vacuity-planner] Markdown report -> {out_md_path}")
    print(
        "[vacuity-planner] summary: "
        f"vacuity={len(vacuity_candidates)}, "
        f"owners={len(owner_candidates)}, "
        f"replacements={len(replacement_candidates)}, "
        f"corridors={len(fingerprint_corridors)}, "
        f"declaration_plans={len(declaration_plans)}, "
        f"bridge_payloads={bridge_payload_count}"
    )


if __name__ == "__main__":
    main()
