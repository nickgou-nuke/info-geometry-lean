"""Planner matching context and declaration resolution logic."""

from __future__ import annotations

from bisect import bisect_left
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable, cast

from .common import (
    DECL_LOCATION_FILE_KEYS,
    DECL_LOCATION_LINE_KEYS,
    DECL_LOCATION_MODULE_KEYS,
    DECL_LOCATION_RANGE_MAX_DELTA,
    DECL_MATCH_CONTEXT_KINDS,
    DECL_MATCH_RELIABILITY,
    DECL_NAME_CONTAINERS,
    DECL_NAME_EXACT_KEYS,
    DECL_NAME_KEYS,
    JsonObj,
    clamp01,
    coerce_int,
    dedup_preserve_order,
    is_valid_decl_name,
    make_cluster_key,
    normalize_expr_record,
    parse_uri_or_path,
)


def _iter_decl_container_nodes(payload: JsonObj) -> Iterable[JsonObj]:
    """Yield top-level payload plus explicitly allowed request/meta container dicts."""
    yield payload

    seen: set[int] = {id(payload)}
    queue: list[Any] = []
    for key in DECL_NAME_CONTAINERS:
        child = payload.get(key)
        if isinstance(child, (dict, list)):
            queue.append(child)

    while queue:
        node = queue.pop(0)
        node_id = id(node)
        if node_id in seen:
            continue
        seen.add(node_id)

        if isinstance(node, dict):
            node_dict = cast(JsonObj, node)
            yield node_dict
            for key in DECL_NAME_CONTAINERS:
                child = node_dict.get(key)
                if isinstance(child, (dict, list)):
                    queue.append(child)
        elif isinstance(node, list):
            for item in cast(list[Any], node):
                if isinstance(item, dict) and id(item) not in seen:
                    queue.append(item)


def _find_decl_context_value(payload: JsonObj, keys: Iterable[str]) -> Any:
    for key in keys:
        if key in payload:
            return payload.get(key)

    for node in _iter_decl_container_nodes(payload):
        for key in keys:
            if key in node:
                return node.get(key)
    return None


def extract_decl_field(payload: JsonObj) -> tuple[str | None, str]:
    for key in DECL_NAME_KEYS:
        value = _find_decl_context_value(payload, (key,))
        if is_valid_decl_name(value):
            decl = str(value).strip()
            if key in DECL_NAME_EXACT_KEYS:
                return decl, "exactDecl"
            return decl, "requestField"
    return None, "unmatched"


def extract_location_hints(
    payload: JsonObj,
    *,
    source_file: str | None,
    root: Path,
) -> tuple[str | None, str | None, int | None]:
    file_hint: str | None = None
    for key in DECL_LOCATION_FILE_KEYS:
        raw = _find_decl_context_value(payload, (key,))
        if isinstance(raw, str) and raw:
            parsed = parse_uri_or_path(raw, root)
            if parsed:
                file_hint = parsed
                break
    if not file_hint:
        file_hint = source_file

    module_hint: str | None = None
    for key in DECL_LOCATION_MODULE_KEYS:
        raw = _find_decl_context_value(payload, (key,))
        if isinstance(raw, str) and raw:
            module_hint = raw.strip()
            break

    line_hint: int | None = None
    for key in DECL_LOCATION_LINE_KEYS:
        raw = _find_decl_context_value(payload, (key,))
        parsed = coerce_int(raw)
        if parsed is not None:
            line_hint = parsed
            break
    if line_hint is None:
        position_any = _find_decl_context_value(payload, ("position",))
        if isinstance(position_any, dict):
            line_hint = coerce_int(cast(JsonObj, position_any).get("line"))

    return file_hint, module_hint, line_hint


def _new_decl_match_context() -> dict[str, Any]:
    decl_names: set[str] = set()
    decl_meta: dict[str, JsonObj] = {}
    by_file_module_line: dict[tuple[str, str, int], list[str]] = defaultdict(list)
    by_file_line: dict[tuple[str, int], list[str]] = defaultdict(list)
    by_file_module: dict[tuple[str, str], list[str]] = defaultdict(list)
    by_file_module_ordered: dict[tuple[str, str], list[tuple[int, str]]] = defaultdict(list)
    by_file_ordered: dict[str, list[tuple[int, str]]] = defaultdict(list)
    cluster_to_decl: dict[str, Counter[str]] = defaultdict(Counter)
    return {
        "theoremNames": decl_names,
        "declNames": decl_names,
        "theoremMeta": decl_meta,
        "byFileModuleLine": by_file_module_line,
        "byFileLine": by_file_line,
        "byFileModule": by_file_module,
        "byFileModuleOrdered": by_file_module_ordered,
        "byFileOrdered": by_file_ordered,
        "clusterToDecl": cluster_to_decl,
    }


def _index_decl_match_context_entry(
    match_ctx: dict[str, Any],
    *,
    name: str,
    file_rel: str | None,
    module: str | None,
    line: int | None,
) -> None:
    decl_names = cast(set[str], match_ctx.get("declNames", set()))
    decl_meta = cast(dict[str, JsonObj], match_ctx.get("theoremMeta", {}))
    by_file_module_line = cast(dict[tuple[str, str, int], list[str]], match_ctx.get("byFileModuleLine", {}))
    by_file_line = cast(dict[tuple[str, int], list[str]], match_ctx.get("byFileLine", {}))
    by_file_module = cast(dict[tuple[str, str], list[str]], match_ctx.get("byFileModule", {}))
    by_file_module_ordered = cast(
        dict[tuple[str, str], list[tuple[int, str]]],
        match_ctx.get("byFileModuleOrdered", {}),
    )
    by_file_ordered = cast(dict[str, list[tuple[int, str]]], match_ctx.get("byFileOrdered", {}))

    decl_names.add(name)
    decl_meta[name] = {"file": file_rel, "module": module, "line": line}

    if isinstance(file_rel, str) and isinstance(module, str):
        by_file_module[(file_rel, module)].append(name)
        if isinstance(line, int) and line >= 0:
            by_file_module_line[(file_rel, module, line)].append(name)
            by_file_module_ordered[(file_rel, module)].append((line, name))
    if isinstance(file_rel, str) and isinstance(line, int) and line >= 0:
        by_file_line[(file_rel, line)].append(name)
        by_file_ordered[file_rel].append((line, name))


def _finalize_decl_match_context(match_ctx: dict[str, Any]) -> None:
    by_file_module_ordered = cast(
        dict[tuple[str, str], list[tuple[int, str]]],
        match_ctx.get("byFileModuleOrdered", {}),
    )
    by_file_ordered = cast(dict[str, list[tuple[int, str]]], match_ctx.get("byFileOrdered", {}))

    for ordered in by_file_module_ordered.values():
        ordered.sort(key=lambda item: (item[0], item[1]))
    for ordered in by_file_ordered.values():
        ordered.sort(key=lambda item: (item[0], item[1]))


def build_decl_match_context_from_decls(
    decls: dict[str, JsonObj],
    root: Path,
) -> dict[str, Any]:
    match_ctx = _new_decl_match_context()

    for decl_key, row in decls.items():
        if not isinstance(row, dict):
            continue
        kind_any = row.get("kind")
        kind = kind_any.strip() if isinstance(kind_any, str) else None
        if not kind or kind not in DECL_MATCH_CONTEXT_KINDS:
            continue

        name_any = row.get("name")
        if isinstance(name_any, str) and name_any:
            name = name_any
        elif isinstance(decl_key, str) and decl_key:
            name = decl_key
        else:
            continue
        if not is_valid_decl_name(name):
            continue

        file_any = row.get("file")
        file_rel = parse_uri_or_path(file_any, root) if isinstance(file_any, str) else None
        module_any = row.get("module")
        module = module_any.strip() if isinstance(module_any, str) and module_any.strip() else None
        line = coerce_int(row.get("line"))

        _index_decl_match_context_entry(
            match_ctx,
            name=name,
            file_rel=file_rel,
            module=module,
            line=line,
        )

    _finalize_decl_match_context(match_ctx)
    return match_ctx


def build_decl_match_context(
    theorem_entries: list[JsonObj],
    decls: dict[str, JsonObj],
    root: Path,
) -> dict[str, Any]:
    match_ctx = build_decl_match_context_from_decls(decls, root)
    indexed_names = cast(set[str], match_ctx.get("declNames", set()))

    for row in theorem_entries:
        if row.get("kind") != "theorem":
            continue
        name_any = row.get("name")
        if not isinstance(name_any, str) or not name_any:
            continue
        name = name_any
        if name in indexed_names:
            continue

        file_any = row.get("file")
        file_rel = parse_uri_or_path(file_any, root) if isinstance(file_any, str) else None
        module_any = row.get("module")
        module = module_any.strip() if isinstance(module_any, str) and module_any.strip() else None
        line = coerce_int(row.get("line"))

        decl_row = decls.get(name)
        if isinstance(decl_row, dict):
            if line is None:
                line = coerce_int(decl_row.get("line"))
            if not file_rel:
                decl_file_any = decl_row.get("file")
                if isinstance(decl_file_any, str):
                    file_rel = parse_uri_or_path(decl_file_any, root)
            if not module:
                decl_module_any = decl_row.get("module")
                if isinstance(decl_module_any, str) and decl_module_any.strip():
                    module = decl_module_any.strip()

        _index_decl_match_context_entry(
            match_ctx,
            name=name,
            file_rel=file_rel,
            module=module,
            line=line,
        )

    _finalize_decl_match_context(match_ctx)
    return match_ctx


def _unique_decl(candidates: Iterable[str]) -> str | None:
    uniq = dedup_preserve_order(candidates)
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

    best: tuple[int, int, str] | None = None

    for probe_line in _line_candidates(line_hint):
        pos = bisect_left(lines, probe_line)
        candidate_lines: list[int] = []
        if pos > 0:
            candidate_lines.append(lines[pos - 1])
        if pos < len(lines):
            candidate_lines.append(lines[pos])

        seen_candidate_lines: set[int] = set()
        for resolved_line in candidate_lines:
            if resolved_line in seen_candidate_lines:
                continue
            seen_candidate_lines.add(resolved_line)

            names = sorted(by_line.get(resolved_line, set()))
            if len(names) != 1:
                continue

            dist = abs(resolved_line - probe_line)
            candidate = (dist, resolved_line, names[0])
            if best is None or candidate < best:
                best = candidate

    if best is None:
        return None

    best_dist, _, best_decl = best
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

    return dedup_preserve_order(out)


def _resolve_decl_by_fingerprint(
    payload: JsonObj,
    *,
    file_hint: str | None,
    module_hint: str | None,
    match_ctx: dict[str, Any],
) -> str | None:
    cluster_to_decl = cast(dict[str, Counter[str]], match_ctx.get("clusterToDecl", {}))
    decl_meta = cast(dict[str, JsonObj], match_ctx.get("theoremMeta", {}))
    if not cluster_to_decl:
        return None

    aggregate: Counter[str] = Counter()
    for cluster in _payload_cluster_keys(payload):
        counts = cluster_to_decl.get(cluster)
        if not counts:
            continue
        for decl_name, count in counts.items():
            meta = decl_meta.get(decl_name, {})
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
    decl_names = cast(set[str], match_ctx.get("declNames", match_ctx.get("theoremNames", set())))

    explicit_decl, explicit_prov = extract_decl_field(payload)
    if isinstance(explicit_decl, str) and explicit_decl:
        if not decl_names or explicit_decl in decl_names:
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
    cluster_to_decl_any = match_ctx.get("clusterToDecl")
    if not isinstance(cluster_to_decl_any, dict):
        return
    cluster_to_decl = cast(dict[str, Counter[str]], cluster_to_decl_any)
    for obs in observations:
        decl_any = obs.get("declName")
        if not isinstance(decl_any, str) or not decl_any:
            continue
        prov_any = obs.get("declMatchProvenance")
        prov = prov_any if isinstance(prov_any, str) else "unmatched"
        if prov not in {"exactDecl", "requestField", "locationFallback"}:
            continue

        rel_any = obs.get("declMatchReliability")
        if isinstance(rel_any, (int, float)):
            rel = clamp01(float(rel_any))
        else:
            rel = DECL_MATCH_RELIABILITY.get(prov, DECL_MATCH_RELIABILITY["unmatched"])

        if prov == "locationFallback" and rel < DECL_MATCH_RELIABILITY["locationFallback"]:
            continue

        cluster_key = make_cluster_key(
            fingerprint_v1=obs.get("fingerprintV1") if isinstance(obs.get("fingerprintV1"), str) else None,
            semantic_head=obs.get("semanticHead") if isinstance(obs.get("semanticHead"), str) else None,
            expr_kind=obs.get("exprKind") if isinstance(obs.get("exprKind"), str) else None,
            arity_shape_value=obs.get("arityShape") if isinstance(obs.get("arityShape"), str) else None,
            binder_shape_value=obs.get("binderShape") if isinstance(obs.get("binderShape"), str) else None,
        )
        cluster_to_decl[cluster_key][decl_any] += 1
