#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


DEFAULT_DECLS = "artifacts/dag/index/decls.jsonl"
DEFAULT_EDGES = "artifacts/dag/index/edges.jsonl"
DEFAULT_TYPES = "artifacts/dag/index/types.jsonl"
DEFAULT_SURFACE_INDEX = "reports/dag/theorem-surface-index.json"
DEFAULT_FAILED_TRANSITIONS = "artifacts/leantrail/failed_transitions.jsonl"
DEFAULT_REP_DEPTH = "artifacts/dag/representation-depth-tags.json"
DEFAULT_OUT = "reports/training/link_ats_dataset.jsonl"
DEFAULT_STATS_OUT = "reports/training/link_ats_dataset.stats.json"


def _iter_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    if not path.exists():
        return
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except Exception:
                continue
            if isinstance(row, dict):
                yield row


def _stable_float_01(key: str, seed: int) -> float:
    digest = hashlib.sha1(f"{seed}|{key}".encode("utf-8")).hexdigest()
    n = int(digest[:15], 16)
    return n / float(16**15 - 1)


def _split_for(key: str, seed: int, train_ratio: float, val_ratio: float) -> str:
    x = _stable_float_01(key, seed)
    if x < train_ratio:
        return "train"
    if x < train_ratio + val_ratio:
        return "val"
    return "test"


def _normalize_kind(raw: str) -> str:
    s = raw.strip().lower()
    if s in {"type", "depends_type"}:
        return "type"
    if s in {"value", "depends_value"}:
        return "value"
    return "value"


def _module_family(module: str) -> str:
    parts = [p for p in module.split(".") if p]
    if len(parts) >= 3:
        return ".".join(parts[:3])
    return module


def _truncate(text: str, max_chars: int) -> str:
    if max_chars <= 0:
        return ""
    if max_chars <= 3:
        return "." * max_chars
    s = text.strip()
    if len(s) <= max_chars:
        return s
    return s[: max_chars - 3] + "..."


@dataclass(frozen=True)
class DeclMeta:
    name: str
    kind: str
    module: str
    module_family: str
    file: str
    line: int | None
    doc: str
    lean_snippet: str
    rep_depth: str | None
    rep_depth_nat: int | None


@dataclass(frozen=True)
class TypeMeta:
    category: str
    domain_key: str
    codomain_key: str
    type_str: str


@dataclass(frozen=True)
class FailurePair:
    src: str
    dst: str
    kind: str
    count: int
    total_cost: int
    error_kinds: tuple[str, ...]


@dataclass(frozen=True)
class PosEdge:
    src: str
    dst: str
    kind: str


def _load_surface_categories(path: Path) -> dict[str, str]:
    if not path.exists():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    rows = payload.get("rows")
    if not isinstance(rows, list):
        return {}
    out: dict[str, str] = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        name = str(row.get("name", "")).strip()
        cat = str(row.get("category", "")).strip()
        if name:
            out[name] = cat
    return out


def _load_decls(
    path: Path,
    *,
    include_kinds: set[str],
    excluded_surface_categories: set[str],
    surface_category_by_decl: dict[str, str],
    rep_depth_by_decl: dict[str, tuple[str | None, int | None]],
    max_doc_chars: int,
    snippet_radius: int,
    max_snippet_chars: int,
) -> dict[str, DeclMeta]:
    file_cache: dict[str, list[str]] = {}

    def line_snippet(file_path: str, line: int | None) -> str:
        if line is None:
            return ""
        p = Path(file_path)
        if not p.exists():
            return ""
        key = str(p)
        lines = file_cache.get(key)
        if lines is None:
            try:
                lines = p.read_text(encoding="utf-8", errors="ignore").splitlines()
            except Exception:
                lines = []
            file_cache[key] = lines
        if not lines:
            return ""
        idx = max(0, int(line) - 1)
        start = max(0, idx - max(0, snippet_radius))
        stop = min(len(lines), idx + max(0, snippet_radius) + 1)
        snippet = "\n".join(lines[start:stop]).strip()
        if not snippet:
            return ""
        if max_snippet_chars > 0 and len(snippet) > max_snippet_chars:
            snippet = snippet[: max_snippet_chars - 3] + "..."
        return snippet

    out: dict[str, DeclMeta] = {}
    for row in _iter_jsonl(path):
        name = str(row.get("name", "")).strip()
        kind = str(row.get("kind", "")).strip()
        module = str(row.get("module", "")).strip()
        if not name or not kind or not module:
            continue
        if kind not in include_kinds:
            continue
        if surface_category_by_decl.get(name, "") in excluded_surface_categories:
            continue
        line_raw = row.get("line")
        out[name] = DeclMeta(
            name=name,
            kind=kind,
            module=module,
            module_family=_module_family(module),
            file=str(row.get("file", "")).strip(),
            line=int(line_raw) if isinstance(line_raw, int) else None,
            doc=_truncate(str(row.get("doc", "") or ""), max_chars=max_doc_chars),
            lean_snippet=line_snippet(str(row.get("file", "")).strip(), int(line_raw) if isinstance(line_raw, int) else None),
            rep_depth=rep_depth_by_decl.get(name, (None, None))[0],
            rep_depth_nat=rep_depth_by_decl.get(name, (None, None))[1],
        )
    return out


def _load_rep_depth(path: Path) -> dict[str, tuple[str | None, int | None]]:
    if not path.exists():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    decls_any = payload.get("declarations")
    if not isinstance(decls_any, list):
        return {}
    out: dict[str, tuple[str | None, int | None]] = {}
    for row in decls_any:
        if not isinstance(row, dict):
            continue
        name = str(row.get("name", "")).strip()
        if not name:
            continue
        depth_label = str(row.get("depth", "")).strip() or None
        depth_nat_raw = row.get("depthNat")
        depth_nat = int(depth_nat_raw) if isinstance(depth_nat_raw, int) else None
        out[name] = (depth_label, depth_nat)
    return out


def _load_types(path: Path, *, max_type_chars: int) -> dict[str, TypeMeta]:
    out: dict[str, TypeMeta] = {}
    if not path.exists():
        return out
    for row in _iter_jsonl(path):
        name = str(row.get("declName", "")).strip()
        if not name or name in out:
            continue
        out[name] = TypeMeta(
            category=str(row.get("category", "")).strip(),
            domain_key=_truncate(str(row.get("domainKey", "") or ""), max_chars=max_type_chars),
            codomain_key=_truncate(str(row.get("codomainKey", "") or ""), max_chars=max_type_chars),
            type_str=_truncate(str(row.get("typeStr", "") or ""), max_chars=max_type_chars),
        )
    return out


def _load_positive_edges(path: Path, decls: dict[str, DeclMeta]) -> list[PosEdge]:
    dedup: set[tuple[str, str, str]] = set()
    out: list[PosEdge] = []
    for row in _iter_jsonl(path):
        src = str(row.get("src", "")).strip()
        dst = str(row.get("dst", "")).strip()
        if src not in decls or dst not in decls:
            continue
        kind = _normalize_kind(str(row.get("kind", "")))
        key = (src, dst, kind)
        if key in dedup:
            continue
        dedup.add(key)
        out.append(PosEdge(src=src, dst=dst, kind=kind))
    return out


def _load_failures(path: Path, decls: dict[str, DeclMeta]) -> tuple[list[FailurePair], Counter[str], Counter[str], dict[tuple[str, str], Counter[str]]]:
    pair_kind_count: dict[tuple[str, str, str], int] = defaultdict(int)
    pair_kind_cost: dict[tuple[str, str, str], int] = defaultdict(int)
    pair_kind_errors: dict[tuple[str, str, str], Counter[str]] = defaultdict(Counter)
    node_pressure: Counter[str] = Counter()
    pair_pressure: Counter[str] = Counter()
    pair_error_kinds: dict[tuple[str, str], Counter[str]] = defaultdict(Counter)

    if not path.exists():
        return [], node_pressure, pair_pressure, pair_error_kinds

    for row in _iter_jsonl(path):
        src = str(row.get("src", "")).strip()
        dst = str(row.get("dst", "")).strip()
        if src not in decls or dst not in decls:
            continue
        kind = _normalize_kind(str(row.get("kind", "")))
        error_kind = str(row.get("error_kind", "")).strip() or "unknown"
        count_raw = row.get("count")
        cost_raw = row.get("total_cost")
        count = int(count_raw) if isinstance(count_raw, int) and count_raw > 0 else 1
        cost = int(cost_raw) if isinstance(cost_raw, int) and cost_raw >= 0 else 0

        key = (src, dst, kind)
        pair_kind_count[key] += count
        pair_kind_cost[key] += cost
        pair_kind_errors[key][error_kind] += count

        node_pressure[src] += count
        node_pressure[dst] += count
        pair_key = f"{src}|{dst}"
        pair_pressure[pair_key] += count
        pair_error_kinds[(src, dst)][error_kind] += count

    out: list[FailurePair] = []
    for (src, dst, kind), count in pair_kind_count.items():
        err_counter = pair_kind_errors[(src, dst, kind)]
        out.append(
            FailurePair(
                src=src,
                dst=dst,
                kind=kind,
                count=count,
                total_cost=pair_kind_cost[(src, dst, kind)],
                error_kinds=tuple(sorted(err_counter.keys())),
            )
        )
    out.sort(key=lambda x: (-(x.total_cost + x.count), x.src, x.dst, x.kind))
    return out, node_pressure, pair_pressure, pair_error_kinds


def _build_non_edges(
    *,
    decls: dict[str, DeclMeta],
    positives: list[PosEdge],
) -> tuple[dict[str, set[str]], dict[str, list[str]], list[str]]:
    pos_by_src: dict[str, set[str]] = defaultdict(set)
    for e in positives:
        pos_by_src[e.src].add(e.dst)

    by_family: dict[str, list[str]] = defaultdict(list)
    all_names = sorted(decls.keys())
    for name, meta in decls.items():
        by_family[meta.module_family].append(name)
    for family in by_family:
        by_family[family].sort()
    return pos_by_src, by_family, all_names


def _sample_random_negative_dst(
    *,
    src: str,
    decls: dict[str, DeclMeta],
    pos_by_src: dict[str, set[str]],
    by_family: dict[str, list[str]],
    all_names: list[str],
    rng: random.Random,
) -> str | None:
    src_meta = decls[src]
    blocked = pos_by_src.get(src, set())

    family_pool = [name for name in by_family.get(src_meta.module_family, []) if name != src and name not in blocked]
    if family_pool and rng.random() < 0.65:
        return family_pool[rng.randrange(len(family_pool))]

    for _ in range(30):
        if not all_names:
            break
        cand = all_names[rng.randrange(len(all_names))]
        if cand != src and cand not in blocked:
            return cand
    return None


def _pair_key(src: str, dst: str, kind: str, label: int) -> str:
    return f"{src}|{dst}|{kind}|{label}"


def _compute_unusual_score(
    *,
    src: str,
    dst: str,
    kind: str,
    decls: dict[str, DeclMeta],
    in_degree: Counter[str],
    node_failure_pressure: Counter[str],
    max_node_failure_pressure: int,
) -> float:
    dst_in = float(in_degree.get(dst, 0))
    rarity = 1.0 / (1.0 + math.log2(2.0 + dst_in))
    cross_module = 1.0 if decls[src].module != decls[dst].module else 0.0
    cross_family = 1.0 if decls[src].module_family != decls[dst].module_family else 0.0
    depth_gap_score = 0.0
    src_depth = decls[src].rep_depth_nat
    dst_depth = decls[dst].rep_depth_nat
    if src_depth is not None and dst_depth is not None:
        depth_gap_score = min(1.0, abs(float(src_depth - dst_depth)) / 4.0)
    kind_bonus = 1.0 if kind == "type" else 0.0

    src_pressure = float(node_failure_pressure.get(src, 0))
    dst_pressure = float(node_failure_pressure.get(dst, 0))
    pressure = 0.0
    if max_node_failure_pressure > 0:
        pressure = min(1.0, (src_pressure + dst_pressure) / (2.0 * float(max_node_failure_pressure)))

    score = (
        0.38 * rarity
        + 0.22 * cross_module
        + 0.18 * cross_family
        + 0.12 * depth_gap_score
        + 0.10 * kind_bonus
        + 0.10 * pressure
    )
    return max(0.0, min(1.0, score))


def _decl_payload(meta: DeclMeta, type_meta: TypeMeta | None) -> dict[str, Any]:
    out = {
        "name": meta.name,
        "kind": meta.kind,
        "module": meta.module,
        "module_family": meta.module_family,
        "file": meta.file,
        "line": meta.line,
        "doc": meta.doc,
        "lean_snippet": meta.lean_snippet,
        "rep_depth": meta.rep_depth,
        "rep_depth_nat": meta.rep_depth_nat,
    }
    if type_meta is not None:
        out["type"] = {
            "category": type_meta.category,
            "domain_key": type_meta.domain_key,
            "codomain_key": type_meta.codomain_key,
            "type_str": type_meta.type_str,
        }
    return out


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Build a local ATS-style link-prediction dataset for Lean declarations "
            "from verified DAG artifacts and failure memory."
        )
    )
    ap.add_argument("--decls", default=DEFAULT_DECLS)
    ap.add_argument("--edges", default=DEFAULT_EDGES)
    ap.add_argument("--types", default=DEFAULT_TYPES)
    ap.add_argument("--surface-index", default=DEFAULT_SURFACE_INDEX)
    ap.add_argument("--failed-transitions", default=DEFAULT_FAILED_TRANSITIONS)
    ap.add_argument("--rep-depth-tags", default=DEFAULT_REP_DEPTH)
    ap.add_argument("--out", default=DEFAULT_OUT)
    ap.add_argument("--stats-out", default=DEFAULT_STATS_OUT)
    ap.add_argument(
        "--include-kinds",
        default="theorem,axiom",
        help="Comma-separated declaration kinds from decls.jsonl.",
    )
    ap.add_argument(
        "--exclude-surface-categories",
        default="surrogate_or_vacuous,package_reprojection",
        help="Comma-separated categories from theorem-surface-index to exclude.",
    )
    ap.add_argument("--max-doc-chars", type=int, default=240)
    ap.add_argument("--snippet-radius", type=int, default=2)
    ap.add_argument("--max-snippet-chars", type=int, default=360)
    ap.add_argument("--max-type-chars", type=int, default=320)
    ap.add_argument("--max-positives", type=int, default=0, help="0 means all positives.")
    ap.add_argument(
        "--hard-negative-ratio",
        type=float,
        default=0.8,
        help="Target hard-negative count relative to positives.",
    )
    ap.add_argument(
        "--random-negative-ratio",
        type=float,
        default=0.7,
        help="Target random-negative count relative to positives.",
    )
    ap.add_argument("--seed", type=int, default=20260418)
    ap.add_argument("--train-ratio", type=float, default=0.9)
    ap.add_argument("--val-ratio", type=float, default=0.05)
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    rng = random.Random(args.seed)

    decls_path = Path(args.decls).resolve()
    edges_path = Path(args.edges).resolve()
    types_path = Path(args.types).resolve()
    surface_path = Path(args.surface_index).resolve()
    failures_path = Path(args.failed_transitions).resolve()
    rep_depth_path = Path(args.rep_depth_tags).resolve()
    out_path = Path(args.out).resolve()
    stats_path = Path(args.stats_out).resolve()

    include_kinds = {x.strip() for x in args.include_kinds.split(",") if x.strip()}
    excluded_surface_categories = {
        x.strip() for x in args.exclude_surface_categories.split(",") if x.strip()
    }

    if not decls_path.exists():
        raise FileNotFoundError(f"decls index missing: {decls_path}")
    if not edges_path.exists():
        raise FileNotFoundError(f"edges index missing: {edges_path}")
    if args.train_ratio <= 0 or args.val_ratio < 0 or args.train_ratio + args.val_ratio >= 1:
        raise ValueError("invalid split ratios: require 0 < train, 0 <= val, train + val < 1")

    surface_category_by_decl = _load_surface_categories(surface_path)
    rep_depth_by_decl = _load_rep_depth(rep_depth_path)
    decls = _load_decls(
        decls_path,
        include_kinds=include_kinds,
        excluded_surface_categories=excluded_surface_categories,
        surface_category_by_decl=surface_category_by_decl,
        rep_depth_by_decl=rep_depth_by_decl,
        max_doc_chars=args.max_doc_chars,
        snippet_radius=max(0, args.snippet_radius),
        max_snippet_chars=max(0, args.max_snippet_chars),
    )
    if not decls:
        raise RuntimeError("no declarations after filters; check include-kinds/surface filters")

    type_by_decl = _load_types(types_path, max_type_chars=args.max_type_chars)
    positives = _load_positive_edges(edges_path, decls)
    if not positives:
        raise RuntimeError("no positive edges after declaration filtering")

    if args.max_positives > 0 and len(positives) > args.max_positives:
        rng.shuffle(positives)
        positives = positives[: args.max_positives]

    failures, node_failure_pressure, pair_failure_pressure, pair_error_kinds = _load_failures(
        failures_path, decls
    )
    positive_pairs = {(e.src, e.dst, e.kind) for e in positives}
    in_degree: Counter[str] = Counter()
    out_degree: Counter[str] = Counter()
    for e in positives:
        in_degree[e.dst] += 1
        out_degree[e.src] += 1

    max_node_failure_pressure = max(node_failure_pressure.values(), default=0)

    pos_by_src, by_family, all_names = _build_non_edges(decls=decls, positives=positives)

    hard_negative_target = int(round(float(len(positives)) * max(0.0, args.hard_negative_ratio)))
    random_negative_target = int(round(float(len(positives)) * max(0.0, args.random_negative_ratio)))

    hard_negatives: list[FailurePair] = []
    for fp in failures:
        if (fp.src, fp.dst, fp.kind) in positive_pairs:
            continue
        hard_negatives.append(fp)
        if len(hard_negatives) >= hard_negative_target:
            break

    rows: list[dict[str, Any]] = []
    sample_kind_counts: Counter[str] = Counter()
    split_counts: Counter[str] = Counter()
    label_counts: Counter[str] = Counter()

    def push_row(row: dict[str, Any]) -> None:
        rows.append(row)
        sample_kind_counts[row["sample_kind"]] += 1
        split_counts[row["split"]] += 1
        label_counts[str(row["label"])] += 1

    for e in positives:
        unusual = _compute_unusual_score(
            src=e.src,
            dst=e.dst,
            kind=e.kind,
            decls=decls,
            in_degree=in_degree,
            node_failure_pressure=node_failure_pressure,
            max_node_failure_pressure=max_node_failure_pressure,
        )
        weight = 1.0 + 2.0 * unusual
        key = _pair_key(e.src, e.dst, e.kind, 1)
        split = _split_for(key, args.seed, args.train_ratio, args.val_ratio)
        push_row(
            {
                "id": f"ats_{hashlib.sha1(key.encode('utf-8')).hexdigest()[:24]}",
                "split": split,
                "label": 1,
                "sample_kind": "positive",
                "link_kind": e.kind,
                "weight": round(weight, 4),
                "unusual_score": round(unusual, 4),
                "source": _decl_payload(decls[e.src], type_by_decl.get(e.src)),
                "target": _decl_payload(decls[e.dst], type_by_decl.get(e.dst)),
                "graph_context": {
                    "source_out_degree": int(out_degree.get(e.src, 0)),
                    "target_in_degree": int(in_degree.get(e.dst, 0)),
                    "same_module": decls[e.src].module == decls[e.dst].module,
                    "same_module_family": decls[e.src].module_family == decls[e.dst].module_family,
                },
                "failure_context": {
                    "source_failure_pressure": int(node_failure_pressure.get(e.src, 0)),
                    "target_failure_pressure": int(node_failure_pressure.get(e.dst, 0)),
                    "pair_failure_count": int(pair_failure_pressure.get(f"{e.src}|{e.dst}", 0)),
                    "pair_error_kinds": sorted(pair_error_kinds.get((e.src, e.dst), {}).keys()),
                },
            }
        )

    for fp in hard_negatives:
        hardness = min(1.0, 0.35 + math.log1p(float(fp.total_cost + fp.count)) / 5.0)
        weight = 1.0 + hardness
        key = _pair_key(fp.src, fp.dst, fp.kind, 0)
        split = _split_for(key, args.seed, args.train_ratio, args.val_ratio)
        push_row(
            {
                "id": f"ats_{hashlib.sha1(key.encode('utf-8')).hexdigest()[:24]}",
                "split": split,
                "label": 0,
                "sample_kind": "hard_negative",
                "link_kind": fp.kind,
                "weight": round(weight, 4),
                "unusual_score": 0.0,
                "source": _decl_payload(decls[fp.src], type_by_decl.get(fp.src)),
                "target": _decl_payload(decls[fp.dst], type_by_decl.get(fp.dst)),
                "graph_context": {
                    "source_out_degree": int(out_degree.get(fp.src, 0)),
                    "target_in_degree": int(in_degree.get(fp.dst, 0)),
                    "same_module": decls[fp.src].module == decls[fp.dst].module,
                    "same_module_family": decls[fp.src].module_family == decls[fp.dst].module_family,
                },
                "failure_context": {
                    "source_failure_pressure": int(node_failure_pressure.get(fp.src, 0)),
                    "target_failure_pressure": int(node_failure_pressure.get(fp.dst, 0)),
                    "pair_failure_count": int(pair_failure_pressure.get(f"{fp.src}|{fp.dst}", 0)),
                    "pair_error_kinds": list(fp.error_kinds),
                    "failure_count": fp.count,
                    "failure_total_cost": fp.total_cost,
                },
                "hardness": round(hardness, 4),
            }
        )

    used_negative_pairs = {(fp.src, fp.dst) for fp in hard_negatives}
    random_negative_rows = 0
    for _ in range(max(0, random_negative_target * 3)):
        if random_negative_rows >= random_negative_target:
            break
        src = positives[rng.randrange(len(positives))].src
        dst = _sample_random_negative_dst(
            src=src,
            decls=decls,
            pos_by_src=pos_by_src,
            by_family=by_family,
            all_names=all_names,
            rng=rng,
        )
        if dst is None:
            continue
        if (src, dst) in used_negative_pairs:
            continue
        used_negative_pairs.add((src, dst))
        same_family = decls[src].module_family == decls[dst].module_family
        hardness = 0.55 if same_family else 0.25
        weight = 1.0 + hardness
        kind = "value"
        key = _pair_key(src, dst, kind, 0)
        split = _split_for(key, args.seed, args.train_ratio, args.val_ratio)
        push_row(
            {
                "id": f"ats_{hashlib.sha1(key.encode('utf-8')).hexdigest()[:24]}",
                "split": split,
                "label": 0,
                "sample_kind": "random_negative",
                "link_kind": kind,
                "weight": round(weight, 4),
                "unusual_score": 0.0,
                "source": _decl_payload(decls[src], type_by_decl.get(src)),
                "target": _decl_payload(decls[dst], type_by_decl.get(dst)),
                "graph_context": {
                    "source_out_degree": int(out_degree.get(src, 0)),
                    "target_in_degree": int(in_degree.get(dst, 0)),
                    "same_module": decls[src].module == decls[dst].module,
                    "same_module_family": same_family,
                },
                "failure_context": {
                    "source_failure_pressure": int(node_failure_pressure.get(src, 0)),
                    "target_failure_pressure": int(node_failure_pressure.get(dst, 0)),
                    "pair_failure_count": int(pair_failure_pressure.get(f"{src}|{dst}", 0)),
                    "pair_error_kinds": sorted(pair_error_kinds.get((src, dst), {}).keys()),
                },
                "hardness": round(hardness, 4),
            }
        )
        random_negative_rows += 1

    rows.sort(key=lambda row: row["id"])
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True) + "\n")

    stats = {
        "inputs": {
            "decls": str(decls_path),
            "edges": str(edges_path),
            "types": str(types_path) if types_path.exists() else None,
            "surface_index": str(surface_path) if surface_path.exists() else None,
            "failed_transitions": str(failures_path) if failures_path.exists() else None,
            "rep_depth_tags": str(rep_depth_path) if rep_depth_path.exists() else None,
        },
        "filters": {
            "include_kinds": sorted(include_kinds),
            "excluded_surface_categories": sorted(excluded_surface_categories),
        },
        "counts": {
            "decls_kept": len(decls),
            "positive_edges_used": len(positives),
            "hard_negatives_used": len(hard_negatives),
            "random_negatives_used": random_negative_rows,
            "rows_written": len(rows),
        },
        "distribution": {
            "by_sample_kind": dict(sample_kind_counts),
            "by_split": dict(split_counts),
            "by_label": dict(label_counts),
        },
        "params": {
            "seed": args.seed,
            "train_ratio": args.train_ratio,
            "val_ratio": args.val_ratio,
            "hard_negative_ratio": args.hard_negative_ratio,
            "random_negative_ratio": args.random_negative_ratio,
            "max_positives": args.max_positives,
            "snippet_radius": args.snippet_radius,
            "max_snippet_chars": args.max_snippet_chars,
        },
    }
    stats_path.parent.mkdir(parents=True, exist_ok=True)
    stats_path.write_text(json.dumps(stats, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")

    print(f"wrote dataset: {out_path}")
    print(f"wrote stats:   {stats_path}")
    print(f"rows: {len(rows)} (pos={len(positives)}, hard_neg={len(hard_negatives)}, rand_neg={random_negative_rows})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
