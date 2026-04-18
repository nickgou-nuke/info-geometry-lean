#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import math
import re
from dataclasses import dataclass
from typing import Any


_NON_ALNUM_RE = re.compile(r"[^A-Za-z0-9_]+")
_CAMEL_SPLIT_RE = re.compile(r"([a-z0-9])([A-Z])")
_INT_RE = re.compile(r"\d+")


@dataclass(frozen=True)
class FeaturizerConfig:
    dim: int
    hash_seed: int
    text_token_limit: int = 32


def _hash_to_index_and_sign(feature: str, cfg: FeaturizerConfig) -> tuple[int, float]:
    digest = hashlib.sha1(f"{cfg.hash_seed}|{feature}".encode("utf-8")).digest()
    h = int.from_bytes(digest[:8], "big", signed=False)
    idx = h % cfg.dim
    sign = -1.0 if ((h >> 63) & 1) else 1.0
    return idx, sign


def _safe_text(value: Any) -> str:
    if value is None:
        return ""
    return str(value).strip()


def _safe_float(value: Any, default: float = 0.0) -> float:
    if isinstance(value, (int, float)):
        return float(value)
    try:
        return float(str(value).strip())
    except Exception:
        return default


def _safe_bool(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return bool(value)
    s = str(value).strip().lower()
    return s in {"1", "true", "yes", "y", "t"}


def _normalize_identifier_token(token: str) -> str:
    token = token.strip()
    if not token:
        return ""
    token = _CAMEL_SPLIT_RE.sub(r"\1 \2", token)
    token = _INT_RE.sub("#", token)
    token = token.lower()
    return token


def _tokenize_identifier(text: str) -> list[str]:
    if not text:
        return []
    chunks = _NON_ALNUM_RE.sub(" ", text).replace("_", " ").split()
    out: list[str] = []
    for chunk in chunks:
        split_chunk = _normalize_identifier_token(chunk)
        if not split_chunk:
            continue
        for tok in split_chunk.split():
            if len(tok) < 2:
                continue
            out.append(tok)
    return out


def _add_feature(acc: dict[int, float], feature: str, value: float, cfg: FeaturizerConfig) -> None:
    if not feature:
        return
    if value == 0.0:
        return
    idx, sign = _hash_to_index_and_sign(feature, cfg)
    acc[idx] = acc.get(idx, 0.0) + (sign * value)


def _add_cat(acc: dict[int, float], key: str, val: str, cfg: FeaturizerConfig) -> None:
    s = val.strip()
    if not s:
        return
    _add_feature(acc, f"{key}={s}", 1.0, cfg)


def _add_bool(acc: dict[int, float], key: str, val: bool, cfg: FeaturizerConfig) -> None:
    _add_feature(acc, f"{key}={'1' if val else '0'}", 1.0, cfg)


def _bucketize_log(value: float) -> str:
    if value <= 0.0:
        return "0"
    b = int(math.floor(math.log1p(value) * 2.0))
    return str(max(0, min(24, b)))


def _add_num(acc: dict[int, float], key: str, value: float, cfg: FeaturizerConfig) -> None:
    v = float(value)
    if not math.isfinite(v):
        return
    if v >= 0.0:
        scaled = math.log1p(v)
    else:
        scaled = -math.log1p(abs(v))
    if scaled > 6.0:
        scaled = 6.0
    elif scaled < -6.0:
        scaled = -6.0
    _add_feature(acc, f"num:{key}", scaled, cfg)
    _add_feature(acc, f"num_bucket:{key}:{_bucketize_log(max(0.0, v))}", 1.0, cfg)


def _add_tokens(
    acc: dict[int, float],
    *,
    prefix: str,
    text: str,
    cfg: FeaturizerConfig,
    max_tokens: int,
) -> None:
    if not text:
        return
    toks = _tokenize_identifier(text)
    if not toks:
        return
    for tok in toks[: max(0, max_tokens)]:
        _add_feature(acc, f"{prefix}:{tok}", 1.0, cfg)


def row_to_sparse_features(row: dict[str, Any], cfg: FeaturizerConfig) -> dict[int, float]:
    src = row.get("source") if isinstance(row.get("source"), dict) else {}
    dst = row.get("target") if isinstance(row.get("target"), dict) else {}
    graph = row.get("graph_context") if isinstance(row.get("graph_context"), dict) else {}
    failure = row.get("failure_context") if isinstance(row.get("failure_context"), dict) else {}
    src_type = src.get("type") if isinstance(src.get("type"), dict) else {}
    dst_type = dst.get("type") if isinstance(dst.get("type"), dict) else {}

    acc: dict[int, float] = {}

    _add_feature(acc, "__bias__", 1.0, cfg)

    link_kind = _safe_text(row.get("link_kind")) or "value"
    _add_cat(acc, "link_kind", link_kind, cfg)
    _add_cat(acc, "sample_kind", _safe_text(row.get("sample_kind")), cfg)

    src_kind = _safe_text(src.get("kind"))
    dst_kind = _safe_text(dst.get("kind"))
    src_family = _safe_text(src.get("module_family"))
    dst_family = _safe_text(dst.get("module_family"))
    src_depth = _safe_text(src.get("rep_depth"))
    dst_depth = _safe_text(dst.get("rep_depth"))

    _add_cat(acc, "src_kind", src_kind, cfg)
    _add_cat(acc, "dst_kind", dst_kind, cfg)
    _add_cat(acc, "src_family", src_family, cfg)
    _add_cat(acc, "dst_family", dst_family, cfg)
    _add_cat(acc, "src_depth", src_depth, cfg)
    _add_cat(acc, "dst_depth", dst_depth, cfg)

    if src_kind and dst_kind:
        _add_cat(acc, "kind_pair", f"{src_kind}->{dst_kind}", cfg)
    if src_family and dst_family:
        _add_cat(acc, "family_pair", f"{src_family}->{dst_family}", cfg)
    if src_depth and dst_depth:
        _add_cat(acc, "depth_pair", f"{src_depth}->{dst_depth}", cfg)

    _add_bool(acc, "same_module", _safe_bool(graph.get("same_module")), cfg)
    _add_bool(acc, "same_family", _safe_bool(graph.get("same_module_family")), cfg)

    src_depth_nat = _safe_float(src.get("rep_depth_nat"), 0.0)
    dst_depth_nat = _safe_float(dst.get("rep_depth_nat"), 0.0)
    _add_num(acc, "depth_src_nat", src_depth_nat, cfg)
    _add_num(acc, "depth_dst_nat", dst_depth_nat, cfg)
    _add_num(acc, "depth_gap_abs", abs(src_depth_nat - dst_depth_nat), cfg)

    _add_num(acc, "src_out_degree", _safe_float(graph.get("source_out_degree"), 0.0), cfg)
    _add_num(acc, "dst_in_degree", _safe_float(graph.get("target_in_degree"), 0.0), cfg)

    _add_num(acc, "src_failure_pressure", _safe_float(failure.get("source_failure_pressure"), 0.0), cfg)
    _add_num(acc, "dst_failure_pressure", _safe_float(failure.get("target_failure_pressure"), 0.0), cfg)
    _add_num(acc, "pair_failure_count", _safe_float(failure.get("pair_failure_count"), 0.0), cfg)
    _add_num(acc, "failure_count", _safe_float(failure.get("failure_count"), 0.0), cfg)
    _add_num(acc, "failure_total_cost", _safe_float(failure.get("failure_total_cost"), 0.0), cfg)

    _add_num(acc, "unusual_score", _safe_float(row.get("unusual_score"), 0.0), cfg)
    _add_num(acc, "hardness", _safe_float(row.get("hardness"), 0.0), cfg)

    err_kinds = failure.get("pair_error_kinds")
    if isinstance(err_kinds, list):
        for err in err_kinds:
            _add_cat(acc, "pair_error_kind", _safe_text(err), cfg)

    _add_tokens(
        acc,
        prefix="src_name",
        text=_safe_text(src.get("name")),
        cfg=cfg,
        max_tokens=cfg.text_token_limit,
    )
    _add_tokens(
        acc,
        prefix="dst_name",
        text=_safe_text(dst.get("name")),
        cfg=cfg,
        max_tokens=cfg.text_token_limit,
    )
    _add_tokens(
        acc,
        prefix="src_mod",
        text=_safe_text(src.get("module")),
        cfg=cfg,
        max_tokens=max(8, cfg.text_token_limit // 2),
    )
    _add_tokens(
        acc,
        prefix="dst_mod",
        text=_safe_text(dst.get("module")),
        cfg=cfg,
        max_tokens=max(8, cfg.text_token_limit // 2),
    )

    _add_tokens(
        acc,
        prefix="src_doc",
        text=_safe_text(src.get("doc")),
        cfg=cfg,
        max_tokens=max(8, cfg.text_token_limit // 2),
    )
    _add_tokens(
        acc,
        prefix="src_lean",
        text=_safe_text(src.get("lean_snippet")),
        cfg=cfg,
        max_tokens=max(10, cfg.text_token_limit),
    )
    _add_tokens(
        acc,
        prefix="dst_doc",
        text=_safe_text(dst.get("doc")),
        cfg=cfg,
        max_tokens=max(8, cfg.text_token_limit // 2),
    )
    _add_tokens(
        acc,
        prefix="dst_lean",
        text=_safe_text(dst.get("lean_snippet")),
        cfg=cfg,
        max_tokens=max(10, cfg.text_token_limit),
    )

    _add_tokens(
        acc,
        prefix="src_type",
        text=_safe_text(src_type.get("type_str")),
        cfg=cfg,
        max_tokens=max(8, cfg.text_token_limit // 2),
    )
    _add_tokens(
        acc,
        prefix="dst_type",
        text=_safe_text(dst_type.get("type_str")),
        cfg=cfg,
        max_tokens=max(8, cfg.text_token_limit // 2),
    )

    return acc


def sparse_dot(weights: Any, feats: dict[int, float]) -> float:
    total = 0.0
    for idx, val in feats.items():
        if 0 <= idx < len(weights):
            total += weights[idx] * val
    return total


def sigmoid(x: float) -> float:
    if x >= 0.0:
        z = math.exp(-x)
        return 1.0 / (1.0 + z)
    z = math.exp(x)
    return z / (1.0 + z)


def weighted_logloss(
    probs: list[float],
    labels: list[int],
    weights: list[float],
    eps: float = 1e-8,
) -> float:
    numer = 0.0
    denom = 0.0
    for p, y, w in zip(probs, labels, weights):
        ww = max(0.0, float(w))
        if ww == 0.0:
            continue
        pp = min(1.0 - eps, max(eps, float(p)))
        yy = 1.0 if int(y) == 1 else 0.0
        numer += ww * (-(yy * math.log(pp) + (1.0 - yy) * math.log(1.0 - pp)))
        denom += ww
    if denom <= 0.0:
        return 0.0
    return numer / denom


def weighted_accuracy(probs: list[float], labels: list[int], weights: list[float]) -> float:
    numer = 0.0
    denom = 0.0
    for p, y, w in zip(probs, labels, weights):
        ww = max(0.0, float(w))
        if ww == 0.0:
            continue
        pred = 1 if p >= 0.5 else 0
        numer += ww * (1.0 if pred == int(y) else 0.0)
        denom += ww
    if denom <= 0.0:
        return 0.0
    return numer / denom


def binary_auc(scores: list[float], labels: list[int]) -> float:
    pairs = [(float(s), int(y)) for s, y in zip(scores, labels)]
    pos = sum(1 for _, y in pairs if y == 1)
    neg = sum(1 for _, y in pairs if y == 0)
    if pos == 0 or neg == 0:
        return 0.5
    pairs.sort(key=lambda t: t[0])
    rank_sum = 0.0
    for i, (_, y) in enumerate(pairs, start=1):
        if y == 1:
            rank_sum += float(i)
    auc = (rank_sum - (pos * (pos + 1) / 2.0)) / float(pos * neg)
    return max(0.0, min(1.0, auc))
