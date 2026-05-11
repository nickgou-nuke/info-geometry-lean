from __future__ import annotations

import json
import re
import urllib.error
import urllib.request
from typing import Any


def normalize_model_text(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", " ", str(value).lower()).strip()


def model_token_set(value: str) -> set[str]:
    return {token for token in normalize_model_text(value).split() if token}


def _alias_variants(model: str) -> list[str]:
    raw = str(model).strip()
    if not raw:
        return []
    variants: list[str] = []
    for item in [raw, raw.split("/")[-1], raw.split("\\")[-1]]:
        tokenized = normalize_model_text(item)
        if tokenized and tokenized not in variants:
            variants.append(tokenized)
    stem = raw.rsplit(".", 1)[0]
    tokenized = normalize_model_text(stem)
    if tokenized and tokenized not in variants:
        variants.append(tokenized)
    return variants


def parse_model_ids(payload: Any) -> list[str]:
    if not isinstance(payload, dict):
        return []
    rows = payload.get("data")
    if not isinstance(rows, list):
        return []
    ids: list[str] = []
    for row in rows:
        if isinstance(row, dict):
            value = row.get("id")
            if isinstance(value, str) and value:
                ids.append(value)
    return ids


def choose_matching_model(
    requested: str, available_ids: list[str], *, fallback_to_first: bool = True, require_match: bool = False
) -> str:
    """Return the best endpoint model id for a requested logical model name.

    Matching supports:
    - exact identity
    - path suffix / basename equivalence
    - token overlap (e.g. ``leanstral-gguf`` vs ``/models/...leanstral...gguf``)
    """
    if not requested:
        return ""
    if not available_ids:
        return requested

    requested_candidates = _alias_variants(requested)
    if requested in available_ids:
        return requested

    request_tokens = model_token_set(requested)
    if not request_tokens:
        return requested

    def score(candidate: str) -> int:
        candidate_tokens = model_token_set(candidate)
        candidate_norm = normalize_model_text(candidate)
        candidate_raw = candidate.lower()

        s = 0
        if requested.lower() == candidate_raw:
            s += 16
        for variant in requested_candidates:
            if variant == candidate_norm:
                s += 12
            elif variant and variant in candidate_norm:
                s += 6

        overlap = len(request_tokens & candidate_tokens)
        if overlap:
            s += overlap * 3
        if request_tokens.issubset(candidate_tokens):
            s += 4

        # Prefer leanstral-tagged identifiers when matching a leanstral alias.
        if "leanstral" in request_tokens and "leanstral" in candidate_tokens:
            s += 5
        return s

    best = requested
    best_score = -1
    for candidate in available_ids:
        if not isinstance(candidate, str):
            continue
        s = score(candidate)
        if s > best_score:
            best_score = s
            best = candidate

    if best_score <= 0:
        if require_match:
            return ""
        if fallback_to_first:
            return available_ids[0]
        return requested
    return best


def fetch_model_ids(base_url: str, timeout: int) -> tuple[int, list[str], str]:
    """Fetch /models listing from OpenAI-compatible endpoint."""
    url = f"{base_url.rstrip('/')}/models"
    req = urllib.request.Request(url, headers={"Accept": "application/json"}, method="GET")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as response:  # noqa: S310 local-only endpoint
            raw = response.read().decode("utf-8", errors="replace")
            payload = json.loads(raw)
            return int(response.status), parse_model_ids(payload), raw
    except urllib.error.HTTPError as exc:
        raw = exc.read().decode("utf-8", errors="replace")
        try:
            payload = json.loads(raw)
        except Exception:
            payload = None
        return int(exc.code), parse_model_ids(payload), raw
    except Exception as exc:  # noqa: BLE001 - local endpoint probe
        return 0, [], repr(exc)


def model_match_score(expected: str, candidate: str) -> int:
    if not expected:
        return 0
    expected = str(expected).strip()
    candidate = str(candidate).strip()
    if not candidate:
        return -1
    if expected == candidate:
        return 3

    expected_variants = _alias_variants(expected)
    candidate_norm = normalize_model_text(candidate)
    if any(expected_variant == candidate_norm for expected_variant in expected_variants):
        return 2

    score = len(model_token_set(expected).intersection(model_token_set(candidate)))
    if score:
        return score
    for expected_variant in expected_variants:
        if expected_variant and expected_variant in candidate_norm:
            return 1
    return 0


def resolve_with_expected(expected: str, candidate: str, available_ids: list[str]) -> str:
    """Resolve a configured model against available ids using expected as anchor.

    If both fields can match different ids, this returns the configured model string.
    """
    if not candidate:
        return ""
    if not expected:
        return candidate

    resolved_expected = choose_matching_model(expected, available_ids, fallback_to_first=False, require_match=True)
    if not resolved_expected:
        return ""
    resolved_candidate = choose_matching_model(candidate, available_ids, fallback_to_first=False, require_match=True)
    return resolved_candidate if model_match_score(resolved_expected, resolved_candidate) > 0 else ""
