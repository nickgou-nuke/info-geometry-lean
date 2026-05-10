"""Tests for tools/infra/hash_signature.py — whitespace normalization and SHA-256 hashing."""
from __future__ import annotations

import hashlib

import pytest

from tools.infra.hash_signature import normalize_ws


def test_normalize_ws_collapses_spaces() -> None:
    assert normalize_ws("a   b  c") == "a b c"


def test_normalize_ws_collapses_newlines() -> None:
    assert normalize_ws("a\nb\nc") == "a b c"


def test_normalize_ws_collapses_tabs() -> None:
    assert normalize_ws("a\t\tb") == "a b"


def test_normalize_ws_strips_leading_trailing() -> None:
    assert normalize_ws("  hello world  ") == "hello world"


def test_normalize_ws_empty_string() -> None:
    assert normalize_ws("") == ""


def test_normalize_ws_already_normalized() -> None:
    text = "foo bar baz"
    assert normalize_ws(text) == text


def test_normalize_ws_mixed_whitespace() -> None:
    assert normalize_ws("  a\t \nb  ") == "a b"


def test_hash_of_normalized_signature_is_stable() -> None:
    sig = normalize_ws("  ∀ x : α, f x = g x  ")
    digest = hashlib.sha256(sig.encode("utf-8")).hexdigest()
    assert len(digest) == 64
    # Stable across calls
    assert hashlib.sha256(sig.encode("utf-8")).hexdigest() == digest


def test_hash_differs_for_different_signatures() -> None:
    s1 = normalize_ws("A → B")
    s2 = normalize_ws("B → A")
    h1 = hashlib.sha256(s1.encode("utf-8")).hexdigest()
    h2 = hashlib.sha256(s2.encode("utf-8")).hexdigest()
    assert h1 != h2


def test_normalize_ws_unicode_preserved() -> None:
    result = normalize_ws("α  →  β")
    assert result == "α → β"
