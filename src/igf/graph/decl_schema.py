"""Shared schema for the compiled-DAG extraction (Lean → JSONL → ArangoDB).

Single owner, on the Python side, of:

- ``decl_key``: L0 declaration key ``d_`` + sha256(``Name.toString``)[:40]
  (same formula as ``DAG.Schema.declKey`` in Lean and the historical importer);
- ``edge_key``: deterministic L3 edge key ``e_`` + sha256("src|kind|dst")[:40];
- version labels for every hash family found in stored rows;
- ``term_digest``: reference implementation of the L1 nameless digest
  ``lean-expr-debruijn-v4`` (``lean/DAG/TermDigest.lean``), used to cross-check
  Lean output with shared test vectors.

Digests and keys are navigation/search keys, never proof evidence.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass


SCHEMA_VERSION = "info_geometry.dag_schema.v1"

# Hash families (labels exactly as emitted by the Lean producers).
TERM_DIGEST_VERSION = "lean-expr-debruijn-v4"       # L1 nameless, alpha-invariant, SHA-256
STRUCTURAL_FINGERPRINT_VERSION = "lean-expr-structural-v3"  # legacy UInt64, includes binder names
SHAPE_FINGERPRINT_VERSION = "lean-expr-shape-v2"    # L2 coarse template, search only
LEGACY_CANONICAL_V2_VERSION = "lean-expr-canonical-v2"  # 2026-09 generation, binder names erased, UInt64

EDGE_KINDS = ("type", "value")


def _sha256_hex(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def decl_key(name: str) -> str:
    """L0 declaration key from the exact ``Name.toString`` emitted by Lean."""
    return "d_" + _sha256_hex(str(name))[:40]


def edge_key(src: str, kind: str, dst: str) -> str:
    """Deterministic L3 edge key; re-imports are idempotent."""
    return "e_" + _sha256_hex(f"{src}|{kind}|{dst}")[:40]


# ---------------------------------------------------------------------------
# L1 reference encoding (must match lean/DAG/TermDigest.lean byte for byte)
# ---------------------------------------------------------------------------

VERSION_BYTE = 0x04
TAGS = {
    "bvar": 0x01, "fvar": 0x02, "mvar": 0x03, "sort": 0x04, "const": 0x05,
    "app": 0x06, "lam": 0x07, "forall": 0x08, "let": 0x09, "lit": 0x0A, "proj": 0x0C,
}

# Terms are tuples:
#   ("bvar", i) ("fvar",) ("mvar",) ("sort", level) ("const", name, (levels...))
#   ("app", f, a) ("lam", ty, body) ("forall", ty, body) ("let", ty, val, body)
#   ("litnat", n) ("litstr", s) ("proj", struct_name, idx, body) ("mdata", body)
# Levels: ("zero",) ("succ", l) ("max", a, b) ("imax", a, b) ("param", name) ("lmvar",)
# Binder names / binder info are simply absent: the encoding erases them.
Term = tuple
Level = tuple


def _u32(n: int) -> bytes:
    return n.to_bytes(4, "big")


def _str(s: str) -> bytes:
    raw = s.encode("utf-8")
    return _u32(len(raw)) + raw


def _nat(n: int) -> bytes:
    return _str(str(n))


def encode_level(level: Level) -> tuple[bytes, bool]:
    tag = level[0]
    if tag == "zero":
        return b"\x00", False
    if tag == "succ":
        inner, o = encode_level(level[1])
        return b"\x01" + inner, o
    if tag in ("max", "imax"):
        a, oa = encode_level(level[1])
        b, ob = encode_level(level[2])
        return (b"\x02" if tag == "max" else b"\x03") + a + b, oa or ob
    if tag == "param":
        return b"\x04" + _str(level[1]), False
    if tag == "lmvar":
        return b"\x05", True
    raise ValueError(f"unknown level {level!r}")


@dataclass(frozen=True)
class TermDigest:
    digest: str
    node_count: int
    open_term: bool
    algorithm_version: str = TERM_DIGEST_VERSION


def term_digest(term: Term) -> TermDigest:
    """Reference SHA-256 Merkle digest of a term (unique-subterm memoised)."""
    memo: dict[Term, bytes] = {}
    state = {"nodes": 0, "open": False}

    def go(t: Term) -> bytes:
        if t in memo:
            return memo[t]
        kind = t[0]
        if kind == "mdata":
            d = go(t[1])
            memo[t] = d
            return d
        head = bytes([VERSION_BYTE])
        is_open = False
        if kind == "bvar":
            body = head + bytes([TAGS["bvar"]]) + _nat(t[1])
        elif kind == "fvar" and len(t) == 2 and isinstance(t[1], int):
            body, is_open = head + bytes([TAGS["fvar"], 0x01]) + _nat(t[1]), False
        elif kind in ("fvar", "mvar"):
            body, is_open = head + bytes([TAGS[kind]]), True
        elif kind == "sort":
            lv, is_open = encode_level(t[1])
            body = head + bytes([TAGS["sort"]]) + lv
        elif kind == "const":
            body = head + bytes([TAGS["const"]]) + _str(t[1]) + _u32(len(t[2]))
            for lvl in t[2]:
                lv, o = encode_level(lvl)
                body += lv
                is_open = is_open or o
        elif kind in ("app", "lam", "forall"):
            body = head + bytes([TAGS[kind]]) + go(t[1]) + go(t[2])
        elif kind == "let":
            body = head + bytes([TAGS["let"]]) + go(t[1]) + go(t[2]) + go(t[3])
        elif kind == "litnat":
            body = head + bytes([TAGS["lit"], 0]) + _nat(t[1])
        elif kind == "litstr":
            body = head + bytes([TAGS["lit"], 1]) + _str(t[1])
        elif kind == "proj":
            body = head + bytes([TAGS["proj"]]) + _str(t[1]) + _nat(t[2]) + go(t[3])
        else:
            raise ValueError(f"unknown term {t!r}")
        state["open"] = state["open"] or is_open
        state["nodes"] += 1
        d = hashlib.sha256(body).digest()
        memo[t] = d
        return d

    root = go(term)
    return TermDigest(root.hex(), state["nodes"], state["open"])
