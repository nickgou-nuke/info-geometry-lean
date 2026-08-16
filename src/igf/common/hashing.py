"""
Unified Hashing utilities for IGF.
Canonical deduplicated implementation for de Bruijn, stable hashing, and AST fingerprints.
"""

from __future__ import annotations

import hashlib
import json
from typing import Any


def stable_hash(*parts: Any, length: int = 16, size: int | None = None) -> str:
    """Computes a stable deterministic SHA256 hex digest for arbitrary nested objects or variadic parts."""
    effective_length = size if size is not None else length
    if len(parts) == 1:
        val = parts[0]
    elif len(parts) == 0:
        val = ""
    else:
        val = parts

    if isinstance(val, str):
        payload = val.encode("utf-8")
    elif isinstance(val, (bytes, bytearray)):
        payload = bytes(val)
    else:
        payload = json.dumps(val, sort_keys=True, default=str).encode("utf-8")
    digest = hashlib.sha256(payload).hexdigest()
    return digest[:effective_length] if effective_length > 0 else digest


def prefixed_hash(*parts: Any) -> str:
    """Computes a SHA256 hex digest prefixed with 'sha256:' joined by '|'."""
    payload = "|".join(str(part) for part in parts)
    return "sha256:" + hashlib.sha256(payload.encode("utf-8")).hexdigest()


def stable_key(prefix: str, *parts: Any, length: int = 32) -> str:
    """Computes a stable deterministic document/edge key formatted as <prefix>_<hex[:length]>."""
    digest = prefixed_hash(*parts).split(":", 1)[1]
    return f"{prefix}_{digest[:length]}" if prefix else digest[:length]


def compute_exact_hash(source: str, length: int = 16) -> str:
    """Computes SHA256 of trimmed source string."""
    return stable_hash(source.strip(), length=length)


def hash_file(path_or_bytes: Any, length: int = 16) -> str:
    """Hashes file content or bytes."""
    if hasattr(path_or_bytes, "read_bytes"):
        return stable_hash(path_or_bytes.read_bytes(), length=length)
    return stable_hash(path_or_bytes, length=length)
