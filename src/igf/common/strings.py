"""
Unified String & Key Sanitization utilities for IGF.
Canonical deduplicated implementation for slugs and ArangoDB keys.
"""

from __future__ import annotations

import re


def slugify(text: str) -> str:
    """Converts arbitrary text into a clean alphanumeric kebab-case or snake-case slug."""
    clean = re.sub(r"[^\w\s-]", "", text.strip().lower())
    return re.sub(r"[-\s]+", "_", clean)


def sanitize_key(raw: str, max_len: int = 200) -> str:
    """Sanitizes an arbitrary string into a valid ArangoDB _key."""
    clean = "".join(c if (c.isalnum() or c in "_-") else "_" for c in raw)
    return clean[:max_len]
