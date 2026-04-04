#!/usr/bin/env python3
"""Shared vacuity policy configuration for Layer B and Layer C.

This module is the single source of truth for:

- strict path prefixes
- bridge file hints
- attribute-based exemptions
- expected violation severity by file context
"""
from __future__ import annotations

from pathlib import Path


BRIDGE_HINTS_DEFAULT = ["Bridge", "Lift", "Rosetta"]

STRICT_PATHS_DEFAULT = [
    "lean/InfoGeometry/Canonical/",
    "lean/InfoGeometry/Quantum/",
]

# Tags that exempt from vacuity checks. Must match Lean attribute names.
EXEMPT_ATTRS = {"infrastructure", "capstone", "terminal", "expository"}


def is_bridge_file(file_path: str | None, bridge_hints: list[str]) -> bool:
    """Return True when the declaration lives in an explicitly bridge-like file.

    Bridge hints are matched against the file stem only, not directory names,
    to avoid classifying all Canonical/Core files as bridge surfaces.
    """
    if file_path is None:
        return False
    stem = Path(file_path).stem
    return any(hint and hint in stem for hint in bridge_hints)


def is_strict_file(file_path: str | None, strict_paths: list[str]) -> bool:
    """Return True when path is under one of the strict policy prefixes."""
    if file_path is None:
        return False
    return any(file_path.startswith(prefix) for prefix in strict_paths)


def expected_violation_level(
    code: str,
    file_path: str | None,
    strict_paths: list[str],
    bridge_hints: list[str],
) -> str | None:
    """Return expected level for known violation codes in the given file context.

    Returns:
      - "error" or "warning" when policy defines a level for the code.
      - None for unknown codes or when code is out of context for the file.
    """
    is_bridge = is_bridge_file(file_path, bridge_hints)
    is_strict = is_strict_file(file_path, strict_paths)

    if code == "V0/syntactic-vacuity":
        return "warning"
    if code == "V1/public-wrapper-inflation":
        return "error" if is_bridge else "warning"
    if code == "V2/dead-public-theorem":
        return "error" if (is_bridge or is_strict) else "warning"
    if code == "V4/bridge-infrastructure-promoted":
        return "warning" if is_bridge else None
    if code == "V5/certification-wash":
        return "error" if (is_bridge or is_strict) else "warning"
    return None
