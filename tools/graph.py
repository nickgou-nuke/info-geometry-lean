#!/usr/bin/env python3
"""Compatibility shim for the archived declaration-graph wrapper.

This module is no longer the canonical causal-order surface of the repository.
The current authoritative declaration graph lives in `artifacts/dag/full_graph.json`
and `artifacts/dag/index/decls.jsonl`, refreshed via `tools/refresh_decl_graph.py`
and consumed directly by the current causal-report pipeline.

The original NetworkX wrapper now lives at:
- `archive/legacy/scripts/graph.py`

Keep this shim only for older consumers that still import `tools.graph`.
Do not route new causal-order tooling through it.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path
from types import ModuleType

_ARCHIVE_PATH = Path(__file__).resolve().parents[1] / "archive" / "legacy" / "scripts" / "graph.py"


def _load_legacy_module() -> ModuleType:
    spec = importlib.util.spec_from_file_location("_info_geometry_legacy_graph", _ARCHIVE_PATH)
    if spec is None or spec.loader is None:
        raise ImportError(f"unable to load legacy graph wrapper from {_ARCHIVE_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_legacy = _load_legacy_module()

ProjectGraph = _legacy.ProjectGraph
load_graph = _legacy.load_graph
edges_as_tuples = _legacy.edges_as_tuples
nodes = _legacy.nodes

__all__ = [
    "ProjectGraph",
    "load_graph",
    "edges_as_tuples",
    "nodes",
]
