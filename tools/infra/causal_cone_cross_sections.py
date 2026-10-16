#!/usr/bin/env python3
"""Pure cross-section calculations for causal cone packets."""

from __future__ import annotations

from typing import Any


def directional_cross_section(
    apices: list[dict[str, Any]],
    seed_ids: list[str],
    rows: list[dict[str, Any]],
) -> tuple[dict[str, dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    """Return indexed nodes, nodes shared by multiple seeds, and all-seed nodes."""
    nodes = {str(row["_id"]): row for row in apices}
    seeds_by_node: dict[str, set[str]] = {}
    for row in rows:
        node = row.get("component") or {}
        node_id = str(node.get("_id"))
        if node_id:
            nodes[node_id] = node
            seeds_by_node.setdefault(node_id, set()).add(str(row.get("seed")))

    shared = [
        {"node": nodes[node_id], "seed_count": len(seeds), "seeds": sorted(seeds)}
        for node_id, seeds in seeds_by_node.items()
        if len(seeds) > 1
    ]
    common = [row for row in shared if row["seed_count"] == len(seed_ids)]
    return nodes, shared, common
