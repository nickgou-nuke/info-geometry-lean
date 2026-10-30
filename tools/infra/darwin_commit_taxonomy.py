#!/usr/bin/env python3
"""Read-only queries over Git ancestry and weak change-category facets.

Commit parent edges are exact repository ancestry. ``changeLabels`` are
multi-label weak classifications; they do not form a hierarchy and do not
assert declaration identity, semantic equivalence, or theorem status.
"""
from __future__ import annotations

from pathlib import Path
from typing import Iterable

from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_username,
    arango_password,
    load_repo_arango_env,
)
from arango.client import ArangoClient


REPO_ROOT = Path(__file__).resolve().parents[2]


def db():
    load_repo_arango_env(REPO_ROOT)
    client = ArangoClient(hosts=arango_endpoint())
    return client.db(arango_database(), username=arango_username(), password=arango_password())


def taxonomy_summary(database) -> Iterable[dict]:
    """Count weak categories; the historical command name remains stable."""
    query = """
    FOR c IN commit_nodes
      FOR label IN c.changeLabels
      COLLECT category = label.category, categoryId = label.categoryId
      WITH COUNT INTO commitCount
      SORT category
      RETURN {category, categoryId, commitCount,
              method: "weak-rule-v3", hierarchy: false}
    """
    return database.aql.execute(query)


def category_emergence(database, category: str) -> Iterable[dict]:
    query = """
    FOR c IN commit_nodes
      FOR label IN c.changeLabels
      FILTER label.category == @category
      SORT c.date
      RETURN {hash: c._key, date: c.date, author: c.author,
              message: c.message, modulePaths: c.modulePaths, label}
    """
    return database.aql.execute(query, bind_vars={"category": category})


def commit_scc(database) -> Iterable[dict]:
    """Run Tarjan over observed Git parent edges; report the data result."""
    from tools.infra.darwin_evolution_algorithms import fetch_lineage, tarjan_scc

    vertices, adjacency = fetch_lineage(database)
    sccs = tarjan_scc(vertices, adjacency)
    multi = sorted((sorted(component) for component in sccs if len(component) > 1),
                   key=len, reverse=True)
    if not multi:
        yield {"scc_id": 0, "size": 1, "membersSample": [],
               "note": f"observed lineage graph has {len(sccs)} singleton SCCs"}
        return
    for index, members in enumerate(multi[:20]):
        yield {"scc_id": index, "size": len(members), "membersSample": members[:5]}


def coarse_grain_by_category(database, category: str | None = None) -> Iterable[dict]:
    """Group commits by one non-hierarchical weak category."""
    query = """
    FOR c IN commit_nodes
      FOR label IN c.changeLabels
      FILTER @category == null OR label.category == @category
      COLLECT category = label.category, categoryId = label.categoryId
      WITH COUNT INTO commitCount
      SORT category
      RETURN {category, categoryId, commitCount, hierarchy: false}
    """
    return database.aql.execute(query, bind_vars={"category": category})


def phylogenetic_paths(database, target_hash: str, depth: int = 6) -> Iterable[dict]:
    query = """
    FOR v, e, p IN 1..@depth INBOUND @target commit_parent_edges_v2
      RETURN {from: v._key, to: p.vertices[-1]._key,
              edges: p.edges[*].edgeKind,
              changeLabels: p.vertices[*].changeLabels}
    """
    return database.aql.execute(
        query, bind_vars={"target": f"commit_nodes/{target_hash}", "depth": depth}
    )


def commit_decl_bridge(database, limit: int = 200) -> Iterable[dict]:
    query = """
    FOR e IN commit_decl_edges
      LIMIT @limit
      RETURN {commit: e._from, path: e._to, edgeKind: e.edgeKind,
              resolution: e.resolution}
    """
    return database.aql.execute(query, bind_vars={"limit": limit})


def connected_components_by_module(database, module_prefix: str = "lean/InfoGeometry/") -> Iterable[dict]:
    query = """
    FOR c IN commit_nodes
      FILTER c.modulePaths != [] AND (
        @modulePrefix == "" OR LENGTH(
          FOR path IN c.modulePaths FILTER STARTS_WITH(path, @modulePrefix) RETURN 1
        ) > 0
      )
      RETURN {hash: c._key, paths: c.modulePaths, changeLabels: c.changeLabels}
    """
    return database.aql.execute(query, bind_vars={"modulePrefix": module_prefix})


def main() -> int:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--query", required=True, choices=[
        "taxonomy_summary", "category_emergence", "commit_scc", "coarse_grain",
        "phylogenetic_paths", "commit_decl_bridge", "connected_components",
    ])
    parser.add_argument("--category", default="")
    parser.add_argument("--target", default="")
    parser.add_argument("--depth", type=int, default=6)
    parser.add_argument("--module-prefix", default="lean/InfoGeometry/")
    parser.add_argument("--limit", type=int, default=200)
    args = parser.parse_args()
    if args.depth < 1:
        parser.error("--depth must be positive")
    if args.limit < 1:
        parser.error("--limit must be positive")
    database = db()
    queries = {
        "taxonomy_summary": taxonomy_summary,
        "category_emergence": lambda handle: category_emergence(handle, args.category),
        "commit_scc": commit_scc,
        "coarse_grain": lambda handle: coarse_grain_by_category(
            handle, args.category or None
        ),
        "phylogenetic_paths": lambda handle: phylogenetic_paths(
            handle, args.target, args.depth
        ),
        "commit_decl_bridge": lambda handle: commit_decl_bridge(handle, args.limit),
        "connected_components": lambda handle: connected_components_by_module(
            handle, args.module_prefix
        ),
    }
    for row in queries[args.query](database):
        print(row)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
