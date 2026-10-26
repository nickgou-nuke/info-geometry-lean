#!/usr/bin/env python3
"""Darwin commit-evolution graph operators.

Read-only AQL queries over commit_nodes/commit_edges/taxonomy_ranks
plus lightweight bridges to decls DNA.
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


def db():
    load_repo_arango_env(REPO_ROOT)
    client = ArangoClient(hosts=arango_endpoint())
    return client.db(arango_database(), username=arango_username(), password=arango_password())


REPO_ROOT = Path(__file__).resolve().parents[2]


def taxonomy_summary(database) -> Iterable[dict]:
    q = """
    FOR r IN taxonomy_ranks
      SORT r.rankIndex
      RETURN {rank: r.rank, rankIndex: r.rankIndex, name: r.name, commits: r.commitCount}
    """
    return database.aql.execute(q)


def species_emergence(database, rank: str = "Species") -> Iterable[dict]:
    q = """
    FOR c IN commit_nodes
      FILTER c.taxonRank == @rank
      SORT c.date
      RETURN {
        hash: c._key,
        date: c.date,
        author: c.author,
        message: c.message,
        modulePaths: c.modulePaths,
        diffHash: c.diffHash
      }
    """
    return database.aql.execute(q, bind_vars={"rank": rank})


def commit_scc(database) -> Iterable[dict]:
    """Genuine Tarjan SCC over the commit lineage (replaces the listing stub)."""
    from tools.infra.darwin_evolution_algorithms import fetch_lineage, tarjan_scc

    vertices, adjacency = fetch_lineage(database)
    sccs = tarjan_scc(vertices, adjacency)
    multi = sorted((sorted(c) for c in sccs if len(c) > 1), key=len, reverse=True)
    if not multi:
        yield {
            "scc_id": 0,
            "size": 1,
            "membersSample": [],
            "note": (
                "lineage DAG confirmed acyclic: all %d SCCs are singletons"
                % len(sccs)
            ),
        }
        return
    for i, members in enumerate(multi[:20]):
        yield {"scc_id": i, "size": len(members), "membersSample": members[:5]}


def coarse_grain_by_rank(database, rank: str = "Family") -> Iterable[dict]:
    q = """
    FOR c IN commit_nodes
      FILTER c.taxonRank == @rank
      COLLECT taxon = c.message WITH COUNT INTO size
      RETURN {taxon, size}
    """
    return database.aql.execute(q, bind_vars={"rank": rank})


def phylogenetic_paths(database, target_hash: str, depth: int = 6) -> Iterable[dict]:
    q = """
    FOR v, e, p IN 1..@depth INBOUND @target commit_edges
      RETURN {
        from: v._key,
        to: p.vertices[-1]._key,
        edges: p.edges[*].edgeKind,
        path: p.vertices[*].taxonRank
      }
    """
    return database.aql.execute(q, bind_vars={"target": f"commit_nodes/{target_hash}", "depth": depth})


def verified_species(database) -> Iterable[dict]:
    q = """
    FOR c IN commit_nodes
      FILTER c.leanVerified
      RETURN {hash: c._key, rank: c.taxonRank, date: c.date, message: c.message}
    """
    return database.aql.execute(q)


def commit_decl_bridge(database, limit: int = 200) -> Iterable[dict]:
    q = """
    FOR e IN commit_decl_edges
      LIMIT @limit
      RETURN {commit: e._from, path: e._to}
    """
    return database.aql.execute(q, bind_vars={"limit": limit})


def connected_components_by_module(database, module_prefix: str = "lean/InfoGeometry/") -> Iterable[dict]:
    q = """
    FOR c IN commit_nodes
      FILTER c.modulePaths != [] AND (
        @modulePrefix == "" OR EXISTS(
          FOR p IN c.modulePaths RETURN p FILTER STARTS_WITH(p, @modulePrefix)
        )
      )
      RETURN {hash: c._key, paths: c.modulePaths}
    """
    return database.aql.execute(q, bind_vars={"modulePrefix": module_prefix})


def main() -> int:
    import argparse
    parser = argparse.ArgumentParser(description="Darwin graph operators")
    parser.add_argument("--query", required=True, choices=[
        "taxonomy_summary",
        "species_emergence",
        "commit_scc",
        "coarse_grain",
        "phylogenetic_paths",
        "verified_species",
        "commit_decl_bridge",
        "connected_components",
    ])
    parser.add_argument("--rank", default="Species")
    parser.add_argument("--target", default="")
    parser.add_argument("--depth", type=int, default=6)
    parser.add_argument("--module-prefix", default="lean/InfoGeometry/")
    parser.add_argument("--limit", type=int, default=200)
    args = parser.parse_args()
    database = db()
    queries = {
        "taxonomy_summary": taxonomy_summary,
        "species_emergence": lambda db: species_emergence(db, args.rank),
        "commit_scc": commit_scc,
        "coarse_grain": lambda db: coarse_grain_by_rank(db, args.rank),
        "phylogenetic_paths": lambda db: phylogenetic_paths(db, args.target, args.depth),
        "verified_species": verified_species,
        "commit_decl_bridge": lambda db: commit_decl_bridge(db, args.limit),
        "connected_components": lambda db: connected_components_by_module(db, args.module_prefix),
    }
    for row in queries[args.query](database):
        print(row)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
