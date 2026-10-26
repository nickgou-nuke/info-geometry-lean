#!/usr/bin/env python3
"""Darwin evolution algorithms over the live declaration/commit graphs.

Genuine graph operators, no stubs:

- iterative Tarjan SCC over the ``commit_nodes`` / ``commit_edges`` lineage DAG
  (species clades; in a linear git DAG every SCC is a singleton, and the
  algorithm *proves* acyclicity of lineage by finding no multi-node SCC),
- union-find weak connected components (species cohorts),
- SCC-condensation coarsening (clade condensation DAG statistics),
- DNA-projection connectivity: two commits belong to one DNA cohort when they
  bridge to a shared declaration through ``commit_decl_edges`` (bidirectional
  union-find over the commit-declaration bipartite graph),
- Linnaean rank hierarchy derivation from ``commit_nodes`` (per-rank commit
  histogram, distinct taxa per rank, parent->child rank-index delta histogram
  across ``parent_of`` edges),
- Lean-mirrored data invariants:
    * ``TaxonRank.rankIndex`` round-trip: every commit doc satisfies
      ``taxonRankIndex == _rank_index(taxonRank)`` (mirrors
      ``rankIndex_injective`` / well-definedness in
      ``lean/InfoGeometry/Graph/DarwinCommitTaxonomy.lean``),
    * anti-collapse witnesses: pairs of distinct commits sharing one identical
      non-empty ``modulePaths`` list remain distinct nodes (mirrors
      ``shared_path_not_equivalence``; the premise tuple is shown to be
      *inhabited* by real data, not vacuous).

Boundary (docs/ASTAQLHASH-HOWTO.md): all results are navigation evidence valid
only for the checkout recorded in the report.  Hashes/dedup at data level use
commit hashes and declaration keys resolved by name query; no hash recipe is
assumed for ``decls`` key derivation.  This module is read-only on the
database: no inserts, replacements, or truncates.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter, defaultdict, deque
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable

from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_username,
    arango_password,
    load_repo_arango_env,
)

try:
    from arango.client import ArangoClient
except ImportError as e:  # pragma: no cover
    raise SystemExit(f"python-arango not installed: {e}")

REPO_ROOT = Path(__file__).resolve().parents[2]


# ---------------------------------------------------------------- utilities

def _git(args: list[str]) -> str:
    return subprocess.check_output(
        ["git", *args], cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL
    )


def connect():
    """Connect to the repository-default AST/AQL ArangoDB lane (8530)."""
    load_repo_arango_env(REPO_ROOT)
    client = ArangoClient(hosts=arango_endpoint())
    db = client.db(
        arango_database(), username=arango_username(), password=arango_password()
    )
    return db


def fetch_lineage(db) -> tuple[list[str], dict[str, list[str]]]:
    """Vertices and parent_of adjacency of the commit lineage."""
    vertices: list[str] = []
    for doc in db.collection("commit_nodes").all():
        vertices.append(doc["_key"])
    adjacency: dict[str, list[str]] = defaultdict(list)
    for e in db.collection("commit_edges").all():
        if e.get("edgeKind") != "parent_of":
            continue
        src = e["_from"].split("/", 1)[1]
        dst = e["_to"].split("/", 1)[1]
        adjacency[src].append(dst)
    return vertices, adjacency


# ------------------------------------------------- genuine graph algorithms

def tarjan_scc(vertices: list[str], adjacency: dict[str, list[str]]) -> list[list[str]]:
    """Iterative Tarjan strongly-connected components (no recursion limit)."""
    index_of: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    on_stack: set[str] = set()
    stack: list[str] = []
    sccs: list[list[str]] = []
    counter = 0

    for root in vertices:
        if root in index_of:
            continue
        index_of[root] = lowlink[root] = counter
        counter += 1
        stack.append(root)
        on_stack.add(root)
        call_stack: list[tuple[str, list[str], int]] = [(root, adjacency.get(root, []), 0)]
        while call_stack:
            node, neighbors, pos = call_stack.pop()
            descends_further = False
            i = pos
            while i < len(neighbors):
                nxt = neighbors[i]
                i += 1
                if nxt not in index_of:
                    # bookkeeping: resume parent later at position i
                    call_stack.append((node, neighbors, i))
                    index_of[nxt] = lowlink[nxt] = counter
                    counter += 1
                    stack.append(nxt)
                    on_stack.add(nxt)
                    call_stack.append((nxt, adjacency.get(nxt, []), 0))
                    descends_further = True
                    break
                if nxt in on_stack and index_of[nxt] < lowlink[node]:
                    lowlink[node] = index_of[nxt]
            if descends_further:
                continue
            # node finished: propagate lowlink to the parent frame consumer
            if call_stack:
                parent, _, _ = call_stack[-1]
                if lowlink[node] < lowlink[parent]:
                    lowlink[parent] = lowlink[node]
            if lowlink[node] == index_of[node]:
                scc: list[str] = []
                while True:
                    member = stack.pop()
                    on_stack.discard(member)
                    scc.append(member)
                    if member == node:
                        break
                sccs.append(scc)
    return sccs


def union_components(vertices: Iterable[str], pairs: Iterable[tuple[str, str]]) -> dict[str, str]:
    """Undirected connected components by union-find; returns node -> root."""
    parent = {v: v for v in vertices}

    def find(x: str) -> str:
        root = x
        while parent[root] != root:
            root = parent[root]
        while parent[x] != root:
            parent[x], x = root, parent[x]
        return root

    def union(a: str, b: str) -> None:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra

    for a, b in pairs:
        union(a, b)
    return {v: find(v) for v in parent}


def condensation_stats(
    sccs: list[list[str]], adjacency: dict[str, list[str]]
) -> dict:
    """Coarsen (contract SCCs) and return condensation-DAG statistics."""
    component_of = {}
    for comp_id, members in enumerate(sccs):
        for m in members:
            component_of[m] = comp_id
    cross: set[tuple[int, int]] = set()
    internal_edges = 0
    for src, targets in adjacency.items():
        cu = component_of.get(src)
        if cu is None:
            continue
        for dst in targets:
            cv = component_of.get(dst)
            if cv is None:
                continue
            if cu == cv:
                internal_edges += 1
            else:
                cross.add((cu, cv))
    sizes = sorted((len(c) for c in sccs), reverse=True)
    multi = [len(c) for c in sccs if len(c) > 1]
    return {
        "componentCount": len(sccs),
        "componentCountMultiNode": len(multi),
        "largestComponentSize": sizes[0] if sizes else 0,
        "internalEdges": internal_edges,
        "condensationEdges": len(cross),
        "topComponentSizes": sizes[:10],
        "multiNodeExamples": [
            sorted(c)[:5] for c in sccs if len(c) > 1
        ][:5],
    }


def breadth_first_levels(root: str, adjacency: dict[str, list[str]], depth: int) -> dict[int, int]:
    """BFS frontier sizes from ``root`` through OUT-direction lineage edges."""
    seen = {root}
    frontier = [root]
    levels: dict[int, int] = {}
    for d in range(1, depth + 1):
        nxt: list[str] = []
        for node in frontier:
            for w in adjacency.get(node, []):
                if w not in seen:
                    seen.add(w)
                    nxt.append(w)
        if not nxt:
            break
        levels[d] = len(nxt)
        frontier = nxt
    return levels


# ------------------------------------------------------------- data lenses

def dna_cohorts(db) -> dict:
    """Connect commits through shared declarations (bipartite union-find)."""
    if not db.has_collection("commit_decl_edges"):
        return {"available": False, "reason": "commit_decl_edges collection absent"}
    commits = [doc["_key"] for doc in db.collection("commit_nodes").all()]
    vertices = list(commits)
    pairs: list[tuple[str, str]] = []
    edge_count = 0
    for e in db.collection("commit_decl_edges").all():
        src = e["_from"].split("/", 1)[1]
        dst = e["_to"].split("/", 1)[1]
        # bipartite: commit on left, declaration DNA node keyed d_<...>
        vertices.append(f"decl::{dst}")
        pairs.append((src, f"decl::{dst}"))
        edge_count += 1
    membership = union_components(vertices, dict.fromkeys(iter_pairs_dedup(pairs)))
    commit_set = set(commits)
    commit_components = defaultdict(int)
    for v, root in membership.items():
        if v not in commit_set and not v.startswith("decl::"):
            continue
        if not v.startswith("decl::"):
            commit_components[root] += 1
    cohorts = Counter(commit_components.values())
    top = sorted(commit_components.items(), key=lambda kv: kv[1], reverse=True)[:3]
    return {
        "available": True,
        "commitDeclEdges": edge_count,
        "distinctDNACohorts": len(commit_components),
        "cohortSizeHistogram": [
            {"commits": size, "cohorts": count} for size, count in sorted(cohorts.items())
        ][:20],
        "largestCohorts": [{"commit": c, "size": n} for c, n in top],
        "avgDeclsPerConnectedCommit": (
            round(edge_count / max(len(commit_set), 1), 3)
        ),
    }


def iter_pairs_dedup(pairs):
    seen = set()
    for pair in pairs:
        if pair in seen:
            continue
        seen.add(pair)
        yield pair


def rank_hierarchy(db) -> dict:
    """Linnaean lens over commits: histogram, distinct taxa, descent deltas."""
    rank_of_commit: dict[str, tuple[int, str]] = {}
    for doc in db.collection("commit_nodes").all():
        rank_of_commit[doc["_key"]] = (
            doc.get("taxonRankIndex", 8),
            doc.get("taxonRank", "Unknown"),
        )
    rank_histogram: Counter[int] = Counter()
    for ridx, _ in rank_of_commit.values():
        rank_histogram[ridx] += 1

    taxa_per_rank: Counter[int] = Counter()
    if db.has_collection("taxonomy_ranks"):
        for doc in db.collection("taxonomy_ranks").all():
            taxa_per_rank[doc.get("rankIndex", 8)] += 1

    delta_histogram: Counter[int] = Counter()
    for e in db.collection("commit_edges").all():
        if e.get("edgeKind") != "parent_of":
            continue
        src = e["_from"].split("/", 1)[1]
        dst = e["_to"].split("/", 1)[1]
        child = rank_of_commit.get(src)
        parent = rank_of_commit.get(dst)
        if child is None or parent is None:
            continue
        delta_histogram[child[0] - parent[0]] += 1

    names = {0: "Domain", 1: "Kingdom", 2: "Phylum", 3: "Class",
             4: "Order", 5: "Family", 6: "Genus", 7: "Species", 8: "Unknown"}
    return {
        "rankHistogram": [
            {"rankIndex": r, "rank": names[r], "commits": rank_histogram.get(r, 0),
             "distinctTaxa": taxa_per_rank.get(r, 0)}
            for r in sorted(set(rank_histogram) | set(taxa_per_rank))
        ],
        "parentToChildDeltaHistogram": [
            {"delta": d, "edges": delta_histogram[d]} for d in sorted(delta_histogram)
        ],
        "rankIncreaseEdges": sum(
            n for d, n in delta_histogram.items() if d > 0
        ),
        "rankDecreaseEdges": sum(
            n for d, n in delta_histogram.items() if d < 0
        ),
        "flatRankEdges": sum(
            n for d, n in delta_histogram.items() if d == 0
        ),
    }


def lean_mirrored_invariants(db) -> dict:
    """Check data-level consequences of the committed Lean theorems."""
    from tools.infra.darwin_commit_graph import _rank_index  # single source of truth

    round_trip_violations = []
    taxonomy_histogram: Counter[str] = Counter()
    modulepaths_by_key: dict[str, list] = {}
    for doc in db.collection("commit_nodes").all():
        rank = doc.get("taxonRank", "Species")
        ridx = doc.get("taxonRankIndex")
        taxonomy_histogram[rank] += 1
        if ridx != _rank_index(rank):
            round_trip_violations.append(
                {"commit": doc["_key"], "rank": rank,
                 "recordedIndex": ridx, "expectedIndex": _rank_index(rank)}
            )
        modulepaths_by_key[doc["_key"]] = doc.get("modulePaths") or []

    groups_by_paths: dict[str, list[str]] = defaultdict(list)
    for key, paths in modulepaths_by_key.items():
        if paths:
            groups_by_paths[json.dumps(paths)].append(key)
    witness_pairs = []
    for paths_json, members in groups_by_paths.items():
        if len(members) < 2:
            continue
        witness_pairs.append(
            {
                "modulePaths": json.loads(paths_json),
                "commits": members[:2],
                "commitCountOnSameTree": len(members),
                "distinctNodeKeys": len(set(members)) == len(members),
                "first_members_introduced_different_hashes": members[0] != members[1],
            }
        )
        if len(witness_pairs) >= 10:
            break
    witness_pairs.sort(key=lambda w: -w["commitCountOnSameTree"])
    return {
        "rankIndexRoundTripViolations": round_trip_violations[:10],
        "rankIndexRoundTripViolationCount": len(round_trip_violations),
        "antiCollapseWitnessCount": len(witness_pairs),
        "antiCollapseWitnesses": witness_pairs,
        "rankDistribution": dict(taxonomy_histogram),
    }


# ------------------------------------------------------------------- report

def build_report(db) -> dict:
    vertices, adjacency = fetch_lineage(db)
    sccs = tarjan_scc(vertices, adjacency)
    condensation = condensation_stats(sccs, adjacency)
    lineage_undirected_pairs = [
        (src, dst) for src in vertices for dst in adjacency.get(src, [])
    ]
    components = union_components(vertices, lineage_undirected_pairs)
    component_sizes = Counter(components.values())
    biggest_root, biggest_size = max(component_sizes.items(), key=lambda kv: kv[1])
    head = _git(["rev-parse", "HEAD"]).strip()
    return {
        "reportSchema": "info_geometry.darwin_evolution_report.v1",
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "repoCommit": head,
        "database": db.name,
        "endpoint": arango_endpoint(),
        "sourceAuthority": "arangodb+git; proof authority is the Lean kernel (ASTAQLHASH-HOWTO boundary)",
        "lineage": {
            "commitNodes": len(vertices),
            "parentOfEdges": sum(len(v) for v in adjacency.values()),
            "scc": condensation,
            "lineageAcyclic": condensation["componentCountMultiNode"] == 0,
            "weakComponents": {
                "count": len(component_sizes),
                "largest": component_sizes[biggest_root] if component_sizes else 0,
                "singletonComponents": sum(
                    1 for s in component_sizes.values() if s == 1
                ),
            },
        },
        "dnaCohorts": dna_cohorts(db),
        "taxonomy": rank_hierarchy(db),
        "leanMirroredInvariants": lean_mirrored_invariants(db),
    }


def print_human(report: dict) -> None:
    lineage = report["lineage"]
    print("=== DARWIN EVOLUTION REPORT ===")
    print(f"repo commit : {report['repoCommit'][:12]}  db: {report['database']}")
    print(
        "lineage     : %d commits, %d parent_of edges"
        % (lineage["commitNodes"], lineage["parentOfEdges"])
    )
    print("lineage acyclic (no multi-node SCC): %s" % lineage["lineageAcyclic"])
    scc = lineage["scc"]
    print(
        "SCC         : %d components, largest=%d, condensation edges=%d"
        % (scc["componentCount"], scc["largestComponentSize"], scc["condensationEdges"])
    )
    print(
        "weak comps  : %d (largest %d, singletons %d)"
        % (
            lineage["weakComponents"]["count"],
            lineage["weakComponents"]["largest"],
            lineage["weakComponents"]["singletonComponents"],
        )
    )
    dna = report["dnaCohorts"]
    if dna.get("available"):
        print(
            "DNA cohorts : %d cohorts from %d commit->decl edges (largest %s)"
            % (
                dna["distinctDNACohorts"],
                dna["commitDeclEdges"],
                dna["cohortSizeHistogram"][-1]["commits"] if dna["cohortSizeHistogram"] else 0,
            )
        )
    else:
        print("DNA cohorts : unavailable (%s)" % dna.get("reason"))
    print("rank histogram:")
    for row in report["taxonomy"]["rankHistogram"]:
        print(
            "  %-8s (idx %d): %6d commits, %5d distinct taxa"
            % (row["rank"], row["rankIndex"], row["commits"], row["distinctTaxa"])
        )
    print("descent deltas: +%d increases, %d flat, %d decreases" % (
        report["taxonomy"]["rankIncreaseEdges"],
        report["taxonomy"]["flatRankEdges"],
        report["taxonomy"]["rankDecreaseEdges"],
    ))
    inv = report["leanMirroredInvariants"]
    print(
        "invariants  : rankIndex round-trip violations=%d | anti-collapse witnesses=%d"
        % (inv["rankIndexRoundTripViolationCount"], inv["antiCollapseWitnessCount"])
    )
    for w in inv["antiCollapseWitnesses"][:3]:
        print(
            "  witness: %d commits share %s  (keys %s vs %s)"
            % (
                w["commitCountOnSameTree"],
                w["modulePaths"][:3],
                w["commits"][0][:10],
                w["commits"][1][:10],
            )
        )


def main() -> int:
    parser = argparse.ArgumentParser(description="Genuine Darwin evolution algorithms (read-only)")
    parser.add_argument(
        "--json-out",
        default="artifacts/dag/darwin_evolution_report.json",
        help="write the JSON report here (default artifacts/dag/)",
    )
    args = parser.parse_args()
    db = connect()
    report = build_report(db)
    print_human(report)
    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2, default=str))
    print("json report: %s" % out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
