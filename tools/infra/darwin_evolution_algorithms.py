#!/usr/bin/env python3
"""Darwin evolution algorithms over the live declaration/commit graphs.

Genuine graph operators, no stubs:

- iterative Tarjan SCC over ``commit_nodes`` / ``commit_parent_edges_v2``;
- union-find weak connected components of the observed parent-edge graph;
- SCC-condensation statistics for the imported graph;
- DNA-projection connectivity: two commits belong to one DNA cohort when they
  bridge to a shared declaration through ``commit_decl_edges`` (bidirectional
  union-find over the commit-declaration bipartite graph),
- Multi-label weak change-category summaries from ``changeLabels``. These
  facets are not an ordered taxonomy and are never interpreted as descent.
- Data-level anti-collapse witnesses: distinct commit hashes sharing one
  identical non-empty ``modulePaths`` list remain distinct graph nodes. This
  mirrors ``shared_path_not_equivalence`` and includes observed witness rows.

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
from tools.infra.graph_components import tarjan_scc

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
    """Vertices and parent-to-child adjacency from the v2 Git edge collection."""
    vertices: list[str] = []
    for doc in db.collection("commit_nodes").all():
        vertices.append(doc["_key"])
    adjacency: dict[str, list[str]] = defaultdict(list)
    for e in db.collection("commit_parent_edges_v2").all():
        if e.get("edgeKind") != "parent_of":
            continue
        src = e["_from"].split("/", 1)[1]
        dst = e["_to"].split("/", 1)[1]
        adjacency[src].append(dst)
    return vertices, adjacency


# ------------------------------------------------- genuine graph algorithms

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
    """BFS frontier sizes from ``root`` through descendant edges."""
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


def change_facet_summary(db) -> dict:
    """Summarize weak categories without turning them into a hierarchy."""
    commits = 0
    labeled_commits = 0
    legacy_rank_records = 0
    category_commit_counts: Counter[str] = Counter()
    category_ids: dict[str, str] = {}
    malformed_labels = 0
    for doc in db.collection("commit_nodes").all():
        commits += 1
        legacy_rank_records += int("taxonRank" in doc or "taxonRankIndex" in doc)
        labels = doc.get("changeLabels") or []
        seen: set[str] = set()
        for label in labels:
            category = label.get("category") if isinstance(label, dict) else None
            category_id = label.get("categoryId") if isinstance(label, dict) else None
            weight = label.get("ruleWeightPercent") if isinstance(label, dict) else None
            evidence_kinds = label.get("evidenceKinds") if isinstance(label, dict) else None
            if (not category or not category_id or label.get("status") != "weak_rule"
                    or not isinstance(weight, int) or not 0 <= weight <= 100
                    or not isinstance(evidence_kinds, list) or not evidence_kinds):
                malformed_labels += 1
                continue
            category_ids[category] = category_id
            seen.add(category)
        if seen:
            labeled_commits += 1
        category_commit_counts.update(seen)
    return {
        "method": "weak-rule-v3",
        "hierarchical": False,
        "commits": commits,
        "labeledCommits": labeled_commits,
        "unlabeledCommits": commits - labeled_commits,
        "malformedLabelCount": malformed_labels,
        "legacyRankRecordCount": legacy_rank_records,
        "categories": [
            {"category": category, "categoryId": category_ids[category],
             "commits": count, "ruleWeightsAreProbabilities": False}
            for category, count in sorted(category_commit_counts.items())
        ],
    }


def commit_identity_witnesses(db) -> dict:
    """Expose observed witnesses for distinct hashes sharing one path list."""
    legacy_rank_records = 0
    modulepaths_by_key: dict[str, list] = {}
    for doc in db.collection("commit_nodes").all():
        legacy_rank_records += int("taxonRank" in doc or "taxonRankIndex" in doc)
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
        "legacyRankRecordCount": legacy_rank_records,
        "antiCollapseWitnessCount": len(witness_pairs),
        "antiCollapseWitnesses": witness_pairs,
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
    biggest_root, biggest_size = max(
        component_sizes.items(), key=lambda kv: kv[1], default=(None, 0)
    )
    head = _git(["rev-parse", "HEAD"]).strip()
    return {
        "reportSchema": "info_geometry.darwin_evolution_report.v2",
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
        "changeFacets": change_facet_summary(db),
        "commitIdentityWitnesses": commit_identity_witnesses(db),
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
    facets = report["changeFacets"]
    print("weak change facets (non-hierarchical):")
    for row in facets["categories"]:
        print("  %-34s %6d commits" % (row["category"], row["commits"]))
    print("facet coverage: %d/%d commits labeled; malformed labels=%d" % (
        facets["labeledCommits"], facets["commits"], facets["malformedLabelCount"]
    ))
    inv = report["commitIdentityWitnesses"]
    print("commit identity: %d path-sharing witness groups; legacy rank rows=%d" % (
        inv["antiCollapseWitnessCount"], inv["legacyRankRecordCount"]
    ))
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
