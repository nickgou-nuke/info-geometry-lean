#!/usr/bin/env python3
"""
AQL Schema and Fast Graph Topology Tracing for Lean Theory Closure.

The schema is deliberately minimal — two collections, three edge kinds.
This makes AQL queries fast (single-digit milliseconds for cone extraction)
and enables deterministic theory completion: detect missing bridges between
disconnected SCCs, trace dependency chains back to axioms/sorries, and
identify minimal proof patches.

## Collections

  nodes  (document collection)
    _key        : stable node id  (e.g. "DAG.LaplacianRank::laplacian_rank_eq_add_rank")
    name        : short declaration name
    kind        : Theorem | Lemma | Definition | Axiom | Structure | Inductive
    module      : namespace prefix  (e.g. "DAG.LaplacianRank")
    file        : relative lean source path
    line        : line number
    role        : owner | translator | pure_conductor | closure_debt | deferred_interface
    rep_depth   : L0_Count | L1_Projective | ... | L5_ThermodynamicClosure
    module_family: carrier algebraic family tag

  edges  (edge collection)
    _from       : source node key
    _to         : target node key
    kind        : depends_type | depends_value | contains
    weight      : dependency strength 0..1
    evidence_ref: file:line string or sha256 of proof excerpt

## Edge Kinds

  depends_type   "A mentions B in its type signature"
                  → B must compile before A; used for topological sort

  depends_value  "A uses B in its proof body"
                  → B's truth is a premise for A; used for sorries propagation

  contains       "Module M contains declaration D"
                  → module-level grouping for namespace navigation

## Key AQL Query Patterns
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set


# ---------------------------------------------------------------------------
# Schema constants
# ---------------------------------------------------------------------------

SCHEMA_VERSION = "leantrail.aql_schema.v2"

NODE_KINDS = {
    "Theorem", "Lemma", "Definition", "Axiom", "Structure",
    "Inductive", "Instance", "Class", "Abbrev", "Example",
}

EDGE_KINDS = {
    "depends_type",    # structural: B appears in A's type
    "depends_value",   # structural: B used in A's proof
    "contains",        # hierarchical: module → child
}

# Topology roles — each node is classified into exactly one
NODE_ROLES = {
    "owner",              # locally proved, no upstream debt
    "translator",         # bridges two module families
    "pure_conductor",     # 0-sorries, fully-proved leaf
    "closure_debt",       # has a _sorry structural field
    "deferred_interface",        # unused, no incoming edges
    "contaminated",       # transitively depends on axiom/sorry
    "fake_transport",     # True := sorry placeholder
}

# Dependency edge kinds used for causal cone tracing
DEPENDENCY_KINDS = {"depends_type", "depends_value"}


# ---------------------------------------------------------------------------
# AQL Query Library
# ---------------------------------------------------------------------------

@dataclass
class AQLQueries:
    """Catalog of AQL queries for fast graph traversal.

    All queries use bind variables (@var) for injection safety.
    Double-@@ means collection name; single-@ means value.
    """

    nodes_collection: str = "ig_nodes"
    edges_collection: str = "ig_edges"

    # ── causal cone (downstream: what does this node depend on?) ──

    @property
    def cone_downstream(self) -> str:
        """All nodes transitively reachable OUTBOUND from a seed.

        BFS with uniqueVertices: global for O(V+E) performance.
        """
        return f"""
        FOR v, e, p IN 1..@max_depth OUTBOUND @seed_id @@{self.edges_collection}
          OPTIONS {{uniqueVertices: "global", bfs: true}}
          FILTER e.kind IN {sorted(DEPENDENCY_KINDS)}
          RETURN {{
            node: {{id: v._id, name: v.name, kind: v.kind, module: v.module,
                   role: v.role, file: v.file}},
            depth: LENGTH(p.edges),
            path: p.vertices[*]._id
          }}
        """

    @property
    def cone_upstream(self) -> str:
        """All nodes transitively reaching the seed (what depends on this?).

        INBOUND = reverse dependency edge. Shows blast radius.
        """
        return f"""
        FOR v, e, p IN 1..@max_depth INBOUND @seed_id @@{self.edges_collection}
          OPTIONS {{uniqueVertices: "global", bfs: true}}
          FILTER e.kind IN {sorted(DEPENDENCY_KINDS)}
          RETURN {{
            node: {{id: v._id, name: v.name, kind: v.kind, module: v.module,
                   role: v.role, file: v.file}},
            depth: LENGTH(p.edges),
            path: p.vertices[*]._id
          }}
        """

    @property
    def cone_any(self) -> str:
        """Bidirectional cone around a seed (upstream + downstream).

        ANY = both INBOUND and OUTBOUND simultaneously.
        """
        return f"""
        FOR v, e, p IN 1..@max_depth ANY @seed_id @@{self.edges_collection}
          OPTIONS {{uniqueVertices: "global", bfs: true}}
          FILTER e.kind IN {sorted(DEPENDENCY_KINDS)}
          RETURN DISTINCT {{
            node: {{id: v._id, name: v.name, kind: v.kind, module: v.module,
                   role: v.role, file: v.file}},
            direction: e._from == @seed_id ? "downstream" : "upstream",
            depth: LENGTH(p.edges)
          }}
        """

    # ── multi-apex: surround multiple seeds at once ──

    @property
    def cone_multi_apex(self) -> str:
        """Combined cone from multiple seeds.

        Finds the minimal subgraph connecting several target theorems
        to identify shared dependencies or missing bridges.
        """
        return f"""
        FOR seed IN @seed_ids
          FOR v, e, p IN 1..@max_depth ANY seed @@{self.edges_collection}
            OPTIONS {{uniqueVertices: "global", bfs: true}}
            FILTER e.kind IN {sorted(DEPENDENCY_KINDS)}
            RETURN DISTINCT {{
              node: {{id: v._id, name: v.name, kind: v.kind, module: v.module,
                     role: v.role, file: v.file}},
              seed: seed,
              depth: LENGTH(p.edges)
            }}
        """

    # ── frontier: find leaves that are NOT fully proved ──

    @property
    def sorries_frontier(self) -> str:
        """All nodes whose role is contaminated or closure_debt.

        These are the frontier: everything depending on them inherits debt.
        """
        return f"""
        FOR n IN @@{self.nodes_collection}
          FILTER n.role IN ["contaminated", "closure_debt", "deferred_interface"]
          SORT n.module, n.name
          RETURN {{
            id: n._id, name: n.name, kind: n.kind, module: n.module,
            role: n.role, file: n.file, line: n.line
          }}
        """

    @property
    def sorries_blast_radius(self) -> str:
        """For each sorried frontier node, count how many nodes depend on it.

        The blast radius = number of nodes transitively upstream
        that would be proved if this sorried node were closed.
        """
        return f"""
        FOR n IN @@{self.nodes_collection}
          FILTER n.role IN ["contaminated", "closure_debt"]
          LET upstream_count = LENGTH(
            FOR v IN 1..99 INBOUND n._id @@{self.edges_collection}
              FILTER v.role NOT IN ["contaminated", "closure_debt"]
              RETURN v
          )
          SORT upstream_count DESC
          RETURN {{
            id: n._id, name: n.name, module: n.module,
            role: n.role, blast_radius: upstream_count
          }}
        """

    # ── bridge detection: disconnected SCCs that should be connected ──

    @property
    def missing_bridges(self) -> str:
        """Theorems in different SCCs that share the same name tokens.

        Finds pairs of nodes across different strongly-connected components
        that have overlapping keyword tokens — candidates for bridge theorems.
        """
        return f"""
        FOR a IN @@{self.nodes_collection}
          FILTER a.kind IN ["Theorem", "Lemma"]
          FOR b IN @@{self.nodes_collection}
            FILTER b.kind IN ["Theorem", "Lemma"]
            FILTER a._key < b._key
            FILTER a.module != b.module
            FILTER a.role == "pure_conductor" AND b.role == "closure_debt"
            LET shared_tokens = LENGTH(
              FOR tok IN TOKENS(a.name, "[_]+")
                FILTER tok IN TOKENS(b.name, "[_]+")
                RETURN tok
            )
            FILTER shared_tokens >= 2
            RETURN {{
              conductor: {{id: a._id, name: a.name, module: a.module}},
              target: {{id: b._id, name: b.name, module: b.module}},
              shared_tokens: shared_tokens
            }}
        """

    # ── topological layer traversal ──

    @property
    def cross_layer_edges(self) -> str:
        """Edges that jump between representation depth layers.

        A high count of cross-layer edges signals a layered architecture.
        Violations of layering (e.g., L5 → L0) signal regressive dependencies.
        """
        return f"""
        FOR e IN @@{self.edges_collection}
          FILTER e.kind IN {sorted(DEPENDENCY_KINDS)}
          LET src_node = DOCUMENT(e._from)
          LET dst_node = DOCUMENT(e._to)
          FILTER src_node != null AND dst_node != null
          FILTER src_node.rep_depth != dst_node.rep_depth
          RETURN {{
            from: {{id: src_node._id, depth: src_node.rep_depth,
                    module: src_node.module}},
            to: {{id: dst_node._id, depth: dst_node.rep_depth,
                  module: dst_node.module}},
            kind: e.kind
          }}
        """

    # ── shortest path ──

    @property
    def shortest_path(self) -> str:
        """Shortest dependency path between two declarations.

        Uses ArangoDB's built-in SHORTEST_PATH for O(E log V) performance.
        """
        return f"""
        FOR v, e IN ANY SHORTEST_PATH @src TO @dst @@{self.edges_collection}
          FILTER e.kind IN {sorted(DEPENDENCY_KINDS)}
          RETURN {{
            vertex: {{id: v._id, name: v.name, kind: v.kind, module: v.module}},
            edge: {{kind: e.kind, evidence: e.evidence_ref}}
          }}
        """

    # ── theory closure check ──

    @property
    def theory_closure_status(self) -> str:
        """Summary: how many nodes at each closure status?

        clean       = 0 upstream sorries
        honest_sorry = explicit sorry, no contamination
        contaminated = transitively depends on a sorry
        """
        return f"""
        FOR n IN @@{self.nodes_collection}
          COLLECT role = n.role WITH COUNT INTO cnt
          SORT cnt DESC
          RETURN {{role: role, count: cnt}}
        """

    @property
    def theory_closure_pct(self) -> str:
        """Closure percentage: (clean nodes) / (total nodes - axioms)."""
        return f"""
        LET total = LENGTH(FOR n IN @@{self.nodes_collection}
                           FILTER n.kind != "Axiom" RETURN n)
        LET clean = LENGTH(FOR n IN @@{self.nodes_collection}
                           FILTER n.role IN ["pure_conductor", "owner", "translator"]
                           RETURN n)
        RETURN {{total: total, clean: clean, pct_clean: clean * 100 / total}}
        """


# ---------------------------------------------------------------------------
# Python-native topology analysis (no ArangoDB required)
# ---------------------------------------------------------------------------

@dataclass
class TopologyAnalyzer:
    """Lightweight topology analysis over the JSON graph export.

    Uses dict-based adjacency lists — no ArangoDB, no NetworkX dependency.
    Fast enough for graphs up to ~50k nodes / 200k edges.
    """

    nodes: Dict[str, Dict[str, Any]] = field(default_factory=dict)
    out_edges: Dict[str, List[tuple[str, str]]] = field(default_factory=dict)
    in_edges: Dict[str, List[tuple[str, str]]] = field(default_factory=dict)

    def load(self, graph: Dict[str, Any]) -> "TopologyAnalyzer":
        """Load from ast_extract.py or arango_dump.py JSON output."""
        for n in graph.get("nodes", []):
            nid = n.get("id", n.get("_id", ""))
            if nid:
                self.nodes[nid] = n
        for e in graph.get("edges", graph.get("links", [])):
            src = e.get("source", e.get("_from", ""))
            dst = e.get("target", e.get("_to", ""))
            kind = e.get("kind", e.get("type", "references"))
            if src and dst:
                self.out_edges.setdefault(src, []).append((dst, kind))
                self.in_edges.setdefault(dst, []).append((src, kind))
        return self

    # ── causal cone (BFS) ──

    def causal_cone(
        self, seed: str, max_depth: int = 5, direction: str = "downstream"
    ) -> Dict[str, Any]:
        """BFS traversal from seed, returning {nodes: {id: depth}, edges: [...]}."""
        from collections import deque

        visited: Dict[str, int] = {seed: 0}
        edges: List[Dict[str, str]] = []
        q = deque([(seed, 0)])

        while q:
            current, depth = q.popleft()
            if depth >= max_depth:
                continue

            neighbors = (
                self.out_edges.get(current, []) if direction == "downstream"
                else self.in_edges.get(current, [])
            )
            for nxt, kind in neighbors:
                edges.append({"source": current, "target": nxt, "kind": kind})
                if nxt not in visited:
                    visited[nxt] = depth + 1
                    q.append((nxt, depth + 1))

        return {"seed": seed, "nodes": visited, "edges": edges, "direction": direction}

    # ── frontier analysis ──

    def frontier_nodes(self) -> List[Dict[str, Any]]:
        """Nodes with no incoming edges (leaves) or contaminated status."""
        frontier = []
        for nid, node in self.nodes.items():
            role = node.get("role", "")
            indeg = len(self.in_edges.get(nid, []))
            if indeg == 0 or role in ("closure_debt", "contaminated"):
                frontier.append({
                    "id": nid, "name": node.get("name", ""),
                    "kind": node.get("kind", ""),
                    "module": node.get("module", ""),
                    "role": role, "out_degree": len(self.out_edges.get(nid, [])),
                    "in_degree": indeg,
                })
        return sorted(frontier, key=lambda x: -x["out_degree"])

    # ── blast radius ──

    def blast_radius(self, min_upstream: int = 0) -> List[Dict[str, Any]]:
        """For each node, count how many nodes depend on it (upstream cardinality)."""
        results = []
        for nid, node in self.nodes.items():
            if node.get("kind") == "Axiom":
                continue
            # BFS upstream
            visited: Set[str] = set()
            q = [nid]
            while q:
                cur = q.pop()
                for src, _ in self.in_edges.get(cur, []):
                    if src not in visited:
                        visited.add(src)
                        q.append(src)
            if len(visited) >= min_upstream:
                results.append({
                    "id": nid, "name": node.get("name", ""),
                    "kind": node.get("kind", ""), "module": node.get("module", ""),
                    "role": node.get("role", ""),
                    "blast_radius": len(visited),
                })
        return sorted(results, key=lambda x: -x["blast_radius"])

    # ── missing bridge detection ──

    def detect_missing_bridges(self) -> List[Dict[str, Any]]:
        """Find pairs of nodes in disconnected SCCs with shared name tokens.

        These are candidate bridge theorems: theorems that should be connected
        by a dependency edge but are currently in separate components.
        """
        import re

        # Compute weakly connected components
        comp: Dict[str, int] = {}
        comp_id = 0
        for nid in self.nodes:
            if nid in comp:
                continue
            comp_id += 1
            stack = [nid]
            while stack:
                cur = stack.pop()
                if cur in comp:
                    continue
                comp[cur] = comp_id
                for nxt, _ in self.out_edges.get(cur, []):
                    if nxt not in comp:
                        stack.append(nxt)
                for src, _ in self.in_edges.get(cur, []):
                    if src not in comp:
                        stack.append(src)

        # Find cross-component pairs with shared tokens
        candidates = []
        node_list = [(nid, n) for nid, n in self.nodes.items()
                     if n.get("kind") in ("Theorem", "Lemma")]
        for i in range(len(node_list)):
            nid_a, na = node_list[i]
            toks_a = set(re.split(r"[_]+", na.get("name", "").lower()))
            if not toks_a or "" in toks_a:
                continue
            for j in range(i + 1, len(node_list)):
                nid_b, nb = node_list[j]
                if comp.get(nid_a) == comp.get(nid_b):
                    continue  # same component → already connected
                toks_b = set(re.split(r"[_]+", nb.get("name", "").lower()))
                shared = toks_a & toks_b
                if len(shared) >= 2:
                    candidates.append({
                        "node_a": {"id": nid_a, "name": na.get("name", ""),
                                   "module": na.get("module", ""),
                                   "component": comp.get(nid_a)},
                        "node_b": {"id": nid_b, "name": nb.get("name", ""),
                                   "module": nb.get("module", ""),
                                   "component": comp.get(nid_b)},
                        "shared_tokens": sorted(shared),
                    })
        return candidates

    # ── closure score ──

    def closure_score(self) -> Dict[str, Any]:
        """Return counts by role for theory closure assessment."""
        from collections import Counter

        role_counts = Counter(n.get("role", "unknown") for n in self.nodes.values())
        kind_counts = Counter(n.get("kind", "unknown") for n in self.nodes.values())
        total = len(self.nodes)
        clean = role_counts.get("pure_conductor", 0) + role_counts.get("owner", 0) + role_counts.get("translator", 0)
        debt = role_counts.get("closure_debt", 0)
        contaminated = role_counts.get("contaminated", 0)

        return {
            "total": total,
            "by_role": dict(role_counts),
            "by_kind": dict(kind_counts),
            "clean": clean,
            "closure_debt": debt,
            "contaminated": contaminated,
            "pct_clean": round(100 * clean / total, 1) if total else 0,
        }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="AQL Schema + Topology Analysis for Lean DAG theory closure."
    )
    parser.add_argument("--graph", default="artifacts/leantrail/lean_ast_graph.json",
                        help="Input AST graph JSON")
    parser.add_argument("--seed", default=None,
                        help="Node ID for causal cone analysis")
    parser.add_argument("--max-depth", type=int, default=5)
    parser.add_argument("--direction", choices=["downstream", "upstream", "any"],
                        default="downstream")
    parser.add_argument("--frontier", action="store_true",
                        help="Show frontier nodes (leaves / contaminated)")
    parser.add_argument("--blast-radius", action="store_true",
                        help="Compute upstream blast radius for all nodes")
    parser.add_argument("--missing-bridges", action="store_true",
                        help="Detect candidate bridge theorems")
    parser.add_argument("--closure", action="store_true",
                        help="Show theory closure score")
    parser.add_argument("--print-aql", action="store_true",
                        help="Print the AQL query catalog")
    parser.add_argument("--out", default=None)
    return parser.parse_args()


def main() -> int:
    args = _parse_args()

    if args.print_aql:
        aql = AQLQueries()
        print("=== AQL Query Catalog ===\n")
        for name, attr in sorted(type(aql).__dict__.items()):
            if isinstance(attr, property):
                print(f"-- {name} --")
                print(getattr(aql, name))
                print()
        return 0

    graph_path = Path(args.graph)
    if not graph_path.exists():
        print(f"Graph file not found: {graph_path}. Run ast_extract.py first.",
              file=__import__("sys").stderr)
        return 1

    graph = json.loads(graph_path.read_text(encoding="utf-8"))
    ta = TopologyAnalyzer().load(graph)
    print(f"Loaded: {len(ta.nodes)} nodes, {sum(len(v) for v in ta.out_edges.values())} edges")

    result: Any = None

    if args.seed:
        result = ta.causal_cone(args.seed, args.max_depth, args.direction)
        print(f"Cone from '{args.seed}' ({args.direction}): "
              f"{len(result['nodes'])} nodes, {len(result['edges'])} edges")

    if args.frontier:
        frontier = ta.frontier_nodes()
        print(f"\nFrontier nodes: {len(frontier)}")
        for f in frontier[:20]:
            print(f"  [{f['role']:16s}] {f['name']:40s}  {f['module']}"
                  f"  in={f['in_degree']} out={f['out_degree']}")
        result = frontier

    if args.blast_radius:
        br = ta.blast_radius(min_upstream=1)
        print(f"\nBlast radius (top 20):")
        for b in br[:20]:
            print(f"  radius={b['blast_radius']:5d}  [{b['role']:16s}] {b['name']:40s}  {b['module']}")
        result = br

    if args.missing_bridges:
        bridges = ta.detect_missing_bridges()
        print(f"\nCandidate bridges: {len(bridges)}")
        for b in bridges[:20]:
            print(f"  {b['node_a']['name']} ({b['node_a']['module']})"
                  f"  <->  {b['node_b']['name']} ({b['node_b']['module']})"
                  f"  shared: {b['shared_tokens']}")
        result = bridges

    if args.closure:
        score = ta.closure_score()
        print(f"\nTheory closure: {score['pct_clean']}% clean"
              f"  ({score['clean']}/{score['total']})")
        print(f"  by role: {score['by_role']}")
        print(f"  by kind: {score['by_kind']}")
        result = score

    if args.out and result is not None:
        out = Path(args.out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(result if isinstance(result, dict) else list(result),
                                  indent=2, ensure_ascii=True) + "\n")
        print(f"\nSaved: {out}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
