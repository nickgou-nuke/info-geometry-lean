from __future__ import annotations

from collections import deque
from typing import Any

from .models import EdgeRecord, GraphSnapshot, NodeRecord


class GraphStore:
    def __init__(self, snapshot: GraphSnapshot) -> None:
        self.snapshot = snapshot
        self.node_by_id: dict[str, NodeRecord] = {n.id: n for n in snapshot.nodes}
        self.out_edges: dict[str, list[EdgeRecord]] = {}
        self.in_edges: dict[str, list[EdgeRecord]] = {}

        for edge in snapshot.edges:
            self.out_edges.setdefault(edge.src, []).append(edge)
            self.in_edges.setdefault(edge.dst, []).append(edge)

    def search(self, query: str, limit: int = 50) -> list[dict[str, Any]]:
        q = query.lower().strip()
        if not q:
            return []
        hits: list[NodeRecord] = []
        for node in self.snapshot.nodes:
            hay = f"{node.name} {node.module} {node.kind} {node.module_family or ''}".lower()
            if q in hay:
                hits.append(node)
                if len(hits) >= limit:
                    break
        return [n.to_dict() for n in hits]

    def get_decl(self, name: str) -> dict[str, Any] | None:
        node = self.node_by_id.get(name)
        if node is None:
            return None
        outgoing = [e.to_dict() for e in self.out_edges.get(name, [])]
        incoming = [e.to_dict() for e in self.in_edges.get(name, [])]
        return {
            "node": node.to_dict(),
            "outgoing": outgoing,
            "incoming": incoming,
        }

    def neighborhood(self, center: str, radius: int = 2, limit_nodes: int = 1500) -> dict[str, Any]:
        if center not in self.node_by_id:
            return {"nodes": [], "edges": []}

        visited = {center}
        q = deque([(center, 0)])
        edge_keys: set[tuple[str, str, str]] = set()

        while q and len(visited) < limit_nodes:
            current, dist = q.popleft()
            if dist >= radius:
                continue

            for edge in self.out_edges.get(current, []):
                edge_keys.add((edge.src, edge.dst, edge.kind))
                if edge.dst not in visited:
                    visited.add(edge.dst)
                    q.append((edge.dst, dist + 1))
            for edge in self.in_edges.get(current, []):
                edge_keys.add((edge.src, edge.dst, edge.kind))
                if edge.src not in visited:
                    visited.add(edge.src)
                    q.append((edge.src, dist + 1))

        nodes = [self.node_by_id[nid].to_dict() for nid in visited if nid in self.node_by_id]
        edges = [
            e.to_dict()
            for e in self.snapshot.edges
            if (e.src, e.dst, e.kind) in edge_keys and e.src in visited and e.dst in visited
        ]
        return {"nodes": nodes, "edges": edges}

    def shortest_path(self, src: str, dst: str, lawful_only: bool = True) -> dict[str, Any]:
        if src not in self.node_by_id or dst not in self.node_by_id:
            return {"path": [], "edges": [], "found": False}

        blocked = {"violates_depth", "obstructs"} if lawful_only else set()
        parent: dict[str, str | None] = {src: None}
        via_edge: dict[str, EdgeRecord] = {}
        q = deque([src])

        found = False
        while q and not found:
            current = q.popleft()
            for edge in self.out_edges.get(current, []):
                if edge.kind in blocked:
                    continue
                nxt = edge.dst
                if nxt in parent:
                    continue
                parent[nxt] = current
                via_edge[nxt] = edge
                if nxt == dst:
                    found = True
                    break
                q.append(nxt)

        if dst not in parent:
            return {"path": [], "edges": [], "found": False}

        path_nodes: list[str] = []
        path_edges: list[dict[str, Any]] = []
        cur = dst
        while cur is not None:
            path_nodes.append(cur)
            edge = via_edge.get(cur)
            if edge is not None:
                path_edges.append(edge.to_dict())
            cur = parent[cur]

        path_nodes.reverse()
        path_edges.reverse()
        return {"path": path_nodes, "edges": path_edges, "found": True}

    def coherence_hotspots(self, limit: int = 25) -> list[dict[str, Any]]:
        rows: list[tuple[float, dict[str, Any]]] = []
        for node in self.snapshot.nodes:
            outgoing = self.out_edges.get(node.id, [])
            translator_count = sum(1 for e in outgoing if e.kind in {"translator_of", "coheres_with"})
            violation_count = sum(1 for e in outgoing if e.kind in {"violates_depth", "obstructs"})
            dependency_count = sum(1 for e in outgoing if e.kind in {"depends_type", "depends_value"})

            if translator_count == 0 and violation_count == 0:
                continue

            score = float(2 * translator_count + 5 * violation_count + 0.05 * dependency_count)
            rows.append(
                (
                    score,
                    {
                        "node": node.to_dict(),
                        "score": score,
                        "translator_edges": translator_count,
                        "violation_edges": violation_count,
                        "dependency_edges": dependency_count,
                    },
                )
            )

        rows.sort(key=lambda x: x[0], reverse=True)
        return [row for _, row in rows[:limit]]
