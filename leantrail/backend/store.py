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

    @staticmethod
    def _structural_dedup_payload(node: NodeRecord) -> dict[str, Any]:
        attrs = node.attrs if isinstance(node.attrs, dict) else {}
        payload = attrs.get("structural_dedup")
        return payload if isinstance(payload, dict) else {}

    @classmethod
    def _dedup_status(cls, node: NodeRecord) -> str:
        payload = cls._structural_dedup_payload(node)
        if not payload:
            return "none"
        subtype = str(payload.get("relation_subtype", "")).strip()
        action = str(payload.get("recommended_action", "")).strip()
        if subtype == "compatibility_alias_candidate" or action == "review_as_alias_family":
            return "suppressed"
        return "active"

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

    def dedup_candidates(self, status: str = "active", limit: int = 50) -> dict[str, Any]:
        normalized = str(status).strip().lower() or "active"
        if normalized not in {"active", "suppressed", "all", "none"}:
            raise ValueError(f"unsupported dedup status: {status}")

        summary = {"active": 0, "suppressed": 0, "none": 0}
        rows: list[dict[str, Any]] = []
        for node in self.snapshot.nodes:
            if node.kind != "Declaration":
                continue
            dedup_status = self._dedup_status(node)
            summary[dedup_status] += 1
            if normalized != "all" and dedup_status != normalized:
                continue
            if normalized == "none" and dedup_status != "none":
                continue
            if dedup_status == "none" and normalized != "none":
                continue
            rows.append(
                {
                    "node": node.to_dict(),
                    "dedup_status": dedup_status,
                    "structural_dedup": self._structural_dedup_payload(node),
                }
            )

        rows.sort(
            key=lambda row: (
                0 if row["dedup_status"] == "active" else 1,
                -int(row["structural_dedup"].get("member_count", 0) or 0),
                str(row["node"].get("name", "")),
            )
        )
        return {"status": normalized, "summary": summary, "results": rows[:limit]}

    def shortest_path(self, src: str, dst: str, lawful_only: bool = True) -> dict[str, Any]:
        return self.shortest_path_with_state_policy(
            src=src,
            dst=dst,
            lawful_only=lawful_only,
            state_policy="any",
        )

    @staticmethod
    def _edge_path_state(edge: EdgeRecord) -> str:
        attrs = edge.attrs if isinstance(edge.attrs, dict) else {}
        state_raw = str(attrs.get("path_state", "")).strip().lower()
        if state_raw in {"failed", "bound", "locked", "meta"}:
            return state_raw
        if edge.kind in {"obstructs", "violates_depth"}:
            return "failed"
        if edge.kind == "contains":
            return "meta"
        return "bound"

    def shortest_path_with_state_policy(
        self,
        src: str,
        dst: str,
        *,
        lawful_only: bool = True,
        state_policy: str = "any",
    ) -> dict[str, Any]:
        if src not in self.node_by_id or dst not in self.node_by_id:
            return {"path": [], "edges": [], "found": False}

        policy = str(state_policy).strip().lower() or "any"
        if policy not in {"any", "exclude-failed", "locked-only"}:
            raise ValueError(f"unsupported state_policy: {state_policy}")

        blocked = {"violates_depth", "obstructs"} if lawful_only else set()
        parent: dict[str, str | None] = {src: None}
        via_edge: dict[str, EdgeRecord] = {}
        q = deque([src])

        found = False
        while q and not found:
            current = q.popleft()
            for edge in self.out_edges.get(current, []):
                if edge.kind == "contains":
                    continue
                if edge.kind in blocked:
                    continue
                edge_state = self._edge_path_state(edge)
                if edge_state == "meta":
                    continue
                if policy == "exclude-failed" and edge_state == "failed":
                    continue
                if policy == "locked-only" and edge_state != "locked":
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
        return {"path": path_nodes, "edges": path_edges, "found": True, "state_policy": policy}

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

    def holonomy_hotspots(
        self,
        limit: int = 25,
        alpha: float = 1.5,
        beta: float = 2.0,
        gamma: float = 3.0,
        min_score: float = 0.0,
    ) -> list[dict[str, Any]]:
        def _as_nonneg_number(value: Any) -> float | None:
            if isinstance(value, (int, float)):
                return float(value) if float(value) >= 0.0 else None
            return None

        rows: list[tuple[float, dict[str, Any]]] = []
        for node in self.snapshot.nodes:
            if node.kind != "Declaration":
                continue

            attrs = node.attrs if isinstance(node.attrs, dict) else {}
            holonomy_attrs = attrs.get("holonomy")
            telemetry = holonomy_attrs if isinstance(holonomy_attrs, dict) else {}

            tactic_steps = _as_nonneg_number(telemetry.get("tactic_steps"))
            context_expansion = _as_nonneg_number(telemetry.get("context_expansion"))
            metavariable_flux = _as_nonneg_number(telemetry.get("metavariable_flux"))
            source = "telemetry"

            if tactic_steps is None or context_expansion is None or metavariable_flux is None:
                source = "proxy"
                outgoing = self.out_edges.get(node.id, [])
                incoming = self.in_edges.get(node.id, [])
                tactic_steps = float(
                    sum(1 for e in outgoing if e.kind in {"depends_type", "depends_value"})
                )
                context_expansion = float(
                    sum(1 for e in incoming if e.kind in {"depends_type", "depends_value"})
                )
                metavariable_flux = float(
                    sum(1 for e in outgoing + incoming if e.kind in {"obstructs", "violates_depth"})
                )
                boundary_class = str(attrs.get("boundary_class", "")).strip().lower()
                if boundary_class in {"boundary", "apex"}:
                    metavariable_flux += 1.0

            holonomy_score = (
                alpha * float(tactic_steps)
                + beta * float(context_expansion)
                + gamma * float(metavariable_flux)
            )
            if holonomy_score < min_score:
                continue

            rows.append(
                (
                    holonomy_score,
                    {
                        "node": node.to_dict(),
                        "holonomy_score": holonomy_score,
                        "components": {
                            "tactic_steps": float(tactic_steps),
                            "context_expansion": float(context_expansion),
                            "metavariable_flux": float(metavariable_flux),
                        },
                        "weights": {"alpha": alpha, "beta": beta, "gamma": gamma},
                        "source": source,
                    },
                )
            )

        rows.sort(key=lambda x: x[0], reverse=True)
        return [row for _, row in rows[:limit]]
