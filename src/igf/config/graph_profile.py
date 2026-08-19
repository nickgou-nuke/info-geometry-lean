from __future__ import annotations

from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class GraphCollections:
    compact_nodes: str = "ig_nodes"
    compact_edges: str = "ig_edges"
    raw_nodes: str = "raw_info_nodes"
    raw_edges: str = "raw_info_edges"
    overlay_nodes: str = "topology_overlay"
    overlay_edges: str = "topology_overlay_edges"
    hive_endpoint: str = "http://127.0.0.1:8540"
    hive_database: str = "hive_live"
    hive_thoughts: str = "Thoughts"
    hive_causal_links: str = "CausalLinks"


@dataclass(frozen=True)
class GraphLaneProfile:
    name: str
    retrieval_layer: str
    witness_layer: str | None
    uses_overlay: bool
    include_hive_sidecar: bool
    authority_note: str
    collections: GraphCollections

    def to_dict(self) -> dict[str, object]:
        return {
            "name": self.name,
            "retrieval_layer": self.retrieval_layer,
            "witness_layer": self.witness_layer,
            "uses_overlay": self.uses_overlay,
            "include_hive_sidecar": self.include_hive_sidecar,
            "authority_note": self.authority_note,
            "collections": asdict(self.collections),
        }


_DEFAULT_COLLECTIONS = GraphCollections()

GRAPH_LANE_PROFILES: dict[str, GraphLaneProfile] = {
    "compact": GraphLaneProfile(
        name="compact",
        retrieval_layer="compact_projection",
        witness_layer=None,
        uses_overlay=False,
        include_hive_sidecar=False,
        authority_note=(
            "Compact retrieval projection only: fast navigation over ig_nodes/ig_edges; "
            "not faithful compiler-memory authority."
        ),
        collections=_DEFAULT_COLLECTIONS,
    ),
    "faithful": GraphLaneProfile(
        name="faithful",
        retrieval_layer="raw_dependency",
        witness_layer="raw_dependency",
        uses_overlay=True,
        include_hive_sidecar=False,
        authority_note=(
            "Faithful raw dependency layer with SCC overlay anchoring; Lean source and raw layer remain authority."
        ),
        collections=_DEFAULT_COLLECTIONS,
    ),
    "hybrid": GraphLaneProfile(
        name="hybrid",
        retrieval_layer="compact_projection",
        witness_layer="raw_dependency",
        uses_overlay=True,
        include_hive_sidecar=False,
        authority_note=(
            "Compact projection ranking with raw-layer witness requirement; overlay used for SCC-backed descent."
        ),
        collections=_DEFAULT_COLLECTIONS,
    ),
    "unified": GraphLaneProfile(
        name="unified",
        retrieval_layer="raw_dependency",
        witness_layer="raw_dependency",
        uses_overlay=True,
        include_hive_sidecar=True,
        authority_note=(
            "Canonical unified lane: retrieve from the faithful raw dependency layer, anchor on SCC overlay, "
            "retain compact projection and Hive memory as sidecars only, never as theorem authority."
        ),
        collections=_DEFAULT_COLLECTIONS,
    ),
}

GRAPH_MODE_ALIASES = {
    "layered": "unified",
}

DEFAULT_GRAPH_MODE = "unified"
GRAPH_MODE_CHOICES = tuple(GRAPH_LANE_PROFILES.keys())


def resolve_graph_mode(mode: str | None = None) -> GraphLaneProfile:
    requested = (mode or DEFAULT_GRAPH_MODE).strip().lower()
    requested = GRAPH_MODE_ALIASES.get(requested, requested)
    try:
        return GRAPH_LANE_PROFILES[requested]
    except KeyError as exc:
        allowed = ", ".join(sorted(GRAPH_LANE_PROFILES))
        raise ValueError(f"unknown graph mode '{mode}'; expected one of: {allowed}") from exc
