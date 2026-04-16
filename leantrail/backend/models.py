from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any


@dataclass
class NodeRecord:
    id: str
    name: str
    kind: str
    module: str
    file: str | None
    line: int | None
    rep_depth: str | None
    role: str | None
    module_family: str | None
    commit_sha: str
    toolchain: str
    artifact_version: int
    attrs: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return {
            "id": self.id,
            "name": self.name,
            "kind": self.kind,
            "module": self.module,
            "file": self.file,
            "line": self.line,
            "rep_depth": self.rep_depth,
            "role": self.role,
            "module_family": self.module_family,
            "commit_sha": self.commit_sha,
            "toolchain": self.toolchain,
            "artifact_version": self.artifact_version,
            "attrs": self.attrs,
        }


@dataclass
class EdgeRecord:
    src: str
    dst: str
    kind: str
    weight: float
    evidence_ref: str
    attrs: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return {
            "src": self.src,
            "dst": self.dst,
            "kind": self.kind,
            "weight": self.weight,
            "evidence_ref": self.evidence_ref,
            "attrs": self.attrs,
        }


@dataclass
class GraphSnapshot:
    metadata: dict[str, Any]
    nodes: list[NodeRecord]
    edges: list[EdgeRecord]

    def to_dict(self) -> dict[str, Any]:
        return {
            "metadata": self.metadata,
            "nodes": [n.to_dict() for n in self.nodes],
            "edges": [e.to_dict() for e in self.edges],
        }

    @staticmethod
    def from_dict(payload: dict[str, Any]) -> "GraphSnapshot":
        nodes = [NodeRecord(**node) for node in payload.get("nodes", [])]
        edges = [EdgeRecord(**edge) for edge in payload.get("edges", [])]
        return GraphSnapshot(metadata=payload.get("metadata", {}), nodes=nodes, edges=edges)
