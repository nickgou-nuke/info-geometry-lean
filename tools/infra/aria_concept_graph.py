#!/usr/bin/env python3
"""Aria-style concept graph builder over local LeanSearch records.

This is a planning/grounding artifact, not proof authority.  It borrows Aria's
useful shape:

    informal claim -> concept graph -> local LeanSearch grounding candidates

and keeps the first implementation deterministic and local.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra.leansearch_local import DEFAULT_RECORDS, search_records, tokenize


SCHEMA = "info_geometry.aria_concept_graph.v1"
CONCEPT_STATUSES = {"unexplored", "exploring", "grounded", "synthesized", "failed", "unresolved"}
STOPWORDS = {
    "about",
    "after",
    "against",
    "also",
    "and",
    "are",
    "between",
    "but",
    "can",
    "each",
    "every",
    "for",
    "from",
    "has",
    "have",
    "into",
    "only",
    "over",
    "that",
    "the",
    "then",
    "there",
    "this",
    "through",
    "under",
    "when",
    "where",
    "with",
}


def slug(text: str) -> str:
    out = re.sub(r"[^A-Za-z0-9]+", "_", text.strip().lower()).strip("_")
    return out[:64] or "concept"


def normalize_phrase(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def concept_kind(phrase: str) -> str:
    low = phrase.lower()
    if any(tok in low for tok in ("theorem", "lemma", "implies", "iff", "if and only if")):
        return "theorem"
    if any(tok in low for tok in ("structure", "class", "space", "algebra", "module", "group", "ring")):
        return "structure"
    if any(tok in low for tok in ("operator", "map", "function", "morphism", "transform")):
        return "operator"
    return "definition"


@dataclass
class ConceptNode:
    name: str
    status: str = "unexplored"
    dependencies: list[str] = field(default_factory=list)
    formal_code: str | None = None
    error_message: str | None = None
    informal_description: str | None = None
    retrieval: list[dict[str, Any]] = field(default_factory=list)

    def to_packet(self, *, index: int) -> dict[str, Any]:
        return {
            "id": f"concept:{slug(self.name)}",
            "index": index,
            "text": self.name,
            "kind": concept_kind(self.name),
            "status": self.status,
            "dependencies": [f"concept:{slug(dep)}" for dep in self.dependencies],
            "formal_code": self.formal_code,
            "error_message": self.error_message,
            "informal_description": self.informal_description,
            "retrieval": self.retrieval,
        }


@dataclass
class DependencyGraph:
    nodes: dict[str, ConceptNode] = field(default_factory=dict)

    def add_concept(self, name: str, informal_description: str | None = None) -> ConceptNode:
        if name not in self.nodes:
            self.nodes[name] = ConceptNode(name=name, informal_description=informal_description)
        elif informal_description:
            self.nodes[name].informal_description = informal_description
        return self.nodes[name]

    def add_dependency(self, parent_concept: str, child_concept: str) -> None:
        parent = self.add_concept(parent_concept)
        self.add_concept(child_concept)
        if child_concept not in parent.dependencies:
            parent.dependencies.append(child_concept)

    def get_next_unexplored_leaf(self) -> ConceptNode | None:
        for node in self.nodes.values():
            if node.status == "unexplored" and all(
                self.nodes[dep].status != "unexplored" for dep in node.dependencies if dep in self.nodes
            ):
                return node
        return None

    def get_ready_to_synthesize_node(self) -> ConceptNode | None:
        for node in self.nodes.values():
            if node.status == "exploring" and node.dependencies and all(
                self.nodes[dep].status in {"grounded", "synthesized"} for dep in node.dependencies if dep in self.nodes
            ):
                return node
        return None

    def is_complete(self, target_concept: str) -> bool:
        return target_concept in self.nodes and self.nodes[target_concept].status in {"grounded", "synthesized"}


def extract_concepts(claim: str, *, max_concepts: int = 12) -> list[str]:
    """Extract deterministic noun-ish concept phrases from a mathematical claim.

    This is intentionally modest.  Later we can swap in an LLM concept
    decomposer while preserving this output schema.
    """
    chunks = re.split(r"[,.;:()\[\]{}]|->|→|=>|⇒|\\to|\\Rightarrow", claim)
    candidates: list[str] = []
    seen: set[str] = set()
    for chunk in chunks:
        words = [
            tok
            for tok in tokenize(chunk)
            if tok not in STOPWORDS and not tok.isdigit() and len(tok) > 2
        ]
        if not words:
            continue
        # Use short adjacent phrases first, then the whole cleaned chunk if
        # it remains compact.
        phrases: list[str] = []
        if words:
            phrases.append(words[0])
        if len(words) <= 4:
            phrases.append(" ".join(words))
        for size in (3, 2):
            for i in range(1, max(len(words) - size + 1, 0)):
                phrases.append(" ".join(words[i : i + size]))
        phrases.extend(words[1:])
        for phrase in phrases:
            phrase = normalize_phrase(phrase)
            key = phrase.lower()
            if key in seen:
                continue
            seen.add(key)
            candidates.append(phrase)
            if len(candidates) >= max_concepts:
                return candidates
    return candidates


def concept_edges(concepts: list[str]) -> list[dict[str, str]]:
    """Create a simple dependency chain from earlier concepts to later ones."""
    edges: list[dict[str, str]] = []
    for idx in range(len(concepts) - 1):
        edges.append(
            {
                "from": f"concept:{slug(concepts[idx])}",
                "to": f"concept:{slug(concepts[idx + 1])}",
                "role": "heuristic_prerequisite",
            }
        )
    return edges


def build_dependency_graph(concepts: list[str]) -> DependencyGraph:
    graph = DependencyGraph()
    for concept in concepts:
        graph.add_concept(concept)
    for idx in range(len(concepts) - 1):
        graph.add_dependency(concepts[idx + 1], concepts[idx])
    return graph


def ground_concept(phrase: str, *, records: Path, top_k: int, min_score: float) -> tuple[str, list[dict[str, Any]]]:
    result = search_records(records_path=records, query=phrase, top_k=top_k)
    retrieval = []
    for hit in result.get("hits") or []:
        if not isinstance(hit, dict):
            continue
        score = float(hit.get("score") or 0.0)
        retrieval.append(
            {
                "name": hit.get("name"),
                "kind": hit.get("kind"),
                "module": hit.get("module"),
                "file": hit.get("file"),
                "line": hit.get("line"),
                "score": score,
                "scoreBreakdown": hit.get("scoreBreakdown") or {},
                "doc": hit.get("doc"),
                "type": hit.get("type"),
            }
        )
    status = "grounded" if retrieval and float(retrieval[0].get("score") or 0.0) >= min_score else "unresolved"
    return status, retrieval


def build_concept_graph(
    *,
    claim: str,
    records: Path,
    top_k: int = 5,
    max_concepts: int = 12,
    min_grounding_score: float = 1.0,
) -> dict[str, Any]:
    concepts = extract_concepts(claim, max_concepts=max_concepts)
    dep_graph = build_dependency_graph(concepts)
    nodes = []
    for idx, phrase in enumerate(concepts):
        status, retrieval = ground_concept(
            phrase,
            records=records,
            top_k=top_k,
            min_score=min_grounding_score,
        )
        node = dep_graph.nodes[phrase]
        node.status = status
        node.retrieval = retrieval
        if status == "grounded" and retrieval:
            best = retrieval[0]
            node.formal_code = f"/- Grounded as {best.get('name')} ({best.get('kind')}) -/"
        nodes.append(node.to_packet(index=idx))
    edges = [
        {
            "from": f"concept:{slug(dep)}",
            "to": f"concept:{slug(parent)}",
            "role": "aria_dependency",
        }
        for parent in concepts
        for dep in dep_graph.nodes[parent].dependencies
    ]
    return {
        "schema": SCHEMA,
        "claim": claim,
        "records": str(records),
        "node_count": len(nodes),
        "edge_count": len(edges),
        "nodes": nodes,
        "edges": edges,
        "aria_model": {
            "concept_statuses": sorted(CONCEPT_STATUSES),
            "top_down_grounding": True,
            "bottom_up_synthesis_readiness": True,
            "graph_shape_source": "frenzymath/Aria-autoformalizer ConceptNode/DependencyGraph adapted locally",
        },
        "authority": {
            "graph_is_planning_prior": True,
            "retrieval_is_grounding_prior": True,
            "lean_remains_proof_authority": True,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--claim", required=True)
    parser.add_argument("--records", type=Path, default=DEFAULT_RECORDS)
    parser.add_argument("--top-k", type=int, default=5)
    parser.add_argument("--max-concepts", type=int, default=12)
    parser.add_argument("--min-grounding-score", type=float, default=1.0)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    payload = build_concept_graph(
        claim=args.claim,
        records=args.records,
        top_k=args.top_k,
        max_concepts=args.max_concepts,
        min_grounding_score=args.min_grounding_score,
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"out": str(args.out), "nodes": payload["node_count"], "edges": payload["edge_count"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
