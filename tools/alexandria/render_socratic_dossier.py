#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


def load_packet(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def render_hit(index: int, hit: dict[str, Any]) -> str:
    chunk = hit.get("chunk", {})
    entities = hit.get("entities", [])
    neighbors = hit.get("neighbors", [])
    lines = [
        f"## Hit {index}: {chunk.get('title', '(untitled)')}",
        f"- chunk kind: {chunk.get('chunkKind', 'unknown')}",
        f"- graph score: {hit.get('graphScore', 0):.6f}",
        f"- lexical score: {hit.get('lexicalScore', 0)}",
        f"- source: {chunk.get('provenance', {}).get('path', 'unknown')}#{chunk.get('provenance', {}).get('ordinal', '?')}",
        "",
        "### Text",
        chunk.get("text", ""),
        "",
    ]
    if entities:
        lines.append("### Entities")
        for entity in entities[:12]:
            lines.append(f"- `{entity.get('entityType', 'entity')}`: {entity.get('normalized') or entity.get('surface')}")
        lines.append("")
    if neighbors:
        lines.append("### Nearby context")
        for neighbor in neighbors[:5]:
            lines.append(
                f"- {neighbor.get('chunkKind', 'chunk')} | {neighbor.get('title', '(untitled)')} | {neighbor.get('text', '')[:180]}"
            )
        lines.append("")
    return "\n".join(lines)


def render_dossier(packet: dict[str, Any]) -> str:
    query = packet.get("query", "")
    graph = packet.get("graph", {})
    seeds = packet.get("seeds", [])
    hits = packet.get("hits", [])

    lines = [
        "# Socratic Raw Context Dossier",
        "",
        "## Query",
        query,
        "",
        "## Retrieval substrate",
        f"- node count: {graph.get('nodeCount', 0)}",
        f"- edge count: {graph.get('edgeCount', 0)}",
        f"- GPU requested: {graph.get('useGpuRequested', False)}",
        f"- backend algos: {', '.join(graph.get('backendPriorityAlgos', [])) or 'none'}",
        "",
        "## Seed chunks",
    ]
    for seed in seeds[:10]:
        lines.append(f"- `{seed.get('chunkKey')}` lexical={seed.get('lexicalScore')}" )
    lines.extend([
        "",
        "## Socratic prompts",
        "- Which chunks actually carry theorem statements versus philosophical framing?",
        "- Which hypotheses or support conditions recur across the strongest hits?",
        "- Where does the Drazin/Penrose split become operational rather than rhetorical?",
        "- Which chunks mention certified Lean owner surfaces or module anchors?",
        "",
        "## Ranked context",
        "",
    ])
    for index, hit in enumerate(hits[:12], start=1):
        lines.append(render_hit(index, hit))
    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description="Render a Socratic dossier from an Alexandria context packet")
    ap.add_argument("--input", required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()

    packet = load_packet(Path(args.input))
    rendered = render_dossier(packet)
    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(rendered, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
