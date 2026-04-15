#!/usr/bin/env python3
"""Minimal search/fetch MCP datasource for OpenAI Deep Research.

This file is a template for the *nested* MCP server used by deep-research jobs.
It is not the Codex-facing gateway.

Contract:
- `search(query)` returns exactly one MCP text content item with JSON payload:
  {"results": [{"id": ..., "title": ..., "url": ...}, ...]}
- `fetch(id)` returns exactly one MCP text content item with JSON payload:
  {"id": ..., "title": ..., "text": ..., "url": ..., "metadata": {...}}
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[2]))

try:
    from fastmcp import FastMCP
except Exception as exc:  # pragma: no cover - runtime dependency guard
    raise SystemExit("Missing dependency: fastmcp (pip install fastmcp)") from exc

mcp = FastMCP(
    name="deep-research-datasource-template",
    instructions="Search and fetch internal documents for deep-research jobs.",
)

# Replace this with your real storage/search backend.
DOCS: dict[str, dict[str, Any]] = {
    "doc-1": {
        "title": "Example internal note",
        "text": "Full document content goes here.",
        "url": "https://example.internal/doc-1",
        "metadata": {"source": "internal", "team": "research"},
    }
}


def _json_text(payload: dict[str, Any]) -> dict[str, list[dict[str, str]]]:
    return {
        "content": [
            {
                "type": "text",
                "text": json.dumps(payload, ensure_ascii=False),
            }
        ]
    }


@mcp.tool()
def search(query: str) -> dict[str, list[dict[str, str]]]:
    q = query.strip().lower()
    if not q:
        return _json_text({"results": []})

    results: list[dict[str, str]] = []
    for doc_id, doc in DOCS.items():
        haystack = f"{doc.get('title', '')}\n{doc.get('text', '')}".lower()
        if q in haystack:
            results.append(
                {
                    "id": doc_id,
                    "title": str(doc.get("title", doc_id)),
                    "url": str(doc.get("url", "")),
                }
            )

    return _json_text({"results": results})


@mcp.tool()
def fetch(id: str) -> dict[str, list[dict[str, str]]]:
    doc_id = id.strip()
    if not doc_id:
        raise ValueError("id must be non-empty")
    if doc_id not in DOCS:
        raise KeyError(f"unknown document id: {doc_id}")

    doc = DOCS[doc_id]
    payload = {
        "id": doc_id,
        "title": str(doc.get("title", doc_id)),
        "text": str(doc.get("text", "")),
        "url": str(doc.get("url", "")),
        "metadata": doc.get("metadata", {}),
    }
    return _json_text(payload)


if __name__ == "__main__":
    mcp.run()
