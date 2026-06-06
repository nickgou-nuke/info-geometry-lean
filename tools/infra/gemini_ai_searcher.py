#!/usr/bin/env python3
"""Gemini AI literature search via browser_use.

Connects to the existing Chromium (port 9222), searches Gemini for
mathematical literature context, and returns enriched context.

Usage:
    python3 tools/infra/gemini_ai_searcher.py "Hodge star operator Lean 4 proof"
"""
from __future__ import annotations

import asyncio
import json
import sys
from pathlib import Path

_REPO = Path(__file__).resolve().parents[2]


async def search_gemini_ai(query: str, cdp_url: str = "http://127.0.0.1:9222") -> dict:
    """Search Gemini and return structured results with references."""
    from browser_use import Agent, Browser, ChatBrowserUse

    browser = Browser(cdp_url=cdp_url)
    task = (
        f"Go to gemini.google.com and search for '{query}'. "
        "Read the response carefully and extract the top relevant mathematical "
        "claims, proof ideas, and literature references. "
        "Then respond with a JSON object containing: "
        "{summary: <the best concise summary>, "
        "references: [{title, url, snippet} for each referenced source]}"
    )
    agent = Agent(
        task=task,
        llm=ChatBrowserUse(),
        browser=browser,
        use_vision=False,
    )
    result = await agent.run()

    try:
        final_msg = result.final_result or ""
        import re
        m = re.search(r"\{[\s\S]*\}", final_msg)
        if m:
            parsed = json.loads(m.group())
            if isinstance(parsed, dict):
                return parsed
        return {"summary": final_msg[:2000], "references": []}
    except (json.JSONDecodeError, AttributeError, TypeError):
        return {"summary": str(result)[:2000], "references": []}


def enrich_context(query: str, context_code: str, cdp_url: str = "http://127.0.0.1:9222") -> str:
    """Enrich Lean proof context with Gemini literature search."""
    result = asyncio.run(search_gemini_ai(query, cdp_url=cdp_url))
    summary = result.get("summary", "")
    refs = result.get("references", [])

    if not summary and not refs:
        return context_code

    parts = [context_code]
    parts.append("\n/* ===== Gemini AI Literature Context =====")
    parts.append(summary[:2000])
    if refs:
        parts.append("--- References ---")
        for i, r in enumerate(refs[:5], 1):
            title = r.get("title", "")[:150]
            url = r.get("url", "")
            snippet = r.get("snippet", "")[:200]
            parts.append(f"[{i}] {title} — {url}")
            if snippet:
                parts.append(f"    {snippet}")
    parts.append("===== End Literature Context ===== */\n")
    return "\n".join(parts)


if __name__ == "__main__":
    query = sys.argv[1] if len(sys.argv) > 1 else "Hodge star operator Lean 4 proof"
    result = asyncio.run(search_gemini_ai(query))
    print(json.dumps(result, indent=2))
