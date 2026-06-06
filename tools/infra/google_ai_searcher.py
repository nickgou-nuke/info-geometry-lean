#!/usr/bin/env python3
"""Google AI Mode literature search via browser_use.

Connects to the existing Chromium (port 9222), searches Google AI Mode
for mathematical literature context, and returns enriched context.

Usage:
    python3 tools/infra/google_ai_searcher.py "Hodge star operator Lean 4 proof"
"""
from __future__ import annotations
import asyncio
import json
import sys
from pathlib import Path

_REPO = Path(__file__).resolve().parents[2]


async def search_google_ai(query: str, cdp_url: str = "http://127.0.0.1:9222") -> dict:
    """Search Google AI Mode and return structured results with references."""
    from browser_use import Agent, Browser, ChatBrowserUse

    browser = Browser(cdp_url=cdp_url)
    task = (
        f"Go to google.com, search for '{query}'. "
        "Read the AI Overview at the top (if present) and the top 5 search results. "
        "Then respond with a JSON object containing: "
        "{summary: <the AI Overview text or top search result summary>, "
        "references: [{title, url, snippet} for each of the top 5 results]}."
    )
    agent = Agent(
        task=task,
        llm=ChatBrowserUse(),
        browser=browser,
        use_vision=False,
    )
    result = await agent.run()

    # Try to parse JSON from the final message
    try:
        final_msg = result.final_result or ""
        # Extract JSON block if present
        import re
        m = re.search(r'\{[\s\S]*\}', final_msg)
        if m:
            return json.loads(m.group())
        return {"summary": final_msg[:2000], "references": []}
    except (json.JSONDecodeError, AttributeError):
        return {"summary": str(result)[:2000], "references": []}


def enrich_context(query: str, context_code: str, cdp_url: str = "http://127.0.0.1:9222") -> str:
    """Enrich Lean proof context with Google AI Mode literature search.

    Blocking wrapper — runs the async search synchronously.
    """
    result = asyncio.run(search_google_ai(query, cdp_url=cdp_url))
    summary = result.get("summary", "")
    refs = result.get("references", [])

    if not summary and not refs:
        return context_code

    parts = [context_code]
    parts.append("\n/* ===== Google AI Mode Literature Context =====")
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
    result = asyncio.run(search_google_ai(query))
    print(json.dumps(result, indent=2))
