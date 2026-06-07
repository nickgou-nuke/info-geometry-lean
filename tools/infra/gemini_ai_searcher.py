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
import time
from pathlib import Path

_REPO = Path(__file__).resolve().parents[2]

try:
    from tools.infra.agent_message_ledger import record_message
except Exception:  # pragma: no cover - observation must never block search.
    record_message = None


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
    started = time.monotonic()
    result = await agent.run()

    try:
        final_msg = result.final_result or ""
        import re
        m = re.search(r"\{[\s\S]*\}", final_msg)
        if m:
            parsed = json.loads(m.group())
            if isinstance(parsed, dict):
                if record_message is not None:
                    try:
                        record_message(
                            source_tool="gemini_ai_searcher.py",
                            source_file="tools/infra/gemini_ai_searcher.py",
                            channel="gemini_browser_search",
                            direction="agent_to_model",
                            provider="gemini",
                            model="browser_use/ChatBrowserUse",
                            platform="gemini.google.com",
                            prompt_text=task,
                            response_text=final_msg,
                            success=True,
                            latency_ms=(time.monotonic() - started) * 1000.0,
                            metadata={"query": query},
                        )
                    except Exception:
                        pass
                return parsed
        if record_message is not None:
            try:
                record_message(
                    source_tool="gemini_ai_searcher.py",
                    source_file="tools/infra/gemini_ai_searcher.py",
                    channel="gemini_browser_search",
                    direction="agent_to_model",
                    provider="gemini",
                    model="browser_use/ChatBrowserUse",
                    platform="gemini.google.com",
                    prompt_text=task,
                    response_text=final_msg,
                    success=bool(final_msg),
                    latency_ms=(time.monotonic() - started) * 1000.0,
                    metadata={"query": query, "failure_pattern": "" if final_msg else "empty_response"},
                )
            except Exception:
                pass
        return {"summary": final_msg[:2000], "references": []}
    except (json.JSONDecodeError, AttributeError, TypeError):
        text = str(result)[:2000]
        if record_message is not None:
            try:
                record_message(
                    source_tool="gemini_ai_searcher.py",
                    source_file="tools/infra/gemini_ai_searcher.py",
                    channel="gemini_browser_search",
                    direction="agent_to_model",
                    provider="gemini",
                    model="browser_use/ChatBrowserUse",
                    platform="gemini.google.com",
                    prompt_text=task,
                    response_text=text,
                    success=False,
                    latency_ms=(time.monotonic() - started) * 1000.0,
                    metadata={"query": query, "failure_pattern": "json_parse_error"},
                )
            except Exception:
                pass
        return {"summary": text, "references": []}


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
