#!/usr/bin/env python3
"""
⚖️ HOLLOW SEMANTIC AUDITOR
Detecting symbolic inflation and math-meaningless proofs.

Protocol: "Exploration may be Jungian. Closure must be Pauli."
Goal: Identify theorems that pass the kernel but carry no mathematical content.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
import urllib.request
import urllib.error
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import repo_root
else:
    from tools.pathing import repo_root

ARANGO_URL = os.environ.get("ARANGO_URL", "http://127.0.0.1:8529")
ARANGO_DB = os.environ.get("ARANGO_DB", "infogeometry")

@dataclass
class AuditResult:
    name: str
    depth: int
    kind: str
    doc: str
    statement: str
    is_hollow: bool
    reasoning: str
    confidence: float
    file: str
    line: int

class PauliAuditor:
    def __init__(self, endpoint: str = "http://127.0.0.1:11434/v1"):
        self.endpoint = endpoint.rstrip("/")

    def _query_llm(self, prompt: str, max_tokens: int = 1024) -> str:
        payload = {
            "messages": [{"role": "user", "content": prompt}],
            "temperature": 0.0,
            "max_tokens": max_tokens
        }
        req = urllib.request.Request(
            f"{self.endpoint}/chat/completions",
            data=json.dumps(payload).encode(),
            headers={"Content-Type": "application/json"}
        )
        with urllib.request.urlopen(req, timeout=300) as resp:
            res = json.loads(resp.read().decode())
            return res["choices"][0]["message"]["content"].strip()

    def audit_theorem(self, profile: dict[str, Any]) -> AuditResult:
        name = profile.get("name", "unknown")
        doc = profile.get("doc", "")
        statement = profile.get("statement", "")
        depth = profile.get("depth", 0)
        kind = profile.get("kind", "theorem")
        file = profile.get("file", "")
        line = profile.get("line", 0)

        prompt = f"""You are the Pauli Auditor, an expert in Lean 4 formalization and mathematical physics.
Your task is to detect "hollow" theorems.

DEFINITION:
A declaration is HOLLOW if:
1. The formal proposition is tautological, vacuous (e.g., P -> P), or merely restates a definition.
2. The name or docstring claims a significant mathematical result, but the formal statement is trivial.
3. The formalization "cheats" by using vacuous assumptions.

INPUT THEOREM:
Name: {name}
Kind: {kind}
Depth: {depth}
Docstring: {doc}
Formal Statement: {statement}

TASK:
Determine if this theorem is HOLLOW.
Return a JSON object with:
- "is_hollow": boolean
- "reasoning": string (detailed mathematical critique)
- "confidence": float (0.0 to 1.0)

Output (JSON only):"""

        try:
            content = self._query_llm(prompt)
            # Robust JSON extraction
            json_match = re.search(r"(\{.*?\})", content, re.DOTALL)
            if json_match:
                data = json.loads(json_match.group(0))
                return AuditResult(
                    name=name,
                    depth=depth,
                    kind=kind,
                    doc=doc,
                    statement=statement,
                    is_hollow=data.get("is_hollow", False),
                    reasoning=data.get("reasoning", "No reasoning provided."),
                    confidence=data.get("confidence", 0.0),
                    file=file,
                    line=line
                )
        except Exception as e:
            return AuditResult(
                name=name,
                depth=depth,
                kind=kind,
                doc=doc,
                statement=statement,
                is_hollow=False,
                reasoning=f"Audit failed: {e}",
                confidence=0.0,
                file=file,
                line=line
            )
        
        return AuditResult(
            name=name,
            depth=depth,
            kind=kind,
            doc=doc,
            statement=statement,
            is_hollow=False,
            reasoning="Parse failure.",
            confidence=0.0,
            file=file,
            line=line
        )

def get_candidates(limit: int = 100) -> list[dict[str, Any]]:
    url = f"{ARANGO_URL.rstrip('/')}/_db/{ARANGO_DB}/_api/cursor"
    query = """
    FOR n IN ig_nodes
      FILTER (n.kind == "theorem" || n.kind == "lemma")
      FILTER n.doc != null && LENGTH(n.doc) > 10
      // Extract depth from topology overlay if available
      LET scc_edge = FIRST(FOR e IN topology_overlay_edges FILTER e._from == n._id && e.role == "member_of_scc" RETURN e)
      LET scc = scc_edge != null ? DOCUMENT(scc_edge._to) : null
      LET depth = scc != null ? (scc.depth || 0) : 0
      FILTER depth >= 2
      SORT depth DESC, n.name ASC
      LIMIT @limit
      RETURN {
        name: n.name,
        kind: n.kind,
        doc: n.doc,
        statement: n.statement || "",
        depth: depth,
        file: n.file || "",
        line: n.line || 0
      }
    """
    try:
        body = json.dumps({"query": query, "bindVars": {"limit": limit}}).encode("utf-8")
        req = urllib.request.Request(url, data=body, method="POST")
        req.add_header("Content-Type", "application/json")
        with urllib.request.urlopen(req, timeout=15) as resp:
            out = json.loads(resp.read().decode("utf-8"))
            return out.get("result", [])
    except Exception as e:
        print(f"[pauli-audit] ERROR: Failed to fetch candidates: {e}", file=sys.stderr)
        return []

def write_text_atomic(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)

def render_markdown(results: list[AuditResult], summary: dict[str, Any]) -> str:
    lines = [
        "# Pauli Authority Audit: Hollow Theorems",
        "",
        "> Protocol: Exploration may be Jungian. Closure must be Pauli.",
        "",
        "## Summary",
        f"- **Total Audited**: {summary['total']}",
        f"- **Hollow Detected**: {summary['hollow_count']}",
        f"- **Audit Date**: {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S UTC')}",
        "",
        "## Critical Findings",
        ""
    ]

    hollows = [r for r in results if r.is_hollow]
    if not hollows:
        lines.append("✅ No hollow theorems detected in this pass.")
    else:
        lines.append("| Theorem | Depth | Confidence | Reason |")
        lines.append("| :--- | :---: | :---: | :--- |")
        for r in sorted(hollows, key=lambda x: -x.confidence):
            lines.append(f"| `{r.name}` | {r.depth} | {r.confidence:.2f} | {r.reasoning} |")

    lines.append("\n## Audit Details")
    for r in results:
        status = "❌ HOLLOW" if r.is_hollow else "✅ SOLID"
        lines.extend([
            f"### {r.name} ({status})",
            f"- **Kind**: {r.kind}",
            f"- **Depth**: {r.depth}",
            f"- **Location**: `{r.file}:{r.line}`",
            f"- **Docstring**: {r.doc}",
            f"- **Formal**: `{r.statement}`",
            f"- **Pauli Critique**: {r.reasoning}",
            ""
        ])

    return "\n".join(lines)

def main():
    parser = argparse.ArgumentParser(description="Audit theorems for mathematical 'hollowness'.")
    parser.add_argument("--limit", type=int, default=20, help="Number of theorems to audit.")
    parser.add_argument("--endpoint", default="http://127.0.0.1:11434/v1", help="LLM endpoint.")
    parser.add_argument("--json-out", type=Path, default=Path("reports/dag/hollow-audit.json"))
    parser.add_argument("--md-out", type=Path, default=Path("reports/dag/hollow-audit.md"))
    args = parser.parse_args()

    print(f"[pauli-audit] Fetching up to {args.limit} candidates from ArangoDB...")
    candidates = get_candidates(args.limit)
    if not candidates:
        print("[pauli-audit] No candidates found.")
        return

    auditor = PauliAuditor(endpoint=args.endpoint)
    results: list[AuditResult] = []
    
    print(f"[pauli-audit] Starting audit with Pauli Core at {args.endpoint}...")
    for i, cand in enumerate(candidates):
        print(f"[{i+1}/{len(candidates)}] Auditing {cand['name']}...")
        res = auditor.audit_theorem(cand)
        results.append(res)
        if res.is_hollow:
            print(f"  ⚠️ DETECTED HOLLOW: {res.reasoning[:100]}...")

    summary = {
        "total": len(results),
        "hollow_count": sum(1 for r in results if r.is_hollow),
        "timestamp": datetime.now(timezone.utc).isoformat()
    }

    payload = {
        "summary": summary,
        "results": [asdict(r) for r in results]
    }

    write_text_atomic(args.json_out, json.dumps(payload, indent=2, ensure_ascii=False) + "\n")
    write_text_atomic(args.md_out, render_markdown(results, summary))

    print(f"[pauli-audit] Audit complete. Results saved to {args.md_out}")

if __name__ == "__main__":
    main()
