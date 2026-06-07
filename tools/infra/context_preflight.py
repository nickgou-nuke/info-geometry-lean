#!/usr/bin/env python3
"""Build a bounded, source-grounded context packet before answering repo questions.

The command intentionally searches several independent lanes and labels the
authority of each result. It is a pre-answer guardrail against stale docs,
docstrings, generated reports, and filename-only reasoning.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[2]

REPO_ROOTS = [
    "lean",
    "tools",
    "scripts",
    "src",
    "cli",
    "lakefile.lean",
    "package.json",
    "agent-orchestrator.ts",
    "arango-rag-tool.ts",
    "chatgpt-oracle.ts",
    "commit-conscious-knowledge.ts",
    "lean-prover-tool.ts",
    "setup-db.ts",
    "sympy-witness.ts",
]

COMMON_EXCLUDES = [
    "!external_refs/**",
    "!node_modules/**",
    "!.lake/**",
    "!.runtime/**",
    "!artifacts/**",
    "!reports/**",
    "!paper_node/**",
    "!quarantine/**",
    "!archive/**",
    "!**/__pycache__/**",
    "!**/*.pyc",
]

EXTERNAL_EXCLUDES = [
    "!**/.lake/**",
    "!**/node_modules/**",
    "!**/__pycache__/**",
    "!**/*.pyc",
]

ENTRYPOINT_PATTERN = (
    "script |lean_exe |package_facet |def main|if __name__ == .__main__.|"
    "argparse|process.argv|Bun.argv|name:"
)

GRAPH_PATTERN = (
    "Arango|AQL|GraphRAG|LeanSearch|leansearch|loogle|infotree|decl_graph|"
    "deBruijn|debruijn|embedding|hash|WL|ig_patch|raw_infotree"
)


@dataclass
class Hit:
    path: str
    line: int | None
    text: str
    token: str
    lane: str


def existing_roots(names: Iterable[str]) -> list[str]:
    return [name for name in names if (ROOT / name).exists()]


def query_tokens(query: str, *, limit: int = 10) -> list[str]:
    raw = re.findall(r"[A-Za-z0-9_./:-]{3,}", query)
    out: list[str] = []
    seen: set[str] = set()
    for tok in raw:
        key = tok.lower()
        if key in seen:
            continue
        seen.add(key)
        out.append(tok)
        if len(out) >= limit:
            break
    return out


def run_rg_fixed(
    token: str,
    roots: list[str],
    *,
    excludes: list[str],
    max_hits: int,
) -> list[str]:
    if not roots:
        return []
    cmd = ["rg", "-n", "-i", "--fixed-strings", "--no-heading"]
    for glob in excludes:
        cmd.extend(["--glob", glob])
    cmd.extend([token, *roots])
    try:
        proc = subprocess.run(
            cmd,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            timeout=20,
            check=False,
        )
    except Exception:
        return []
    if proc.returncode not in (0, 1):
        return []
    return proc.stdout.splitlines()[:max_hits]


def run_rg_regex(
    pattern: str,
    roots: list[str],
    *,
    excludes: list[str],
    max_hits: int,
) -> list[str]:
    if not roots:
        return []
    cmd = ["rg", "-n", "-i", "--no-heading"]
    for glob in excludes:
        cmd.extend(["--glob", glob])
    cmd.extend([pattern, *roots])
    try:
        proc = subprocess.run(
            cmd,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            timeout=20,
            check=False,
        )
    except Exception:
        return []
    if proc.returncode not in (0, 1):
        return []
    return proc.stdout.splitlines()[:max_hits]


def parse_rg_line(raw: str, *, token: str, lane: str) -> Hit | None:
    parts = raw.split(":", 2)
    if len(parts) < 3:
        return None
    path, line_raw, text = parts
    try:
        line = int(line_raw)
    except ValueError:
        line = None
    return Hit(path=path, line=line, text=text.strip(), token=token, lane=lane)


def collect_token_hits(
    lane: str,
    tokens: list[str],
    roots: list[str],
    *,
    excludes: list[str],
    max_per_token: int,
) -> list[Hit]:
    hits: list[Hit] = []
    for token in tokens:
        for raw in run_rg_fixed(token, roots, excludes=excludes, max_hits=max_per_token):
            hit = parse_rg_line(raw, token=token, lane=lane)
            if hit is not None:
                hits.append(hit)
    return hits


def collect_pattern_hits(
    lane: str,
    pattern: str,
    roots: list[str],
    *,
    excludes: list[str],
    max_hits: int,
) -> list[Hit]:
    hits: list[Hit] = []
    for raw in run_rg_regex(pattern, roots, excludes=excludes, max_hits=max_hits):
        hit = parse_rg_line(raw, token=pattern, lane=lane)
        if hit is not None:
            hits.append(hit)
    return hits


def summarize_paths(hits: list[Hit], *, limit: int) -> list[dict[str, Any]]:
    counts = Counter(hit.path for hit in hits)
    by_path: dict[str, list[Hit]] = defaultdict(list)
    for hit in hits:
        by_path[hit.path].append(hit)

    out: list[dict[str, Any]] = []
    for path, count in counts.most_common(limit):
        samples = []
        for hit in by_path[path][:3]:
            samples.append(
                {
                    "line": hit.line,
                    "token": hit.token,
                    "text": hit.text[:240],
                }
            )
        out.append({"path": path, "hits": count, "samples": samples})
    return out


def lean_owner_candidates(hits: list[Hit], *, limit: int) -> list[dict[str, Any]]:
    lean_hits = [hit for hit in hits if hit.path.startswith("lean/") and hit.path.endswith(".lean")]
    return summarize_paths(lean_hits, limit=limit)


def tool_candidates(hits: list[Hit], *, limit: int) -> list[dict[str, Any]]:
    tool_hits = [
        hit
        for hit in hits
        if hit.path.startswith(("tools/", "scripts/", "src/", "cli/"))
        or hit.path.endswith(".ts")
        or hit.path in {"lakefile.lean", "package.json"}
    ]
    return summarize_paths(tool_hits, limit=limit)


def artifact_presence() -> dict[str, Any]:
    paths = {
        "dag_decls": "artifacts/dag/index/decls.jsonl",
        "dag_types": "artifacts/dag/index/types.jsonl",
        "leansearch_records": "artifacts/leansearch_local/records.jsonl",
        "dag_manifest": "artifacts/dag/index/manifest.json",
        "raw_infotree_dir": "artifacts/raw_infotree",
    }
    out: dict[str, Any] = {}
    for key, rel in paths.items():
        path = ROOT / rel
        out[key] = {
            "path": rel,
            "exists": path.exists(),
            "size": path.stat().st_size if path.exists() and path.is_file() else None,
        }
    return out


def build_packet(args: argparse.Namespace) -> dict[str, Any]:
    tokens = query_tokens(args.query, limit=args.token_limit)
    repo_roots = existing_roots(REPO_ROOTS)

    repo_hits = collect_token_hits(
        "repo-owned",
        tokens,
        repo_roots,
        excludes=COMMON_EXCLUDES,
        max_per_token=args.max_per_token,
    )
    entrypoint_hits = collect_pattern_hits(
        "entrypoints",
        ENTRYPOINT_PATTERN,
        repo_roots,
        excludes=COMMON_EXCLUDES,
        max_hits=args.max_entrypoints,
    )
    graph_hits = collect_pattern_hits(
        "graph-indexing",
        GRAPH_PATTERN,
        repo_roots,
        excludes=COMMON_EXCLUDES,
        max_hits=args.max_graph_hits,
    )

    external_hits: list[Hit] = []
    if args.include_external and (ROOT / "external_refs").exists():
        external_hits = collect_token_hits(
            "external-ref",
            tokens,
            ["external_refs"],
            excludes=EXTERNAL_EXCLUDES,
            max_per_token=args.max_external_per_token,
        )

    all_repo_context_hits = repo_hits + entrypoint_hits + graph_hits
    return {
        "schema": "info_geometry.context_preflight.v1",
        "query": args.query,
        "tokens": tokens,
        "authority": {
            "lean_source": "proof authority after lake env lean or locked Lake build",
            "graph_rag_arango_leantrail_loogle_sympy": "navigation and evidence only",
            "external_refs": "context only unless explicitly promoted",
            "docs_docstrings_reports": "hints only",
        },
        "artifact_presence": artifact_presence(),
        "observed_in_repo_owned_code": summarize_paths(repo_hits, limit=args.top),
        "entrypoint_surfaces": summarize_paths(entrypoint_hits, limit=args.top),
        "graph_indexing_surfaces": summarize_paths(graph_hits, limit=args.top),
        "lean_owner_candidates": lean_owner_candidates(all_repo_context_hits, limit=args.top),
        "tool_candidates": tool_candidates(all_repo_context_hits, limit=args.top),
        "observed_in_external_refs": summarize_paths(external_hits, limit=args.top),
        "required_next_checks": [
            "Inspect the highest-ranked Lean owner candidates before proof claims.",
            "Run `lake env lean <owner-file>` before saying a theorem is proved.",
            "Run GraphRAG/Arango/LeanTrail/Loogle as navigation, not authority.",
            "Report external_refs separately from repo-owned code.",
            "Name missing or stale docs as maintenance debt instead of filling gaps.",
        ],
    }


def markdown(packet: dict[str, Any]) -> str:
    lines = [
        "# Context Preflight",
        "",
        f"Query: `{packet['query']}`",
        "",
        "## Authority",
    ]
    for key, value in packet["authority"].items():
        lines.append(f"- `{key}`: {value}")

    lines.extend(["", "## Artifact Presence"])
    for key, data in packet["artifact_presence"].items():
        status = "present" if data["exists"] else "missing"
        lines.append(f"- `{key}`: {status} at `{data['path']}`")

    for section, title in [
        ("observed_in_repo_owned_code", "Repo-Owned Code"),
        ("entrypoint_surfaces", "Entrypoints"),
        ("graph_indexing_surfaces", "Graph And Indexing Surfaces"),
        ("lean_owner_candidates", "Lean Owner Candidates"),
        ("tool_candidates", "Tool Candidates"),
        ("observed_in_external_refs", "External Refs"),
    ]:
        lines.extend(["", f"## {title}"])
        rows = packet.get(section) or []
        if not rows:
            lines.append("- no hits")
            continue
        for row in rows:
            lines.append(f"- `{row['path']}` ({row['hits']} hits)")
            for sample in row["samples"][:2]:
                line = sample["line"] if sample["line"] is not None else "?"
                lines.append(f"  - L{line}: {sample['text']}")

    lines.extend(["", "## Required Next Checks"])
    for item in packet["required_next_checks"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("query", help="Question or search phrase to ground before answering")
    parser.add_argument("--include-external", action="store_true", help="Also search external_refs separately")
    parser.add_argument("--json-out", type=Path, help="Write JSON packet to this path")
    parser.add_argument("--markdown-out", type=Path, help="Write Markdown packet to this path")
    parser.add_argument("--json", action="store_true", help="Print JSON instead of Markdown")
    parser.add_argument("--top", type=int, default=12, help="Top paths per section")
    parser.add_argument("--token-limit", type=int, default=10, help="Maximum query tokens to search")
    parser.add_argument("--max-per-token", type=int, default=30, help="Maximum repo hits per token")
    parser.add_argument("--max-external-per-token", type=int, default=20, help="Maximum external hits per token")
    parser.add_argument("--max-entrypoints", type=int, default=120, help="Maximum entrypoint scan hits")
    parser.add_argument("--max-graph-hits", type=int, default=160, help="Maximum graph/index scan hits")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    packet = build_packet(args)

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(packet, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    if args.markdown_out:
        args.markdown_out.parent.mkdir(parents=True, exist_ok=True)
        args.markdown_out.write_text(markdown(packet), encoding="utf-8")

    if args.json:
        print(json.dumps(packet, indent=2, ensure_ascii=True))
    else:
        print(markdown(packet))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
