#!/usr/bin/env python3
from __future__ import annotations

"""Unified natural-language GraphRAG explorer for the repo.

This is intentionally authority-safe:
- Lean declarations and build artifacts are proof/navigation authority.
- Markdown docs, black books, handovers, and external mirrors are retrieval context.
- External corpora are searched as mirrors only; they are never treated as proofs.
"""

import argparse
import json
import re
import subprocess
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_LEAN_RECORDS = ROOT / "artifacts" / "leansearch_local" / "records.jsonl"
DEFAULT_EXTERNAL_ROOT = ROOT / "external_refs"
DEFAULT_DOC_ROOTS = [ROOT / "docs", ROOT / "handover"]
DEFAULT_BLACKBOOK_ROOTS = [
    ROOT / "docs" / "black_books",
    ROOT / "black_books",
    ROOT / "external_refs" / "black_books",
    ROOT / "external_refs" / "blackbooks",
]
DEFAULT_TEXT_EXTS = {".md", ".txt", ".rst", ".yaml", ".yml"}

TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_']{2,}")


@dataclass(frozen=True)
class Hit:
    source: str
    title: str
    path: str
    score: float
    snippet: str
    metadata: dict[str, Any]


def tokenize(text: str) -> list[str]:
    return [tok.lower() for tok in TOKEN_RE.findall(text)]


def score_text(text: str, qterms: list[str]) -> float:
    low = text.lower()
    score = 0.0
    for term in qterms:
        if term in low:
            score += 1.0 + low.count(term) * 0.25
    return score


def excerpt(text: str, terms: list[str], radius: int = 180) -> str:
    low = text.lower()
    positions = [low.find(term) for term in terms if term in low]
    pos = min((p for p in positions if p >= 0), default=-1)
    if pos < 0:
        return ""
    start = max(0, pos - radius)
    end = min(len(text), pos + radius)
    snippet = text[start:end].strip().replace("\n", " ")
    return re.sub(r"\s+", " ", snippet)


def iter_text_files(root: Path) -> Iterable[Path]:
    if not root.exists():
        return []
    for path in root.rglob("*"):
        if path.is_file() and path.suffix.lower() in DEFAULT_TEXT_EXTS:
            yield path


def search_text_roots(roots: list[Path], query: str, limit: int) -> list[Hit]:
    qterms = tokenize(query)
    hits: list[Hit] = []
    for root in roots:
        if not root.exists():
            continue
        for path in iter_text_files(root):
            try:
                text = path.read_text(encoding="utf-8", errors="ignore")
            except Exception:
                continue
            score = score_text(text, qterms)
            if score <= 0:
                continue
            hits.append(
                Hit(
                    source=root.name,
                    title=path.stem,
                    path=str(path.relative_to(ROOT) if path.is_relative_to(ROOT) else path),
                    score=score,
                    snippet=excerpt(text, qterms),
                    metadata={"root": str(root), "kind": path.suffix.lower()},
                )
            )
    hits.sort(key=lambda h: (-h.score, h.path))
    return hits[:limit]


# [lossless-compact] read_jsonl folded into igf.common.json_io.read_jsonl
from igf.common.json_io import read_jsonl


def search_lean_records(records_path: Path, query: str, limit: int) -> list[Hit]:
    rows = read_jsonl(records_path)
    qterms = tokenize(query)
    hits: list[Hit] = []
    for row in rows:
        search_tokens = " ".join(str(x) for x in row.get("searchTokens", []))
        hay = " ".join(
            str(row.get(key, "")) for key in ("name", "kind", "module", "file", "doc", "type", "snippet")
        )
        score = score_text(search_tokens + " " + hay, qterms)
        if score <= 0:
            continue
        hits.append(
            Hit(
                source="lean",
                title=str(row.get("name") or row.get("module") or "Lean declaration"),
                path=str(row.get("file") or ""),
                score=score,
                snippet=str(row.get("snippet") or row.get("doc") or row.get("type") or ""),
                metadata={
                    "kind": row.get("kind"),
                    "module": row.get("module"),
                    "line": row.get("line"),
                },
            )
        )
    hits.sort(key=lambda h: (-h.score, h.title, h.path))
    return hits[:limit]


def discover_external_mirrors(root: Path) -> list[Path]:
    if not root.exists():
        return []
    mirrors: list[Path] = []
    for child in sorted(root.iterdir()):
        if child.is_dir() and (child / "index.json").exists() and (child / "keyword_index.json").exists():
            mirrors.append(child)
    return mirrors


def discover_external_lean_roots(root: Path, mirrors: list[Path]) -> list[Path]:
    """Find external refs trees that contain Lean sources but no mirror index.

    These are searched as raw Lean text so GraphRAG can surface non-bridged
    external Lean code until a formal mirror index is generated.
    """
    if not root.exists():
        return []
    mirror_set = {m.resolve() for m in mirrors}
    out: list[Path] = []
    for child in sorted(root.iterdir()):
        if not child.is_dir():
            continue
        if child.resolve() in mirror_set:
            continue
        if child.name.startswith('.'):
            continue
        has_lean = False
        for p in child.rglob("*.lean"):
            sp = str(p)
            if "/.lake/" in sp or "/build/" in sp or "/.git/" in sp:
                continue
            has_lean = True
            break
        if has_lean:
            out.append(child)
    return out


def search_external_lean_roots(roots: list[Path], query: str, limit: int) -> list[Hit]:
    qterms = tokenize(query)
    hits: list[Hit] = []
    for root in roots:
        for path in root.rglob("*.lean"):
            sp = str(path)
            if "/.lake/" in sp or "/build/" in sp or "/.git/" in sp:
                continue
            try:
                text = path.read_text(encoding="utf-8", errors="ignore")
            except Exception:
                continue
            score = score_text(text, qterms)
            if score <= 0:
                continue
            rel = str(path.relative_to(ROOT) if path.is_relative_to(ROOT) else path)
            hits.append(
                Hit(
                    source=f"{root.name}-raw-lean",
                    title=path.stem,
                    path=rel,
                    score=score,
                    snippet=excerpt(text, qterms),
                    metadata={"root": str(root), "kind": ".lean", "mode": "raw_external_lean"},
                )
            )
    hits.sort(key=lambda h: (-h.score, h.path))
    return hits[:limit]


def search_external_corpus(corpus_root: Path, query: str, limit: int) -> list[Hit]:
    try:
        index = json.loads((corpus_root / "index.json").read_text(encoding="utf-8"))
        keywords = json.loads((corpus_root / "keyword_index.json").read_text(encoding="utf-8"))
    except Exception:
        return []

    qterms = tokenize(query)
    decls = index.get("declarations", []) if isinstance(index, dict) else []
    kw_rows = keywords.get("termIndex", []) if isinstance(keywords, dict) else []

    bonus_terms = Counter()
    for row in kw_rows:
        if not isinstance(row, dict):
            continue
        term = str(row.get("term") or "").lower()
        if not term:
            continue
        if any(t in term for t in qterms):
            bonus_terms[term] += int(row.get("count", 0) or 0)

    hits: list[Hit] = []
    for decl in decls:
        if not isinstance(decl, dict):
            continue
        hay = " ".join(str(decl.get(k, "")) for k in ("name", "kind", "module", "file", "doc", "type"))
        score = score_text(hay, qterms)
        name = str(decl.get("name") or decl.get("decl") or "")
        if name.lower() in bonus_terms:
            score += 2.0
        if score <= 0:
            continue
        snippet = str(decl.get("doc") or decl.get("type") or "")
        hits.append(
            Hit(
                source=corpus_root.name,
                title=name or str(decl.get("kind") or "external decl"),
                path=str(corpus_root / str(decl.get("file") or "")),
                score=score,
                snippet=snippet[:240],
                metadata={
                    "kind": decl.get("kind"),
                    "line": decl.get("line"),
                    "corpus": str(corpus_root),
                },
            )
        )

    hits.sort(key=lambda h: (-h.score, h.title, h.path))
    return hits[:limit]


def run_gravity(query: str, limit: int) -> dict[str, Any]:
    cmd = [
        "python3",
        str(ROOT / "tools" / "infra" / "arango_gravity_context.py"),
        "--query",
        query,
        "--top-k",
        str(limit),
        "--source",
        "auto",
        "--require-source",
    ]
    proc = subprocess.run(cmd, cwd=ROOT, text=True, capture_output=True)
    if proc.returncode != 0:
        return {
            "ok": False,
            "error": proc.stderr.strip() or proc.stdout.strip() or f"exit {proc.returncode}",
            "command": cmd,
        }
    try:
        payload = json.loads(proc.stdout)
    except Exception:
        return {"ok": False, "error": "gravity output was not valid JSON", "command": cmd, "stdout": proc.stdout[-2000:]}
    return {"ok": True, "command": cmd, "payload": payload}


def format_md_section(title: str, hits: list[Hit]) -> str:
    if not hits:
        return f"## {title}\n\n- no hits\n"
    lines = [f"## {title}", ""]
    for idx, hit in enumerate(hits, start=1):
        lines.append(f"{idx}. **{hit.title}**  ")
        lines.append(f"   - score: `{hit.score:.2f}`")
        lines.append(f"   - source: `{hit.source}`")
        lines.append(f"   - path: `{hit.path}`")
        if hit.snippet:
            lines.append(f"   - excerpt: {hit.snippet}")
        if hit.metadata:
            lines.append(f"   - metadata: `{json.dumps(hit.metadata, ensure_ascii=False)}`")
    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("query", help="Natural-language or keyword query")
    ap.add_argument("--top-k", type=int, default=8)
    ap.add_argument("--lean-records", type=Path, default=DEFAULT_LEAN_RECORDS)
    ap.add_argument("--external-root", type=Path, default=DEFAULT_EXTERNAL_ROOT)
    ap.add_argument("--docs-root", action="append", type=Path, default=[])
    ap.add_argument("--black-books-root", type=Path, default=ROOT / "docs" / "black_books")
    ap.add_argument("--extra-black-books-root", action="append", type=Path, default=[])
    ap.add_argument("--handover-root", type=Path, default=ROOT / "handover")
    ap.add_argument("--no-gravity", action="store_true")
    ap.add_argument("--scope", choices=["all", "lean", "docs", "external", "gravity"], default="all")
    ap.add_argument("--format", choices=["md", "json"], default="md")
    args = ap.parse_args()

    docs_roots = args.docs_root or DEFAULT_DOC_ROOTS
    do_lean = args.scope in {"all", "lean"}
    do_docs = args.scope in {"all", "docs"}
    do_external = args.scope in {"all", "external"}
    do_gravity = args.scope in {"all", "gravity"} and not args.no_gravity

    blackbook_roots: list[Path] = []
    for bb in [args.black_books_root, *DEFAULT_BLACKBOOK_ROOTS, *(args.extra_black_books_root or [])]:
        if bb and bb not in blackbook_roots:
            blackbook_roots.append(bb)

    text_hits = search_text_roots(
        [*(docs_roots or []), *blackbook_roots, args.handover_root],
        args.query,
        args.top_k,
    ) if do_docs else []
    lean_hits = search_lean_records(args.lean_records, args.query, args.top_k) if do_lean else []
    external_hits: list[Hit] = []
    if do_external:
        mirrors = discover_external_mirrors(args.external_root)
        for mirror in mirrors:
            external_hits.extend(search_external_corpus(mirror, args.query, max(1, args.top_k // 2)))
        raw_lean_roots = discover_external_lean_roots(args.external_root, mirrors)
        external_hits.extend(search_external_lean_roots(raw_lean_roots, args.query, max(1, args.top_k // 2)))
        external_hits.sort(key=lambda h: (-h.score, h.title, h.path))
        external_hits = external_hits[: args.top_k]

    gravity = None
    if do_gravity:
        gravity = run_gravity(args.query, args.top_k)

    result = {
        "query": args.query,
        "topK": args.top_k,
        "lean": [hit.__dict__ for hit in lean_hits],
        "docs": [hit.__dict__ for hit in text_hits],
        "external": [hit.__dict__ for hit in external_hits],
        "gravity": gravity,
    }

    if args.format == "json":
        print(json.dumps(result, indent=2, ensure_ascii=False))
        return 0

    print(f"# GraphRAG explorer\n\nQuery: `{args.query}`\n")
    print(format_md_section("Lean declarations", lean_hits))
    print(format_md_section("Docs / black books / handover", text_hits))
    print(format_md_section("External mirrors", external_hits))
    if gravity is not None:
        print("## Gravity context")
        print("")
        if gravity.get("ok"):
            payload = gravity.get("payload", {})
            items = payload.get("items") or []
            print(f"- graph source: `{payload.get('graph_source', 'unknown')}`")
            print(f"- item count: `{len(items)}`")
            for idx, item in enumerate(items[: args.top_k], start=1):
                if not isinstance(item, dict):
                    continue
                name = item.get("name") or item.get("decl") or item.get("id") or "item"
                score = item.get("score") or item.get("weight") or item.get("rank") or "?"
                path = item.get("file") or item.get("path") or ""
                print(f"{idx}. `{name}` score={score} path=`{path}`")
                excerpt = item.get("source_excerpt")
                if isinstance(excerpt, dict):
                    excerpt = excerpt.get("text") or excerpt.get("excerpt")
                if isinstance(excerpt, str) and excerpt:
                    excerpt_line = re.sub(r"\\s+", " ", excerpt)[:240]
                    print(f"   - excerpt: {excerpt_line}")
        else:
            print(f"- unavailable: {gravity.get('error')}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
