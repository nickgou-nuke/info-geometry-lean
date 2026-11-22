#!/usr/bin/env python3
"""Unified natural-language GraphRAG explorer for the repo.

This is intentionally authority-safe:
- Lean declarations and build artifacts are proof/navigation authority.
- Markdown docs, black books, handovers, and external mirrors are retrieval context.
- External corpora are searched as mirrors only; they are never treated as proofs.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable
from urllib.error import URLError

ROOT = Path(__file__).resolve().parents[2]
for _path in (str(ROOT), str(ROOT / "src")):
    if _path not in sys.path:
        sys.path.insert(0, _path)

VALID_SCOPES = frozenset({"all", "lean", "docs", "external", "gravity", "alexandria"})
ALEXANDRIA_AUTHORITY = "retrieval_context_only"
ALEXANDRIA_DISCLAIMER = "Alexandria PDF results are retrieval context only; NOT verified Lean proof evidence."
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
from igf.common.json_io import read_jsonl  # noqa: E402


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


def parse_scopes(raw: str) -> tuple[str, ...]:
    parts = [part.strip().lower() for part in str(raw).split(",") if part.strip()]
    if not parts:
        raise argparse.ArgumentTypeError("scope must not be empty")
    invalid = [part for part in parts if part not in VALID_SCOPES]
    if invalid:
        allowed = ", ".join(sorted(VALID_SCOPES))
        raise argparse.ArgumentTypeError(f"invalid scope(s): {', '.join(invalid)} (choose from {allowed})")
    deduped: list[str] = []
    for part in parts:
        if part not in deduped:
            deduped.append(part)
    return tuple(deduped)


def search_alexandria(
    query: str,
    limit: int,
    *,
    endpoint: str | None = None,
    database: str | None = None,
) -> list[Hit]:
    from tools.alexandria.retrieve_context import retrieve_arango_context

    packet = retrieve_arango_context(
        query,
        endpoint=endpoint,
        database=database,
        top_k=limit,
        hops=1,
    )
    qterms = tokenize(query)
    hits: list[Hit] = []
    for row in packet.get("hits", []):
        if not isinstance(row, dict):
            continue
        chunk = row.get("chunk") if isinstance(row.get("chunk"), dict) else {}
        doc = row.get("document") if isinstance(row.get("document"), dict) else {}
        prov = chunk.get("provenance") if isinstance(chunk.get("provenance"), dict) else {}
        path = str(row.get("path") or prov.get("path") or doc.get("path") or "")
        title = str(
            row.get("title")
            or doc.get("title")
            or chunk.get("title")
            or (Path(path).name if path else "")
            or "Alexandria PDF chunk"
        )
        text = str(chunk.get("text") or "")
        snippet = excerpt(text, qterms) or re.sub(r"\s+", " ", text).strip()[:280]
        entities = [
            {
                "surface": e.get("surface"),
                "normalized": e.get("normalized"),
                "entityType": e.get("entityType"),
            }
            for e in (row.get("entities") or [])[:8]
            if isinstance(e, dict)
        ]
        dag_neighbors = [
            {
                "_key": d.get("_key"),
                "edgeType": d.get("edgeType"),
                "direction": d.get("direction"),
                "chunkKind": d.get("chunkKind"),
                "title": d.get("title"),
                "surface": d.get("surface"),
            }
            for d in (row.get("dagNeighbors") or [])[:6]
            if isinstance(d, dict)
        ]
        hits.append(
            Hit(
                source="alexandria",
                title=title,
                path=path,
                score=float(row.get("score") or 0.0),
                snippet=snippet,
                metadata={
                    "authority": ALEXANDRIA_AUTHORITY,
                    "sourceAuthority": ALEXANDRIA_AUTHORITY,
                    "documentKey": row.get("documentKey") or chunk.get("documentKey"),
                    "chunkKey": row.get("chunkKey") or chunk.get("_key"),
                    "chunkKind": row.get("chunkKind") or chunk.get("chunkKind"),
                    "contentHash": row.get("contentHash") or prov.get("contentHash") or doc.get("contentHash"),
                    "pageStart": row.get("pageStart") if row.get("pageStart") is not None else prov.get("pageStart"),
                    "pageEnd": row.get("pageEnd") if row.get("pageEnd") is not None else prov.get("pageEnd"),
                    "section": prov.get("section"),
                    "entities": entities,
                    "dagNeighbors": dag_neighbors,
                },
            )
        )
    return hits


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
    ap.add_argument(
        "--scope",
        type=parse_scopes,
        default="all",
        help="Scope(s): all, lean, docs, external, gravity, alexandria (comma-separated allowed)",
    )
    ap.add_argument("--alexandria-endpoint", default=None)
    ap.add_argument("--alexandria-database", default=None)
    ap.add_argument("--format", choices=["md", "json"], default="md")
    args = ap.parse_args()
    if args.top_k < 0:
        ap.error("--top-k must be >= 0")

    scopes = parse_scopes(args.scope) if isinstance(args.scope, str) else args.scope
    scope_str = ",".join(scopes)
    has_all = "all" in scopes
    docs_roots = args.docs_root or DEFAULT_DOC_ROOTS
    do_lean = has_all or ("lean" in scopes)
    do_docs = has_all or ("docs" in scopes)
    do_external = has_all or ("external" in scopes)
    do_gravity = (has_all or ("gravity" in scopes)) and not args.no_gravity
    do_alexandria = "alexandria" in scopes

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

    alexandria_hits: list[Hit] = []
    if do_alexandria:
        try:
            alexandria_hits = search_alexandria(
                args.query,
                args.top_k,
                endpoint=args.alexandria_endpoint,
                database=args.alexandria_database,
            )
        except ValueError as exc:
            print(json.dumps({"error": str(exc)}, ensure_ascii=False), file=sys.stderr)
            return 2
        except (URLError, OSError, RuntimeError) as exc:
            print(json.dumps({"error": f"Alexandria query failed: {exc}"}, ensure_ascii=False), file=sys.stderr)
            return 1

    gravity = None
    if do_gravity:
        gravity = run_gravity(args.query, args.top_k)

    result: dict[str, Any] = {
        "query": args.query,
        "topK": args.top_k,
        "scope": scope_str,
        "lean": [hit.__dict__ for hit in lean_hits],
        "docs": [hit.__dict__ for hit in text_hits],
        "external": [hit.__dict__ for hit in external_hits],
        "alexandria": [hit.__dict__ for hit in alexandria_hits],
        "gravity": gravity,
        "authorities": {
            "lean": "proof_or_navigation_authority",
            "docs": "retrieval_context_only",
            "external": "search_only_mirror",
            "alexandria": ALEXANDRIA_AUTHORITY,
        },
    }
    if do_alexandria and not do_lean:
        result["authority"] = ALEXANDRIA_AUTHORITY
        result["disclaimer"] = ALEXANDRIA_DISCLAIMER

    if args.format == "json":
        print(json.dumps(result, indent=2, ensure_ascii=False))
        return 0

    print(f"# GraphRAG explorer\n\nQuery: `{args.query}`\n")
    print(format_md_section("Lean declarations", lean_hits))
    print(format_md_section("Docs / black books / handover", text_hits))
    print(format_md_section("External mirrors", external_hits))
    if do_alexandria:
        print(format_md_section("Alexandria PDFs (retrieval_context_only — not verified Lean proof evidence)", alexandria_hits))
        print(f"Authority: `{ALEXANDRIA_AUTHORITY}` — {ALEXANDRIA_DISCLAIMER}\n")
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
