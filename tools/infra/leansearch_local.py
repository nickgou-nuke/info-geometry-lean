#!/usr/bin/env python3
"""Dependency-free LeanSearch-style retrieval over local DAG declaration artifacts.

This is not a replacement for LeanSearch.  It borrows the useful shape:

    Lean declaration records -> searchable text -> ranked retrieval results

and keeps the first implementation local, deterministic, and authority-safe.
Embedding models, informal-description generation, or Arango-backed retrieval can
be added later behind the same record schema.
"""

from __future__ import annotations

import argparse
import json
import math
import re
from collections import Counter
from pathlib import Path
from typing import Any, Iterable


DEFAULT_DECLS = Path("artifacts/dag/index/decls.jsonl")
DEFAULT_TYPES = Path("artifacts/dag/index/types.jsonl")
DEFAULT_RECORDS = Path("artifacts/leansearch_local/records.jsonl")

TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_']{1,}")
IDENTIFIER_CHAR_RE = re.compile(r"[^a-z0-9]+")
LEAN_DECL_RE = re.compile(
    r"^\s*(?:(?:@[^\n]*)\s*)*"
    r"(?:(?:private|protected|partial|unsafe|noncomputable|opaque)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|axiom|constant|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)


def tokenize(text: str) -> list[str]:
    return [tok.lower() for tok in TOKEN_RE.findall(text)]


def split_name_tokens(name: str) -> list[str]:
    pieces = re.sub(r"([a-z])([A-Z])", r"\1 \2", name.replace(".", " ").replace("_", " "))
    return tokenize(pieces)


def _unique_preserving_order(tokens: Iterable[str]) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for tok in tokens:
        if tok in seen:
            continue
        seen.add(tok)
        out.append(tok)
    return out


def query_tokens(query: str) -> list[str]:
    """Tokenize user queries using both prose and Lean identifier splitting.

    Declaration records store split Lean names (`tensorFactorSeparation` becomes
    `tensor factor separation`). Queries must receive the same expansion or
    exact Lean-style names become invisible to the lexical scorer.
    """

    return _unique_preserving_order(tokenize(query) + split_name_tokens(query))


def normalize_identifier_text(text: str) -> str:
    return IDENTIFIER_CHAR_RE.sub("", text.lower())


def iter_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    if not path.exists():
        return
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except Exception:
                continue
            if isinstance(row, dict):
                yield row


def load_types(path: Path) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in iter_jsonl(path):
        name = str(row.get("declName") or row.get("name") or "").strip()
        if name and name not in out:
            out[name] = row
    return out


def source_snippet(file_path: str, line: int | None, *, radius: int, max_chars: int) -> str:
    if line is None:
        return ""
    path = Path(file_path)
    if not path.exists():
        return ""
    try:
        lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
    except Exception:
        return ""
    if not lines:
        return ""
    idx = max(0, line - 1)
    start = max(0, idx - radius)
    stop = min(len(lines), idx + radius + 1)
    snippet = "\n".join(lines[start:stop]).strip()
    if max_chars > 0 and len(snippet) > max_chars:
        return snippet[: max_chars - 3] + "..."
    return snippet


def module_name_from_path(path: Path, source_roots: list[Path]) -> str:
    path_resolved = path.resolve()
    for root in source_roots:
        try:
            rel = path_resolved.relative_to(root.resolve())
        except ValueError:
            continue
        return ".".join(rel.with_suffix("").parts)
    return path.with_suffix("").name


def iter_source_decls(source_roots: list[Path]) -> Iterable[dict[str, Any]]:
    """Yield declaration records from Lean source roots without using comments as truth.

    This mode is only a navigation fallback for external or spin-off trees that
    do not have DAG `decls.jsonl` / `types.jsonl` artifacts yet.  The records are
    source-derived and must still be verified with `lake env lean` before use.
    """

    roots = [root.resolve() for root in source_roots]
    for root in roots:
        if root.is_file() and root.suffix == ".lean":
            candidates = [root]
        elif root.is_dir():
            candidates = sorted(root.rglob("*.lean"))
        else:
            continue
        for path in candidates:
            try:
                lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
            except Exception:
                continue
            module = module_name_from_path(path, roots)
            namespace_stack: list[str] = []
            for line_no, line in enumerate(lines, start=1):
                stripped = line.strip()
                if stripped.startswith("namespace "):
                    ns = stripped.removeprefix("namespace ").strip().split()[0:1]
                    if ns:
                        namespace_stack.append(ns[0])
                    continue
                if stripped == "end" or stripped.startswith("end "):
                    if namespace_stack:
                        namespace_stack.pop()
                    continue
                match = LEAN_DECL_RE.match(line)
                if match is None:
                    continue
                kind, local_name = match.groups()
                if local_name == "_":
                    continue
                if "." in local_name:
                    name = local_name
                elif namespace_stack:
                    name = ".".join(namespace_stack + [local_name])
                else:
                    name = local_name
                yield {
                    "name": name,
                    "kind": kind,
                    "module": module,
                    "file": str(path),
                    "line": line_no,
                    "doc": "",
                }


def build_record(decl: dict[str, Any], type_by_name: dict[str, dict[str, Any]], *, snippet_radius: int, max_snippet_chars: int) -> dict[str, Any] | None:
    name = str(decl.get("name") or "").strip()
    if not name:
        return None
    line_raw = decl.get("line")
    line = int(line_raw) if isinstance(line_raw, int) else None
    type_row = type_by_name.get(name, {})
    type_str = str(type_row.get("typeStr") or "")
    doc = str(decl.get("doc") or "")
    file_path = str(decl.get("file") or "")
    snippet = source_snippet(
        file_path,
        line,
        radius=snippet_radius,
        max_chars=max_snippet_chars,
    )
    name_tokens = split_name_tokens(name)
    doc_tokens = tokenize(doc)
    type_tokens = tokenize(type_str)
    snippet_tokens = tokenize(snippet)
    search_tokens = sorted(set(name_tokens + doc_tokens + type_tokens + snippet_tokens))
    return {
        "schema": "info_geometry.leansearch_local.record.v1",
        "name": name,
        "kind": str(decl.get("kind") or ""),
        "module": str(decl.get("module") or ""),
        "file": file_path,
        "line": line,
        "doc": doc,
        "type": type_str,
        "snippet": snippet,
        "nameTokens": name_tokens,
        "searchTokens": search_tokens,
        "informalDescription": doc or type_str or name,
    }


def build_records(
    *,
    decls_path: Path,
    types_path: Path,
    out_path: Path,
    snippet_radius: int = 2,
    max_snippet_chars: int = 1200,
) -> dict[str, Any]:
    type_by_name = load_types(types_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with out_path.open("w", encoding="utf-8") as out:
        for decl in iter_jsonl(decls_path):
            record = build_record(
                decl,
                type_by_name,
                snippet_radius=snippet_radius,
                max_snippet_chars=max_snippet_chars,
            )
            if record is None:
                continue
            out.write(json.dumps(record, ensure_ascii=True) + "\n")
            count += 1
    return {
        "schema": "info_geometry.leansearch_local.build_summary.v1",
        "decls": str(decls_path),
        "types": str(types_path),
        "out": str(out_path),
        "records": count,
    }


def build_source_records(
    *,
    source_roots: list[Path],
    out_path: Path,
    snippet_radius: int = 2,
    max_snippet_chars: int = 1200,
) -> dict[str, Any]:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    resolved_roots = [root.resolve() for root in source_roots]
    count = 0
    with out_path.open("w", encoding="utf-8") as out:
        for decl in iter_source_decls(resolved_roots):
            record = build_record(
                decl,
                {},
                snippet_radius=snippet_radius,
                max_snippet_chars=max_snippet_chars,
            )
            if record is None:
                continue
            record["schema"] = "info_geometry.leansearch_local.source_record.v1"
            record["authority"] = "source-navigation-only"
            out.write(json.dumps(record, ensure_ascii=True) + "\n")
            count += 1
    return {
        "schema": "info_geometry.leansearch_local.source_build_summary.v1",
        "sourceRoots": [str(root) for root in resolved_roots],
        "out": str(out_path),
        "records": count,
    }


def _idf(records: list[dict[str, Any]]) -> dict[str, float]:
    n = max(len(records), 1)
    df: Counter[str] = Counter()
    for record in records:
        df.update(set(str(tok) for tok in record.get("searchTokens") or []))
    return {tok: math.log((n + 1) / (freq + 1)) + 1.0 for tok, freq in df.items()}


def _score(query: str, query_tokens: list[str], record: dict[str, Any], idf: dict[str, float]) -> tuple[float, dict[str, float]]:
    search_tokens = set(str(tok) for tok in record.get("searchTokens") or [])
    name_tokens = set(str(tok) for tok in record.get("nameTokens") or [])
    name = str(record.get("name") or "").lower()
    doc = str(record.get("doc") or "").lower()
    typ = str(record.get("type") or "").lower()

    lexical = sum(idf.get(tok, 1.0) for tok in query_tokens if tok in search_tokens)
    name_bonus = sum(2.0 for tok in query_tokens if tok in name_tokens or tok in name)
    doc_bonus = sum(0.75 for tok in query_tokens if tok in doc)
    type_bonus = sum(0.5 for tok in query_tokens if tok in typ)
    exact_name_bonus = 0.0
    raw_tokens = tokenize(query)
    if len(raw_tokens) == 1:
        needle = normalize_identifier_text(raw_tokens[0])
        haystack = normalize_identifier_text(name)
        if needle and needle in haystack:
            exact_name_bonus = 25.0
    total = lexical + name_bonus + doc_bonus + type_bonus + exact_name_bonus
    return total, {
        "lexical": lexical,
        "name": name_bonus,
        "exactName": exact_name_bonus,
        "doc": doc_bonus,
        "type": type_bonus,
    }


def search_records(*, records_path: Path, query: str, top_k: int) -> dict[str, Any]:
    records = list(iter_jsonl(records_path))
    query_tokens_ = query_tokens(query)
    idf = _idf(records)
    hits = []
    for record in records:
        total, parts = _score(query, query_tokens_, record, idf)
        if total <= 0:
            continue
        hits.append((total, parts, record))
    hits.sort(key=lambda item: (-item[0], str(item[2].get("name") or "")))
    return {
        "schema": "info_geometry.leansearch_local.search_result.v1",
        "query": query,
        "queryTokens": query_tokens_,
        "records": str(records_path),
        "topK": top_k,
        "hits": [
            {
                "rank": idx,
                "score": score,
                "scoreBreakdown": parts,
                "schema": record.get("schema"),
                "authority": record.get("authority"),
                "name": record.get("name"),
                "kind": record.get("kind"),
                "module": record.get("module"),
                "file": record.get("file"),
                "line": record.get("line"),
                "doc": record.get("doc"),
                "type": record.get("type"),
                "snippet": record.get("snippet"),
            }
            for idx, (score, parts, record) in enumerate(hits[:top_k], start=1)
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    build = sub.add_parser("build", help="Build local LeanSearch-style records from DAG artifacts")
    build.add_argument("--decls", type=Path, default=DEFAULT_DECLS)
    build.add_argument("--types", type=Path, default=DEFAULT_TYPES)
    build.add_argument("--out", type=Path, default=DEFAULT_RECORDS)
    build.add_argument("--snippet-radius", type=int, default=2)
    build.add_argument("--max-snippet-chars", type=int, default=1200)

    source_build = sub.add_parser(
        "build-source",
        help="Build navigation-only records directly from Lean source roots",
    )
    source_build.add_argument("--source-root", type=Path, action="append", required=True)
    source_build.add_argument("--out", type=Path, default=DEFAULT_RECORDS)
    source_build.add_argument("--snippet-radius", type=int, default=2)
    source_build.add_argument("--max-snippet-chars", type=int, default=1200)

    search = sub.add_parser("search", help="Search local LeanSearch-style records")
    search.add_argument("query")
    search.add_argument("--records", type=Path, default=DEFAULT_RECORDS)
    search.add_argument("--top-k", type=int, default=8)
    search.add_argument("--out", type=Path)

    args = parser.parse_args()
    if args.cmd == "build":
        summary = build_records(
            decls_path=args.decls,
            types_path=args.types,
            out_path=args.out,
            snippet_radius=args.snippet_radius,
            max_snippet_chars=args.max_snippet_chars,
        )
        print(json.dumps(summary, indent=2, ensure_ascii=True))
        return 0

    if args.cmd == "build-source":
        summary = build_source_records(
            source_roots=args.source_root,
            out_path=args.out,
            snippet_radius=args.snippet_radius,
            max_snippet_chars=args.max_snippet_chars,
        )
        print(json.dumps(summary, indent=2, ensure_ascii=True))
        return 0

    result = search_records(records_path=args.records, query=args.query, top_k=args.top_k)
    payload = json.dumps(result, indent=2, ensure_ascii=True)
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(payload + "\n", encoding="utf-8")
    print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
