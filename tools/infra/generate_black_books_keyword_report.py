#!/usr/bin/env python3
"""Build a full lexical index from black-book markdown files only."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path


TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_'-]{2,}")

STOPWORDS = {
    "the",
    "and",
    "for",
    "with",
    "that",
    "this",
    "from",
    "into",
    "over",
    "under",
    "between",
    "across",
    "then",
    "than",
    "also",
    "only",
    "where",
    "when",
    "while",
    "because",
    "therefore",
    "hence",
    "about",
    "above",
    "below",
    "what",
    "which",
    "whose",
    "have",
    "has",
    "had",
    "are",
    "was",
    "were",
    "will",
    "shall",
    "can",
    "may",
    "might",
    "not",
    "but",
    "one",
    "two",
    "three",
    "four",
    "five",
    "six",
    "seven",
    "eight",
    "nine",
    "ten",
    "chapter",
    "chapters",
    "black",
    "book",
    "books",
    "repo",
    "repository",
    "lean",
    "lean4",
    "proof",
    "theorem",
    "lemma",
    "axiom",
    "code",
    "file",
    "files",
    "docs",
    "doc",
    "line",
    "lines",
}


@dataclass(frozen=True)
class CorpusDoc:
    rel_path: str
    text_lower: str
    token_counts: Counter[str]


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", default=".")
    ap.add_argument(
        "--include-refactor",
        action="store_true",
        help="Include docs/black_books_refactor/*.md in corpus.",
    )
    ap.add_argument(
        "--out",
        default="docs/auto/black_books_keyword_research_report.md",
    )
    ap.add_argument(
        "--json-out",
        default="reports/keywords/black_books_keyword_research_report.json",
    )
    ap.add_argument("--top-terms-md", type=int, default=220)
    ap.add_argument("--top-files-per-term", type=int, default=5)
    ap.add_argument("--min-term-count", type=int, default=3)
    return ap.parse_args()


def git_head(root: Path) -> str:
    try:
        out = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, stderr=subprocess.DEVNULL
        )
        return out.decode("utf-8").strip()
    except Exception:
        return "unknown"


def list_tracked_markdown(root: Path, include_refactor: bool) -> list[Path]:
    try:
        out = subprocess.check_output(
            ["git", "ls-files"], cwd=root, stderr=subprocess.DEVNULL
        ).decode("utf-8")
        files: list[Path] = []
        for line in out.splitlines():
            if not line.endswith(".md"):
                continue
            if line.startswith("docs/black_books/"):
                p = (root / line).resolve()
                if p.is_file():
                    files.append(p)
            elif include_refactor and line.startswith("docs/black_books_refactor/"):
                p = (root / line).resolve()
                if p.is_file():
                    files.append(p)
        return sorted(files)
    except Exception:
        pats = [root / "docs/black_books"]
        if include_refactor:
            pats.append(root / "docs/black_books_refactor")
        files: list[Path] = []
        for base in pats:
            if base.exists():
                files.extend(base.rglob("*.md"))
        return sorted(p.resolve() for p in files if p.is_file())


def tokenize(text: str) -> Counter[str]:
    c: Counter[str] = Counter()
    for tok in TOKEN_RE.findall(text):
        low = tok.lower().strip("-'_")
        if len(low) < 3:
            continue
        if low in STOPWORDS:
            continue
        if low.startswith("http"):
            continue
        c[low] += 1
    return c


def iter_docs(root: Path, paths: list[Path]) -> list[CorpusDoc]:
    docs: list[CorpusDoc] = []
    for p in paths:
        rel = p.relative_to(root).as_posix()
        text = p.read_text(encoding="utf-8", errors="ignore")
        docs.append(CorpusDoc(rel_path=rel, text_lower=text.lower(), token_counts=tokenize(text)))
    return docs


def build_term_index(
    docs: list[CorpusDoc], min_term_count: int, top_files_per_term: int
) -> list[dict]:
    global_counts: Counter[str] = Counter()
    file_counts: dict[str, Counter[str]] = {}
    for d in docs:
        global_counts.update(d.token_counts)
        file_counts[d.rel_path] = d.token_counts

    term_rows: list[dict] = []
    for term, count in global_counts.items():
        if count < min_term_count:
            continue
        doc_hits = []
        df = 0
        for fp, counts in file_counts.items():
            c = counts.get(term, 0)
            if c > 0:
                df += 1
                doc_hits.append((c, fp))
        doc_hits.sort(key=lambda x: (-x[0], x[1]))
        term_rows.append(
            {
                "term": term,
                "count": count,
                "docFreq": df,
                "topFiles": [{"file": f, "count": c} for c, f in doc_hits[:top_files_per_term]],
            }
        )
    term_rows.sort(key=lambda r: (-r["count"], -r["docFreq"], r["term"]))
    return term_rows


def top_docs_by_mass(docs: list[CorpusDoc], top_n: int = 25) -> list[tuple[str, int]]:
    rows = [(d.rel_path, sum(d.token_counts.values())) for d in docs]
    rows.sort(key=lambda x: (-x[1], x[0]))
    return rows[:top_n]


def ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def render_markdown(
    *,
    root: Path,
    head: str,
    docs_count: int,
    term_rows: list[dict],
    hotspot_rows: list[tuple[str, int]],
    top_terms_md: int,
    include_refactor: bool,
) -> str:
    now = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    lines: list[str] = []
    lines.append("# Black Books Keyword Research Report")
    lines.append("")
    lines.append(f"- generated: `{now}`")
    lines.append(f"- git head: `{head}`")
    lines.append(f"- root: `{root.resolve().as_posix()}`")
    scope = "`docs/black_books/*.md`"
    if include_refactor:
        scope += " + `docs/black_books_refactor/*.md`"
    lines.append(f"- corpus scope: {scope}")
    lines.append(f"- markdown files indexed: `{docs_count}`")
    lines.append(f"- unique indexed terms: `{len(term_rows)}`")
    lines.append("")

    lines.append("## Sorted Terms")
    lines.append("")
    lines.append("| rank | term | count | doc freq | top chapters |")
    lines.append("| ---: | --- | ---: | ---: | --- |")
    for i, row in enumerate(term_rows[:top_terms_md], start=1):
        hotspots = ", ".join(
            f"`{x['file']}` ({x['count']})" for x in row["topFiles"][:3]
        )
        lines.append(
            f"| {i} | `{row['term']}` | {row['count']} | {row['docFreq']} | {hotspots} |"
        )
    lines.append("")
    lines.append(
        f"_Markdown shows top `{min(top_terms_md, len(term_rows))}` terms; full sorted index is in JSON output._"
    )
    lines.append("")

    lines.append("## Chapter Hotspots By Lexical Mass")
    lines.append("")
    lines.append("| chapter | lexical mass |")
    lines.append("| --- | ---: |")
    for f, m in hotspot_rows:
        lines.append(f"| `{f}` | {m} |")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    args = parse_args()
    root = Path(args.root).resolve()
    out_path = (root / args.out).resolve()
    json_out = (root / args.json_out).resolve()

    md_files = list_tracked_markdown(root, args.include_refactor)
    docs = iter_docs(root, md_files)
    term_rows = build_term_index(
        docs, min_term_count=args.min_term_count, top_files_per_term=args.top_files_per_term
    )
    hotspot_rows = top_docs_by_mass(docs)

    md = render_markdown(
        root=root,
        head=git_head(root),
        docs_count=len(docs),
        term_rows=term_rows,
        hotspot_rows=hotspot_rows,
        top_terms_md=args.top_terms_md,
        include_refactor=args.include_refactor,
    )
    ensure_parent(out_path)
    out_path.write_text(md, encoding="utf-8")

    payload = {
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "gitHead": git_head(root),
        "includeRefactor": args.include_refactor,
        "indexedFiles": [p.relative_to(root).as_posix() for p in md_files],
        "termIndex": term_rows,
        "fileHotspots": [{"file": f, "lexicalMass": m} for f, m in hotspot_rows],
    }
    ensure_parent(json_out)
    json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    print(f"[black-books-index] wrote {os.path.relpath(out_path, root)}")
    print(f"[black-books-index] wrote {os.path.relpath(json_out, root)}")
    print(f"[black-books-index] files={len(docs)} terms={len(term_rows)}")


if __name__ == "__main__":
    main()
