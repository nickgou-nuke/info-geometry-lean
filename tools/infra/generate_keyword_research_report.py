#!/usr/bin/env python3
"""Build a genuine full lexical index from all tracked Lean files.

This script does not start from hand-picked keywords.
It tokenizes every tracked `*.lean` file in the repository, computes
corpus-level frequencies, and emits a sorted term index with file hotspots.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path


STOPWORDS = {
    # Lean syntax / tactic vocabulary
    "admit",
    "aesop",
    "all_goals",
    "any_goals",
    "apply",
    "assumption",
    "axiom",
    "by",
    "calc",
    "cases",
    "change",
    "class",
    "constructor",
    "continue",
    "def",
    "do",
    "else",
    "end",
    "exact",
    "example",
    "ext",
    "false",
    "for",
    "from",
    "fun",
    "have",
    "if",
    "import",
    "in",
    "inductive",
    "infer_instance",
    "intro",
    "is",
    "let",
    "lemma",
    "linarith",
    "match",
    "namespace",
    "noncomputable",
    "obtain",
    "of",
    "open",
    "or",
    "private",
    "protected",
    "rfl",
    "rw",
    "simp",
    "simpa",
    "show",
    "structure",
    "suffices",
    "termination_by",
    "theorem",
    "then",
    "this",
    "true",
    "unfold",
    "variable",
    "where",
    "with",
    "the",
    "and",
    "using",
    "from",
    "into",
    "through",
    "across",
    "between",
    "under",
    "over",
    "type",
    "types",
    "plus",
    "minus",
    "comp",
    "map",
    "add",
    "mul",
    "sub",
    "nat",
    "fin",
    "one",
    "two",
    "three",
    "section",
    "local",
    "global",
    "default",
    "self",
    "json",
    "decl",
    # High-noise repository boilerplate
    "info",
    "geometry",
    "infogeometry",
    "canonical",
    "bridge",
    "owner",
    "lane",
    "packet",
    "core",
    "lean",
    "mathlib",
}

RAW_TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_']{2,}")
IDENT_SPLIT_RE = re.compile(r"[A-Z]?[a-z]+|[A-Z]+(?=[A-Z]|$)|[0-9]+")


@dataclass(frozen=True)
class CorpusFile:
    rel_path: str
    text: str
    token_counts: Counter[str]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        default=".",
        help="Repository root path (default: current directory).",
    )
    parser.add_argument(
        "--out",
        default="docs/auto/lean_keyword_research_report.md",
        help="Markdown report output path.",
    )
    parser.add_argument(
        "--json-out",
        default="reports/keywords/lean_keyword_research_report.json",
        help="Optional JSON output path.",
    )
    parser.add_argument(
        "--top-terms-md",
        type=int,
        default=300,
        help="How many sorted terms to render in markdown.",
    )
    parser.add_argument(
        "--top-files-per-term",
        type=int,
        default=5,
        help="How many hotspot files to show per term.",
    )
    parser.add_argument(
        "--min-term-count",
        type=int,
        default=6,
        help="Minimum global count required for term inclusion.",
    )
    return parser.parse_args()


def git_head(root: Path) -> str:
    try:
        out = subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=root,
            stderr=subprocess.DEVNULL,
        )
        return out.decode("utf-8").strip()
    except Exception:
        return "unknown"


def list_tracked_lean_files(root: Path) -> list[Path]:
    try:
        out = subprocess.check_output(
            ["git", "ls-files"],
            cwd=root,
            stderr=subprocess.DEVNULL,
        ).decode("utf-8")
        tracked = []
        for line in out.splitlines():
            if not line.endswith(".lean"):
                continue
            p = (root / line).resolve()
            if p.is_file():
                tracked.append(p)
        return sorted(tracked)
    except Exception:
        # Fallback if git metadata is unavailable.
        return sorted((root / "lean").rglob("*.lean"))


def split_identifier(token: str) -> list[str]:
    bits = token.replace("'", "").split("_")
    out: list[str] = []
    for bit in bits:
        for part in IDENT_SPLIT_RE.findall(bit):
            low = part.lower()
            if len(low) < 3:
                continue
            if low in STOPWORDS:
                continue
            out.append(low)
    return out


def iter_corpus_files(root: Path, lean_files: list[Path]) -> list[CorpusFile]:
    files: list[CorpusFile] = []
    for p in lean_files:
        rel = p.relative_to(root).as_posix()
        text = p.read_text(encoding="utf-8", errors="ignore")
        counts: Counter[str] = Counter()
        for tok in RAW_TOKEN_RE.findall(text):
            for low in split_identifier(tok):
                counts[low] += 1
        files.append(CorpusFile(rel_path=rel, text=text.lower(), token_counts=counts))
    return files


def build_term_index(
    corpus: list[CorpusFile], *, min_term_count: int, top_files_per_term: int
) -> list[dict]:
    global_counts = Counter()
    file_hits: dict[str, Counter[str]] = defaultdict(Counter)
    for cf in corpus:
        global_counts.update(cf.token_counts)
        for term, c in cf.token_counts.items():
            if c > 0:
                file_hits[term][cf.rel_path] = c

    rows: list[dict] = []
    for term, count in global_counts.items():
        if count < min_term_count:
            continue
        files = file_hits.get(term, Counter())
        top_files = files.most_common(top_files_per_term)
        rows.append(
            {
                "term": term,
                "count": count,
                "docFreq": len(files),
                "topFiles": [{"file": p, "count": c} for p, c in top_files],
            }
        )
    rows.sort(key=lambda r: (-r["count"], -r["docFreq"], r["term"]))
    return rows


def top_files_by_mass(corpus: list[CorpusFile], top_n: int) -> list[tuple[str, int]]:
    masses = []
    for cf in corpus:
        masses.append((cf.rel_path, sum(cf.token_counts.values())))
    masses.sort(key=lambda x: (-x[1], x[0]))
    return masses[:top_n]


def ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def render_markdown(
    *,
    root: Path,
    head: str,
    term_rows: list[dict],
    hotspot_rows: list[tuple[str, int]],
    lean_file_count: int,
    top_terms_md: int,
) -> str:
    now = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    lines: list[str] = []
    lines.append("# Keyword Research Report")
    lines.append("")
    lines.append(f"- generated: `{now}`")
    lines.append(f"- git head: `{head}`")
    lines.append(f"- root: `{root.resolve().as_posix()}`")
    lines.append("- corpus: all tracked `*.lean` files in repository")
    lines.append(f"- lean files indexed: `{lean_file_count}`")
    lines.append(f"- unique indexed terms: `{len(term_rows)}`")
    lines.append("")

    lines.append("## Sorted Terms (Full Lean Corpus)")
    lines.append("")
    lines.append("| rank | term | count | doc freq | top files |")
    lines.append("| ---: | --- | ---: | ---: | --- |")
    for i, row in enumerate(term_rows[:top_terms_md], start=1):
        hotspots = ", ".join(
            f"`{f['file']}` ({f['count']})" for f in row["topFiles"][:3]
        )
        lines.append(
            f"| {i} | `{row['term']}` | {row['count']} | {row['docFreq']} | {hotspots} |"
        )
    lines.append("")
    lines.append(
        f"_Markdown shows top `{min(top_terms_md, len(term_rows))}` terms; full sorted index is in JSON output._"
    )
    lines.append("")

    lines.append("## File Hotspots By Lexical Mass")
    lines.append("")
    lines.append("| file | lexical mass |")
    lines.append("| --- | ---: |")
    for f, m in hotspot_rows:
        lines.append(f"| `{f}` | {m} |")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    args = parse_args()
    root = Path(args.root).resolve()
    out_path = (root / args.out).resolve()
    json_out = (root / args.json_out).resolve() if args.json_out else None

    lean_files = list_tracked_lean_files(root)
    corpus = iter_corpus_files(root, lean_files)
    term_rows = build_term_index(
        corpus,
        min_term_count=args.min_term_count,
        top_files_per_term=args.top_files_per_term,
    )
    hotspot_rows = top_files_by_mass(corpus, top_n=25)

    report = render_markdown(
        root=root,
        head=git_head(root),
        term_rows=term_rows,
        hotspot_rows=hotspot_rows,
        lean_file_count=len(lean_files),
        top_terms_md=args.top_terms_md,
    )
    ensure_parent(out_path)
    out_path.write_text(report, encoding="utf-8")

    if json_out:
        ensure_parent(json_out)
        payload = {
            "generatedAt": datetime.now(timezone.utc).isoformat(),
            "gitHead": git_head(root),
            "indexedLeanFiles": [p.relative_to(root).as_posix() for p in lean_files],
            "termIndex": term_rows,
            "fileHotspots": [{"file": f, "lexicalMass": m} for f, m in hotspot_rows],
        }
        json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    print(f"[keyword-report] wrote {os.path.relpath(out_path, root)}")
    if json_out:
        print(f"[keyword-report] wrote {os.path.relpath(json_out, root)}")
    print(
        f"[keyword-report] lean_files={len(lean_files)} term_rows={len(term_rows)} corpus_files={len(corpus)}"
    )


if __name__ == "__main__":
    main()
