#!/usr/bin/env python3
"""Create a black-books story from full black-books keyword index."""

from __future__ import annotations

import argparse
import json
import math
import re
import subprocess
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path


NOISE_TERMS = {
    "canonical",
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
    "file",
    "files",
    "line",
    "lines",
    "code",
    "core",
    "bridge",
    "owner",
    "lane",
    "packet",
    "space",
}

PROFILE_BONUS: dict[str, dict[str, float]] = {
    "balanced": {
        "modular": 4500.0,
        "krein": 4000.0,
        "transport": 3500.0,
        "anomaly": 3000.0,
        "drazin": 3000.0,
        "einstein": 2500.0,
        "methodology": 2500.0,
        "audit": 2500.0,
        "story": 2200.0,
    },
    "physics": {
        "modular": 9000.0,
        "tomita": 10000.0,
        "connes": 10000.0,
        "radon": 9000.0,
        "nikodym": 9000.0,
        "krein": 9000.0,
        "clifford": 8500.0,
        "bogoliubov": 8500.0,
        "sinkhorn": 8000.0,
        "kms": 8000.0,
        "drazin": 7500.0,
        "einstein": 7500.0,
        "weyl": 7000.0,
        "majorana": 7000.0,
    },
    "methodology": {
        "methodology": 12000.0,
        "protocol": 11000.0,
        "audit": 10500.0,
        "vacuity": 10000.0,
        "dag": 10000.0,
        "refactor": 9500.0,
        "taxonomy": 9000.0,
        "representation": 9000.0,
        "closure": 8500.0,
        "story": 8000.0,
        "narrative": 8000.0,
        "jung": 7800.0,
        "pauli": 7800.0,
        "alchemical": 7600.0,
    },
}


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", default=".")
    ap.add_argument(
        "--index-json",
        default="reports/keywords/black_books_keyword_research_report.json",
    )
    ap.add_argument(
        "--story-out",
        default="docs/auto/black_books_story_from_keyword_index.md",
    )
    ap.add_argument(
        "--json-out",
        default="reports/keywords/black_books_characteristic_term_deep_search.json",
    )
    ap.add_argument(
        "--profile",
        choices=["balanced", "physics", "methodology"],
        default="balanced",
    )
    ap.add_argument("--term-count", type=int, default=24)
    ap.add_argument("--min-count", type=int, default=8)
    ap.add_argument("--min-doc-freq", type=int, default=2)
    ap.add_argument("--max-doc-freq", type=int, default=80)
    ap.add_argument("--max-excerpts-per-term", type=int, default=20)
    return ap.parse_args()


def git_head(root: Path) -> str:
    try:
        out = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, stderr=subprocess.DEVNULL
        )
        return out.decode("utf-8").strip()
    except Exception:
        return "unknown"


# [lossless-compact] load_json folded into igf.common.json_io.load_json
from igf.common.json_io import load_json


def pick_terms(
    term_rows: list[dict],
    *,
    profile: str,
    term_count: int,
    min_count: int,
    min_doc_freq: int,
    max_doc_freq: int,
) -> list[dict]:
    bonus = PROFILE_BONUS.get(profile, {})
    rows: list[dict] = []
    for row in term_rows:
        term = row["term"]
        c = int(row["count"])
        df = int(row["docFreq"])
        if c < min_count:
            continue
        if df < min_doc_freq or df > max_doc_freq:
            continue
        if len(term) < 4:
            continue
        if term in NOISE_TERMS:
            continue
        score = c * math.log(df + 1.0) + bonus.get(term, 0.0)
        rows.append(
            {
                "term": term,
                "count": c,
                "docFreq": df,
                "score": score,
                "topFiles": row.get("topFiles", []),
            }
        )
    rows.sort(key=lambda r: (-r["score"], -r["count"], r["term"]))
    return rows[:term_count]


def load_docs(root: Path, files: list[str]) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    for rel in files:
        p = (root / rel).resolve()
        if not p.is_file():
            continue
        out[rel] = p.read_text(encoding="utf-8", errors="ignore").splitlines()
    return out


def deep_search_excerpts(
    terms: list[dict], docs_by_file: dict[str, list[str]], max_excerpts: int
) -> list[dict]:
    out: list[dict] = []
    for row in terms:
        term = row["term"]
        excerpts = []
        chapter_counts: Counter[str] = Counter()
        pattern = re.compile(rf"\b{re.escape(term)}\b", re.IGNORECASE)
        for rel, lines in docs_by_file.items():
            for i, ln in enumerate(lines, start=1):
                if pattern.search(ln):
                    clean = " ".join(ln.strip().split())
                    if clean:
                        chapter_counts[rel] += 1
                        excerpts.append(
                            {
                                "file": rel,
                                "line": i,
                                "text": clean[:220],
                            }
                        )
        excerpts.sort(key=lambda e: (e["file"], e["line"]))
        out.append(
            {
                "term": term,
                "count": row["count"],
                "docFreq": row["docFreq"],
                "score": row["score"],
                "topFiles": row.get("topFiles", []),
                "excerptCount": len(excerpts),
                "chapterHits": [{"file": f, "hits": c} for f, c in chapter_counts.most_common(8)],
                "excerpts": excerpts[:max_excerpts],
            }
        )
    return out


def cluster_terms(rows: list[dict]) -> dict[str, list[dict]]:
    clusters = {
        "Physics and Operator-Geometry": [],
        "Psychology and Alchemical Method": [],
        "Repository Methodology and Audit": [],
        "General Narrative Layer": [],
    }
    for r in rows:
        t = r["term"]
        if any(k in t for k in ["modular", "krein", "clifford", "tomita", "connes", "radon", "nikodym", "drazin", "einstein", "weyl", "majorana", "transport", "sinkhorn", "kms", "quantum"]):
            clusters["Physics and Operator-Geometry"].append(r)
        elif any(k in t for k in ["jung", "pauli", "archetype", "shadow", "trickster", "alchemical", "alchemy", "myth", "unconscious"]):
            clusters["Psychology and Alchemical Method"].append(r)
        elif any(k in t for k in ["audit", "vacuity", "dag", "protocol", "methodology", "taxonomy", "representation", "closure", "refactor", "index", "story", "narrative"]):
            clusters["Repository Methodology and Audit"].append(r)
        else:
            clusters["General Narrative Layer"].append(r)
    return clusters


def render_story(
    *,
    root: Path,
    head: str,
    profile: str,
    indexed_files: int,
    rows: list[dict],
    clusters: dict[str, list[dict]],
) -> str:
    now = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    lines: list[str] = []
    lines.append("# Black Books Story From Full Keyword Index")
    lines.append("")
    lines.append(f"- generated: `{now}`")
    lines.append(f"- git head: `{head}`")
    lines.append(f"- root: `{root.resolve().as_posix()}`")
    lines.append(f"- selector profile: `{profile}`")
    lines.append(f"- indexed black-book files: `{indexed_files}`")
    lines.append(f"- characteristic terms selected: `{len(rows)}`")
    lines.append("")

    lines.append("## Method")
    lines.append("")
    lines.append("1. Full lexical index on black-book markdown corpus.")
    lines.append("2. Characteristic-term selection by count × log(doc-frequency + 1), plus profile-term bias.")
    lines.append("3. Deep search over chapter excerpts with file/line evidence.")
    lines.append("")

    lines.append("## Characteristic Terms")
    lines.append("")
    lines.append("| term | count | doc freq | score | excerpt hits |")
    lines.append("| --- | ---: | ---: | ---: | ---: |")
    for r in rows:
        lines.append(
            f"| `{r['term']}` | {r['count']} | {r['docFreq']} | {r['score']:.2f} | {r['excerptCount']} |"
        )
    lines.append("")

    lines.append("## Deep Excerpt Search")
    lines.append("")
    for r in rows:
        lines.append(f"### `{r['term']}`")
        lines.append(f"- excerpt hits: `{r['excerptCount']}`")
        if r["chapterHits"]:
            hs = ", ".join(f"`{h['file']}` ({h['hits']})" for h in r["chapterHits"][:4])
            lines.append(f"- chapter hotspots: {hs}")
        if r["excerpts"]:
            lines.append("- sample excerpts:")
            for e in r["excerpts"][:6]:
                lines.append(f"  - `{e['file']}:{e['line']}` — {e['text']}")
        lines.append("")

    lines.append("## Refactored Black-Book Story")
    lines.append("")
    for name, vals in clusters.items():
        if not vals:
            continue
        term_list = ", ".join(f"`{v['term']}`" for v in vals[:8])
        hits = sum(v["excerptCount"] for v in vals)
        lines.append(f"- **{name}**: `{hits}` excerpt hits across {term_list}.")
    lines.append("")
    lines.append(
        "This synthesis remains prose-layer evidence. Stable formal claims still require cross-checking against theorem/lemma/axiom surfaces in the Lean corpus."
    )
    lines.append("")
    return "\n".join(lines)


def ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def main() -> None:
    args = parse_args()
    root = Path(args.root).resolve()
    index_json = (root / args.index_json).resolve()
    story_out = (root / args.story_out).resolve()
    json_out = (root / args.json_out).resolve()

    payload = load_json(index_json)
    term_rows = payload.get("termIndex", [])
    indexed_files = payload.get("indexedFiles", [])
    if not term_rows:
        raise RuntimeError(f"No termIndex found in {index_json}")

    chosen = pick_terms(
        term_rows,
        profile=args.profile,
        term_count=args.term_count,
        min_count=args.min_count,
        min_doc_freq=args.min_doc_freq,
        max_doc_freq=args.max_doc_freq,
    )
    docs_by_file = load_docs(root, indexed_files)
    deep_rows = deep_search_excerpts(chosen, docs_by_file, args.max_excerpts_per_term)
    clusters = cluster_terms(deep_rows)

    md = render_story(
        root=root,
        head=git_head(root),
        profile=args.profile,
        indexed_files=len(indexed_files),
        rows=deep_rows,
        clusters=clusters,
    )
    ensure_parent(story_out)
    story_out.write_text(md, encoding="utf-8")

    out = {
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "gitHead": git_head(root),
        "profile": args.profile,
        "indexedFiles": len(indexed_files),
        "characteristicTerms": deep_rows,
        "clusters": {k: [v["term"] for v in vals] for k, vals in clusters.items()},
    }
    ensure_parent(json_out)
    json_out.write_text(json.dumps(out, indent=2), encoding="utf-8")

    print(f"[black-books-story] wrote {story_out.relative_to(root)}")
    print(f"[black-books-story] wrote {json_out.relative_to(root)}")
    print(
        f"[black-books-story] profile={args.profile} terms={len(deep_rows)} files={len(indexed_files)}"
    )


if __name__ == "__main__":
    main()
