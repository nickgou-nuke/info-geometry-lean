#!/usr/bin/env python3
"""Refactor full Lean keyword indexing into a declaration-grounded repo story.

Pipeline:
1) read sorted lexical index from all tracked Lean files
2) pick characteristic terms by profile-aware score
3) deep search all theorem/lemma/axiom blocks for each term
4) emit a research report + narrative repository story
"""

from __future__ import annotations

import argparse
import json
import math
import re
import subprocess
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path


DECL_RE = re.compile(r"^\s*(theorem|lemma|axiom)\s+([A-Za-z0-9_.']+)", re.MULTILINE)

NOISE_TERMS = {
    "add",
    "attribute",
    "canonical",
    "certified",
    "bridge",
    "blueprint",
    "comp",
    "core",
    "decl",
    "deriv",
    "docs",
    "owner",
    "packet",
    "lane",
    "module",
    "modules",
    "axiom",
    "theorem",
    "lemma",
    "projector",
    "operatorial",
    "proof",
    "prob",
    "source",
    "target",
    "data",
    "line",
    "lines",
    "type",
    "types",
    "true",
    "false",
    "nat",
    "fin",
    "real",
    "complex",
    "map",
    "plus",
    "minus",
    "head",
    "rep",
    "zero",
    "linear",
    "doubled",
    "split",
    "finite",
    "name",
    "form",
    "part",
    "seed",
    "left",
    "right",
    "complete",
    "proj",
    "smul",
    "positive",
    "epsilon",
    "sum",
    "set",
    "state",
    "flow",
    "count",
    "counts",
    "phase",
    "space",
    "family",
    "index",  # too broad; specific index words are captured separately
}

PROFILE_BONUS: dict[str, dict[str, float]] = {
    "balanced": {
        "modular": 5000.0,
        "krein": 4500.0,
        "transport": 4500.0,
        "drazin": 3500.0,
        "einstein": 3500.0,
        "quantum": 3000.0,
        "clifford": 3000.0,
        "projective": 2500.0,
        "gauge": 2000.0,
    },
    "physics": {
        "tomita": 12000.0,
        "connes": 12000.0,
        "radon": 11000.0,
        "nikodym": 11000.0,
        "kms": 11000.0,
        "sinkhorn": 10500.0,
        "bogoliubov": 10500.0,
        "hamiltonian": 10000.0,
        "einstein": 9500.0,
        "drazin": 9000.0,
        "weyl": 8500.0,
        "majorana": 8500.0,
        "clifford": 8000.0,
        "quantum": 7000.0,
        "projective": 6000.0,
        "gauge": 5000.0,
        "thermo": 5000.0,
        "llm": 4500.0,
    },
    "methodology": {
        "audit": 12000.0,
        "vacuity": 12000.0,
        "dag": 11000.0,
        "representation": 10000.0,
        "depth": 9000.0,
        "semantic": 9000.0,
        "morphism": 8500.0,
        "causal": 8000.0,
        "frontier": 8000.0,
        "policy": 7500.0,
        "artifact": 7000.0,
        "indexer": 6500.0,
        "closure": 6000.0,
    },
}


@dataclass(frozen=True)
class DeclBlock:
    kind: str
    name: str
    file: str
    line: int
    body_lower: str


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", default=".")
    ap.add_argument(
        "--index-json",
        default="reports/keywords/lean_keyword_research_report.json",
        help="Input from generate_keyword_research_report.py",
    )
    ap.add_argument(
        "--story-out",
        default="docs/auto/repo_story_from_keyword_index.md",
        help="Markdown story output path",
    )
    ap.add_argument(
        "--term-json-out",
        default="reports/keywords/characteristic_term_deep_search.json",
        help="Deep-search JSON output path",
    )
    ap.add_argument("--term-count", type=int, default=24)
    ap.add_argument("--min-count", type=int, default=20)
    ap.add_argument("--min-doc-freq", type=int, default=40)
    ap.add_argument("--max-doc-freq", type=int, default=400)
    ap.add_argument("--max-decls-per-term", type=int, default=40)
    ap.add_argument(
        "--profile",
        choices=["balanced", "physics", "methodology"],
        default="balanced",
        help="Selector profile bias.",
    )
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


def list_tracked_lean_files(root: Path) -> list[Path]:
    try:
        out = subprocess.check_output(
            ["git", "ls-files"], cwd=root, stderr=subprocess.DEVNULL
        ).decode("utf-8")
        files = []
        for line in out.splitlines():
            if line.endswith(".lean"):
                p = (root / line).resolve()
                if p.is_file():
                    files.append(p)
        return sorted(files)
    except Exception:
        return sorted((root / "lean").rglob("*.lean"))


def parse_decl_blocks(root: Path, lean_files: list[Path]) -> list[DeclBlock]:
    blocks: list[DeclBlock] = []
    for p in lean_files:
        rel = p.relative_to(root).as_posix()
        text = p.read_text(encoding="utf-8", errors="ignore")
        matches = list(DECL_RE.finditer(text))
        if not matches:
            continue
        starts = [m.start() for m in matches] + [len(text)]
        for i, m in enumerate(matches):
            kind = m.group(1)
            name = m.group(2)
            start = starts[i]
            end = starts[i + 1]
            body = text[start:end].lower()
            line = text.count("\n", 0, start) + 1
            blocks.append(DeclBlock(kind=kind, name=name, file=rel, line=line, body_lower=body))
    return blocks


def pick_characteristic_terms(
    term_rows: list[dict],
    *,
    total_docs: int,
    term_count: int,
    min_count: int,
    min_doc_freq: int,
    max_doc_freq: int,
    profile: str,
) -> list[dict]:
    bonus_table = PROFILE_BONUS.get(profile, {})
    picks: list[dict] = []
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
        score = c * math.log(df + 1.0) + bonus_table.get(term, 0.0)
        picks.append(
            {
                "term": term,
                "count": c,
                "docFreq": df,
                "score": score,
                "topFiles": row.get("topFiles", []),
            }
        )
    picks.sort(key=lambda r: (-r["score"], -r["count"], r["term"]))
    return picks[:term_count]


def deep_search_by_terms(
    terms: list[dict], blocks: list[DeclBlock], max_decls_per_term: int
) -> list[dict]:
    out: list[dict] = []
    for row in terms:
        term = row["term"]
        matches = []
        for b in blocks:
            if term in b.body_lower or term in b.name.lower():
                matches.append(
                    {
                        "kind": b.kind,
                        "name": b.name,
                        "file": b.file,
                        "line": b.line,
                    }
                )
        # Deterministic sort: file, line, name
        matches.sort(key=lambda d: (d["file"], d["line"], d["name"]))
        kind_counts = Counter(m["kind"] for m in matches)
        out.append(
            {
                "term": term,
                "count": row["count"],
                "docFreq": row["docFreq"],
                "score": row["score"],
                "topFiles": row.get("topFiles", []),
                "declarationCount": len(matches),
                "kindCounts": dict(kind_counts),
                "declarations": matches[:max_decls_per_term],
            }
        )
    return out


def infer_story_clusters(term_results: list[dict]) -> dict[str, list[dict]]:
    clusters = {
        "Modular-Operator Spine": [],
        "Krein-Clifford Geometry": [],
        "Transport-Thermo Layer": [],
        "Anomaly-Index-Gravity Layer": [],
        "Methodology and Infrastructure": [],
    }
    for r in term_results:
        t = r["term"]
        if any(k in t for k in ["modular", "tomita", "connes", "radon", "nikodym", "hamiltonian"]):
            clusters["Modular-Operator Spine"].append(r)
        elif any(k in t for k in ["krein", "clifford", "majorana", "chiral", "spinor"]):
            clusters["Krein-Clifford Geometry"].append(r)
        elif any(k in t for k in ["transport", "bogoliubov", "sinkhorn", "kms", "thermo", "softmax", "gibbs", "llm"]):
            clusters["Transport-Thermo Layer"].append(r)
        elif any(k in t for k in ["drazin", "einstein", "anomaly", "fredholm", "index", "tensor", "weyl"]):
            clusters["Anomaly-Index-Gravity Layer"].append(r)
        else:
            clusters["Methodology and Infrastructure"].append(r)
    return clusters


def render_story(
    *,
    root: Path,
    head: str,
    total_docs: int,
    term_results: list[dict],
    cluster_map: dict[str, list[dict]],
    profile: str,
) -> str:
    now = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    lines: list[str] = []
    lines.append("# Repository Story From Full Lean Keyword Index")
    lines.append("")
    lines.append(f"- generated: `{now}`")
    lines.append(f"- git head: `{head}`")
    lines.append(f"- indexed tracked Lean files: `{total_docs}`")
    lines.append(f"- selector profile: `{profile}`")
    lines.append(f"- characteristic terms selected: `{len(term_results)}`")
    lines.append("")

    lines.append("## Method")
    lines.append("")
    lines.append("1. Full lexical index over all tracked `*.lean` files, sorted by frequency.")
    lines.append(
        "2. Characteristic-term selection by count × log(doc-frequency + 1), plus profile-term bias."
    )
    lines.append("3. Deep search over declaration blocks (`theorem`, `lemma`, `axiom`) for each selected term.")
    lines.append("")

    lines.append("## Characteristic Terms")
    lines.append("")
    lines.append("| term | count | doc freq | score | declaration hits |")
    lines.append("| --- | ---: | ---: | ---: | ---: |")
    for r in term_results:
        lines.append(
            f"| `{r['term']}` | {r['count']} | {r['docFreq']} | {r['score']:.2f} | {r['declarationCount']} |"
        )
    lines.append("")

    lines.append("## Deep Declaration Search")
    lines.append("")
    for r in term_results:
        lines.append(f"### `{r['term']}`")
        kc = r["kindCounts"]
        lines.append(
            f"- declaration matches: `{r['declarationCount']}` (theorem `{kc.get('theorem', 0)}`, lemma `{kc.get('lemma', 0)}`, axiom `{kc.get('axiom', 0)}`)"
        )
        if r["topFiles"]:
            hotspots = ", ".join(
                f"`{x['file']}` ({x['count']})" for x in r["topFiles"][:4]
            )
            lines.append(f"- lexical hotspots: {hotspots}")
        if r["declarations"]:
            lines.append("- sample declarations:")
            for d in r["declarations"][:8]:
                lines.append(
                    f"  - `{d['kind']} {d['name']}` — `{d['file']}:{d['line']}`"
                )
        lines.append("")

    lines.append("## Refactored Story")
    lines.append("")
    lines.append(
        "The repository narrative is not a single file stack; it is a layered transport story anchored by declaration-bearing operator geometry."
    )
    lines.append("")
    for cname, rows in cluster_map.items():
        if not rows:
            continue
        total_decls = sum(r["declarationCount"] for r in rows)
        top_terms = ", ".join(f"`{r['term']}`" for r in rows[:6])
        lines.append(f"- **{cname}**: `{total_decls}` declaration hits across {top_terms}.")
    lines.append("")
    lines.append(
        "In this refactoring, the black-book lane is treated as hypothesis generation, while theorem/lemma/axiom surfaces provide the stable kernel-confirmed memory of the project."
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
    term_json_out = (root / args.term_json_out).resolve()

    payload = load_json(index_json)
    term_rows = payload.get("termIndex", [])
    if not term_rows:
        raise RuntimeError(f"No termIndex in {index_json}")

    lean_files = list_tracked_lean_files(root)
    blocks = parse_decl_blocks(root, lean_files)
    min_count = args.min_count
    min_doc_freq = args.min_doc_freq
    max_doc_freq = args.max_doc_freq
    if args.profile == "physics":
        min_count = min(min_count, 10)
        min_doc_freq = min(min_doc_freq, 12)
    elif args.profile == "methodology":
        min_count = min(min_count, 8)
        min_doc_freq = min(min_doc_freq, 4)
        max_doc_freq = min(max_doc_freq, 250)

    terms = pick_characteristic_terms(
        term_rows,
        total_docs=len(lean_files),
        term_count=args.term_count,
        min_count=min_count,
        min_doc_freq=min_doc_freq,
        max_doc_freq=max_doc_freq,
        profile=args.profile,
    )
    term_results = deep_search_by_terms(terms, blocks, args.max_decls_per_term)
    cluster_map = infer_story_clusters(term_results)

    md = render_story(
        root=root,
        head=git_head(root),
        total_docs=len(lean_files),
        term_results=term_results,
        cluster_map=cluster_map,
        profile=args.profile,
    )
    ensure_parent(story_out)
    story_out.write_text(md, encoding="utf-8")

    ensure_parent(term_json_out)
    out_payload = {
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "gitHead": git_head(root),
        "indexedLeanFiles": len(lean_files),
        "declarationBlocks": len(blocks),
        "profile": args.profile,
        "characteristicTerms": term_results,
        "clusters": {
            k: [r["term"] for r in v]
            for k, v in cluster_map.items()
        },
    }
    term_json_out.write_text(json.dumps(out_payload, indent=2), encoding="utf-8")

    print(f"[repo-story] wrote {story_out.relative_to(root)}")
    print(f"[repo-story] wrote {term_json_out.relative_to(root)}")
    print(
        f"[repo-story] lean_files={len(lean_files)} decl_blocks={len(blocks)} characteristic_terms={len(term_results)}"
    )


if __name__ == "__main__":
    main()
