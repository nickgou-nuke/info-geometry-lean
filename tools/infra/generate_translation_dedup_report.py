#!/usr/bin/env python3
"""Generate a read-only report for translation/dedup overlays.

The report separates:

* exact hash buckets from declaration topology,
* derived/Lean-verified translation SCCs,
* translation edges by kind and verification tier,
* vector-near review-only candidates.

It does not mutate Lean, Arango, or any overlay collection.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


DEFAULT_WIRE_DIR = Path("artifacts/expr-graph/wire-topology")
DEFAULT_TRANSLATION_DIR = Path("artifacts/expr-graph/translation-candidates")
DEFAULT_JSON_OUT = Path("reports/dag/translation-dedup-report.json")
DEFAULT_MD_OUT = Path("reports/dag/translation-dedup-report.md")


def utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def iter_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    if not path.exists():
        return
    with path.open("r", encoding="utf-8") as handle:
        for line_no, raw in enumerate(handle, start=1):
            line = raw.strip()
            if not line:
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_no}: expected JSON object")
            yield row


def exact_buckets(topologies: list[dict[str, Any]], hash_kind: str) -> list[dict[str, Any]]:
    groups: dict[str, list[str]] = defaultdict(list)
    for row in topologies:
        hash_value = str(row.get(hash_kind, "") or "")
        decl = str(row.get("decl", "") or "")
        if hash_value and decl:
            groups[hash_value].append(decl)
    buckets = [
        {"hash": hash_value, "count": len(sorted(set(decls))), "declarations": sorted(set(decls))}
        for hash_value, decls in groups.items()
        if len(set(decls)) > 1
    ]
    buckets.sort(key=lambda row: (-int(row["count"]), str(row["hash"])))
    return buckets


def build_report(wire_dir: Path, translation_dir: Path) -> dict[str, Any]:
    topologies = list(iter_jsonl(wire_dir / "ig_decl_topologies.jsonl"))
    candidates = list(iter_jsonl(translation_dir / "ig_translation_candidates.jsonl"))
    edges = list(iter_jsonl(translation_dir / "ig_translation_edges.jsonl"))
    sccs = list(iter_jsonl(translation_dir / "ig_translation_scc.jsonl"))

    verified_candidates = [row for row in candidates if bool(row.get("verified"))]
    lean_verified_candidates = [row for row in verified_candidates if bool(row.get("leanVerified"))]
    review_candidates = [row for row in candidates if not bool(row.get("verified"))]
    vector_review = [row for row in review_candidates if row.get("candidateKind") == "logic_vector_near"]
    verified_sccs = [row for row in sccs if int(row.get("memberCount", 0) or 0) > 1]
    verified_sccs.sort(key=lambda row: (-int(row.get("memberCount", 0) or 0), str(row.get("translationSccHash", ""))))

    edge_kind_counts = Counter(str(row.get("translationKind", "") or "") for row in edges)
    edge_tier_counts = Counter(str(row.get("verificationTier", "") or "") for row in edges)
    candidate_kind_counts = Counter(str(row.get("candidateKind", "") or "") for row in candidates)

    return {
        "generated_at": utc_now_iso(),
        "wire_dir": str(wire_dir),
        "translation_dir": str(translation_dir),
        "truth_boundary": "dedup report is advisory; Lean/hash evidence remains authoritative",
        "stats": {
            "declaration_topologies": len(topologies),
            "translation_candidates": len(candidates),
            "verified_candidates": len(verified_candidates),
            "lean_verified_candidates": len(lean_verified_candidates),
            "review_only_candidates": len(review_candidates),
            "verified_translation_edges": len(edges),
            "translation_sccs": len(sccs),
            "nontrivial_translation_sccs": len(verified_sccs),
        },
        "candidate_kind_counts": dict(sorted(candidate_kind_counts.items())),
        "verified_edge_kind_counts": dict(sorted(edge_kind_counts.items())),
        "verified_edge_tier_counts": dict(sorted(edge_tier_counts.items())),
        "exact_buckets": {
            "ownerAwareHash": exact_buckets(topologies, "ownerAwareHash"),
            "patternHash": exact_buckets(topologies, "patternHash"),
            "roleHash": exact_buckets(topologies, "roleHash"),
        },
        "verified_translation_sccs": verified_sccs,
        "top_vector_review_candidates": sorted(
            vector_review,
            key=lambda row: -float((row.get("signals") or {}).get("logicVectorCosine", 0.0) or 0.0),
        )[:50],
        "top_verified_edges": sorted(
            edges,
            key=lambda row: (str(row.get("translationKind", "")), str(row.get("sourceDecl", "")), str(row.get("targetDecl", ""))),
        )[:100],
    }


def build_markdown(report: dict[str, Any]) -> str:
    stats = report["stats"]
    lines: list[str] = []
    lines.append("# Translation Dedup Report")
    lines.append("")
    lines.append(f"- generated_at: `{report.get('generated_at', '')}`")
    lines.append(f"- wire_dir: `{report.get('wire_dir', '')}`")
    lines.append(f"- translation_dir: `{report.get('translation_dir', '')}`")
    lines.append(f"- truth_boundary: `{report.get('truth_boundary', '')}`")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    for key, value in stats.items():
        lines.append(f"- {key}: `{value}`")
    lines.append("")
    lines.append("## Candidate Kinds")
    lines.append("")
    for key, value in report.get("candidate_kind_counts", {}).items():
        lines.append(f"- `{key}`: `{value}`")
    lines.append("")
    lines.append("## Verified Edge Kinds")
    lines.append("")
    for key, value in report.get("verified_edge_kind_counts", {}).items():
        lines.append(f"- `{key}`: `{value}`")
    lines.append("")
    lines.append("## Verification Tiers")
    lines.append("")
    for key, value in report.get("verified_edge_tier_counts", {}).items():
        lines.append(f"- `{key}`: `{value}`")
    lines.append("")
    lines.append("## Exact Hash Buckets")
    lines.append("")
    for hash_kind, buckets in report.get("exact_buckets", {}).items():
        lines.append(f"### {hash_kind}")
        lines.append("")
        if not buckets:
            lines.append("_No nontrivial buckets._")
            lines.append("")
            continue
        lines.append("| count | hash | declarations |")
        lines.append("|---:|---|---|")
        for row in buckets[:30]:
            decls = ", ".join(row.get("declarations", [])[:12])
            if len(row.get("declarations", [])) > 12:
                decls += ", ..."
            lines.append(f"| {row.get('count', 0)} | `{str(row.get('hash', ''))[:24]}` | {decls} |")
        lines.append("")
    lines.append("## Verified Translation SCCs")
    lines.append("")
    sccs = report.get("verified_translation_sccs", [])
    if not sccs:
        lines.append("_No nontrivial verified translation SCCs._")
    else:
        lines.append("| members | translationSccHash | declarations |")
        lines.append("|---:|---|---|")
        for row in sccs[:50]:
            members = ", ".join(row.get("members", [])[:16])
            if len(row.get("members", [])) > 16:
                members += ", ..."
            lines.append(f"| {row.get('memberCount', 0)} | `{str(row.get('translationSccHash', ''))[:24]}` | {members} |")
    lines.append("")
    lines.append("## Top Vector Review Candidates")
    lines.append("")
    vector_rows = report.get("top_vector_review_candidates", [])
    if not vector_rows:
        lines.append("_No vector-near review candidates._")
    else:
        lines.append("| cosine | source | target | reviewOnly |")
        lines.append("|---:|---|---|---|")
        for row in vector_rows[:50]:
            signals = row.get("signals") or {}
            lines.append(
                f"| {float(signals.get('logicVectorCosine', 0.0) or 0.0):.6f} "
                f"| `{row.get('sourceDecl', '')}` | `{row.get('targetDecl', '')}` | `{row.get('reviewOnly', True)}` |"
            )
    lines.append("")
    return "\n".join(lines) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wire-dir", type=Path, default=DEFAULT_WIRE_DIR)
    parser.add_argument("--translation-dir", type=Path, default=DEFAULT_TRANSLATION_DIR)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON_OUT)
    parser.add_argument("--md-out", type=Path, default=DEFAULT_MD_OUT)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    report = build_report(args.wire_dir, args.translation_dir)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")
    args.md_out.parent.mkdir(parents=True, exist_ok=True)
    args.md_out.write_text(build_markdown(report), encoding="utf-8")
    print(f"Translation dedup report written: {args.json_out} {args.md_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
