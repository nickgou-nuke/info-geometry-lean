#!/usr/bin/env python3
"""Report the authority boundary between triple and kernel certificate layers.

This is a read-only audit/report generator.  It joins materialized
``ig_triple_homomorphism_edges.jsonl`` and ``ig_kernel_equivalence_edges.jsonl``
rows and classifies each pair by the strongest available certificate evidence.

It does not mutate Lean, Arango, JSONL overlays, or SCC artifacts.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


DEFAULT_WIRE_DIR = Path("artifacts/expr-graph/wire-topology")
DEFAULT_TRIPLE_EDGES = DEFAULT_WIRE_DIR / "ig_triple_homomorphism_edges.jsonl"
DEFAULT_KERNEL_EDGES = DEFAULT_WIRE_DIR / "ig_kernel_equivalence_edges.jsonl"
DEFAULT_JSON_OUT = Path("reports/dag/certificate-authority-layers.json")
DEFAULT_MD_OUT = Path("reports/dag/certificate-authority-layers.md")


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


def pair_key_from_edge(row: dict[str, Any]) -> tuple[str, str]:
    return (str(row.get("_from", "") or ""), str(row.get("_to", "") or ""))


def pair_label(row: dict[str, Any]) -> str:
    source = str(row.get("sourceLabel", "") or row.get("sourceDecl", "") or row.get("sourceId", "") or row.get("_from", ""))
    target = str(row.get("targetLabel", "") or row.get("targetDecl", "") or row.get("targetId", "") or row.get("_to", ""))
    return f"{source} -> {target}"


def is_triple_certificate(row: dict[str, Any]) -> bool:
    return str(row.get("kind", "") or "") == "triple_homomorphism_certificate"


def is_missing_triple(row: dict[str, Any]) -> bool:
    return str(row.get("kind", "") or "") == "missing_mapped_triple"


def is_kernel_certificate(row: dict[str, Any]) -> bool:
    return str(row.get("kind", "") or "") == "kernel_equivalence_certificate"


def choose_kernel(rows: list[dict[str, Any]]) -> dict[str, Any] | None:
    if not rows:
        return None
    priority = {
        "rewrite_safe": 3,
        "verified_not_rewrite_safe": 2,
        "rejected": 1,
    }
    return max(
        rows,
        key=lambda row: (
            priority.get(str(row.get("status", "") or ""), 0),
            int(bool(row.get("leanVerified", False))),
            str(row.get("verificationTier", "") or ""),
        ),
    )


def recommended_action(
    triple: dict[str, Any] | None,
    kernel: dict[str, Any] | None,
) -> str:
    if triple is not None and str(triple.get("status", "") or "") == "triple_hom_rejected":
        return "candidate-rejected-with-missing-triples"
    if kernel is not None and str(kernel.get("status", "") or "") == "rewrite_safe":
        return "rewrite-safe-dedup-scc"
    if kernel is not None and str(kernel.get("status", "") or "") == "verified_not_rewrite_safe":
        return "statement-equivalence-review"
    if triple is not None and bool(triple.get("leanVerified", False)) and kernel is None:
        return "structural-equivalence-review"
    if kernel is not None and str(kernel.get("status", "") or "") == "rejected":
        return "kernel-rejected-candidate"
    return "insufficient-certificate-evidence"


def build_pair_row(
    key: tuple[str, str],
    *,
    triple: dict[str, Any] | None,
    kernel: dict[str, Any] | None,
    missing: list[dict[str, Any]],
) -> dict[str, Any]:
    representative = triple or kernel or (missing[0] if missing else {})
    action = recommended_action(triple, kernel)
    return {
        "from": key[0],
        "to": key[1],
        "pair": pair_label(representative),
        "tripleHomStatus": str(triple.get("status", "absent") if triple else "absent"),
        "tripleLeanVerified": bool(triple.get("leanVerified", False)) if triple else False,
        "missingTriples": int(triple.get("missingTriples", len(missing)) or 0) if triple else len(missing),
        "kernelStatus": str(kernel.get("status", "absent") if kernel else "absent"),
        "kernelTier": str(kernel.get("verificationTier", "") if kernel else ""),
        "kernelLeanVerified": bool(kernel.get("leanVerified", False)) if kernel else False,
        "safeForDedupSCC": bool(triple.get("safeForDedupSCC", False)) if triple else False,
        "safeForAutoRewrite": bool(kernel.get("safeForAutoRewrite", False)) if kernel else False,
        "recommendedAction": action,
        "tripleCertificateHash": str(triple.get("certificateHash", "") if triple else ""),
        "kernelCertificateHash": str(kernel.get("certificateHash", "") if kernel else ""),
        "missingTripleHashes": [
            str(row.get("missingTripleHash", "") or "")
            for row in missing
            if str(row.get("missingTripleHash", "") or "")
        ],
    }


def build_report(triple_edges_path: Path, kernel_edges_path: Path) -> dict[str, Any]:
    triple_rows = list(iter_jsonl(triple_edges_path))
    kernel_rows = list(iter_jsonl(kernel_edges_path))

    triples_by_pair: dict[tuple[str, str], dict[str, Any]] = {}
    missing_by_pair: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    kernels_by_pair: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)

    for row in triple_rows:
        key = pair_key_from_edge(row)
        if not key[0] or not key[1]:
            continue
        if is_triple_certificate(row):
            triples_by_pair[key] = row
        elif is_missing_triple(row):
            missing_by_pair[key].append(row)

    for row in kernel_rows:
        key = pair_key_from_edge(row)
        if not key[0] or not key[1] or not is_kernel_certificate(row):
            continue
        kernels_by_pair[key].append(row)

    all_pairs = sorted(set(triples_by_pair) | set(missing_by_pair) | set(kernels_by_pair))
    pair_rows = [
        build_pair_row(
            key,
            triple=triples_by_pair.get(key),
            kernel=choose_kernel(kernels_by_pair.get(key, [])),
            missing=missing_by_pair.get(key, []),
        )
        for key in all_pairs
    ]

    action_counts = Counter(row["recommendedAction"] for row in pair_rows)
    triple_counts = Counter(row["tripleHomStatus"] for row in pair_rows)
    kernel_counts = Counter(row["kernelStatus"] for row in pair_rows)

    return {
        "generated_at": utc_now_iso(),
        "triple_edges_path": str(triple_edges_path),
        "kernel_edges_path": str(kernel_edges_path),
        "truth_boundary": (
            "read-only audit; triple certificates prove finite incidence preservation, "
            "kernel certificates prove Lean definitional equality, and only kernel "
            "safeForAutoRewrite authorizes rewrite materialization"
        ),
        "stats": {
            "triple_edge_rows": len(triple_rows),
            "kernel_edge_rows": len(kernel_rows),
            "pairs": len(pair_rows),
            "triple_certificate_pairs": len(triples_by_pair),
            "kernel_certificate_pairs": len(kernels_by_pair),
            "missing_mapped_triple_edges": sum(len(rows) for rows in missing_by_pair.values()),
        },
        "recommended_action_counts": dict(sorted(action_counts.items())),
        "triple_status_counts": dict(sorted(triple_counts.items())),
        "kernel_status_counts": dict(sorted(kernel_counts.items())),
        "pairs": pair_rows,
    }


def build_markdown(report: dict[str, Any]) -> str:
    lines: list[str] = []
    lines.append("# Certificate Authority Layers Report")
    lines.append("")
    lines.append(f"- generated_at: `{report.get('generated_at', '')}`")
    lines.append(f"- triple_edges_path: `{report.get('triple_edges_path', '')}`")
    lines.append(f"- kernel_edges_path: `{report.get('kernel_edges_path', '')}`")
    lines.append(f"- truth_boundary: `{report.get('truth_boundary', '')}`")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    for key, value in report.get("stats", {}).items():
        lines.append(f"- {key}: `{value}`")
    lines.append("")
    lines.append("## Recommended Actions")
    lines.append("")
    for key, value in report.get("recommended_action_counts", {}).items():
        lines.append(f"- `{key}`: `{value}`")
    lines.append("")
    lines.append("## Pair Classification")
    lines.append("")
    pairs = report.get("pairs", [])
    if not pairs:
        lines.append("_No certificate pairs found._")
        lines.append("")
        return "\n".join(lines)
    lines.append(
        "| action | tripleHomStatus | kernelStatus | missingTriples | safeForDedupSCC | "
        "safeForAutoRewrite | pair |"
    )
    lines.append("|---|---|---|---:|---|---|---|")
    for row in pairs[:200]:
        lines.append(
            f"| `{row.get('recommendedAction', '')}` "
            f"| `{row.get('tripleHomStatus', '')}` "
            f"| `{row.get('kernelStatus', '')}` "
            f"| {row.get('missingTriples', 0)} "
            f"| `{row.get('safeForDedupSCC', False)}` "
            f"| `{row.get('safeForAutoRewrite', False)}` "
            f"| `{row.get('pair', '')}` |"
        )
    lines.append("")
    return "\n".join(lines) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--triple-edges", type=Path, default=DEFAULT_TRIPLE_EDGES)
    parser.add_argument("--kernel-edges", type=Path, default=DEFAULT_KERNEL_EDGES)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON_OUT)
    parser.add_argument("--md-out", type=Path, default=DEFAULT_MD_OUT)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    report = build_report(args.triple_edges, args.kernel_edges)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")
    args.md_out.parent.mkdir(parents=True, exist_ok=True)
    args.md_out.write_text(build_markdown(report), encoding="utf-8")
    print(f"Certificate authority layers report written: {args.json_out} {args.md_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
