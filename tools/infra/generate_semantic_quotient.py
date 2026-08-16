#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import normalize_user_path, repo_root
else:
    from tools.pathing import normalize_user_path, repo_root


DEFAULT_HOTSPOTS = "reports/dag/structural-hotspots.json"
DEFAULT_FIBERS = "reports/dag/structural-fibers.json"
DEFAULT_DEDUP = "reports/dag/structural-dedup.json"
DEFAULT_SURFACE = "reports/dag/theorem-surface-index.json"
DEFAULT_JSON_OUT = "reports/dag/semantic-quotient.json"
DEFAULT_MD_OUT = "reports/dag/semantic-quotient.md"

SUSPICIOUS_CATEGORIES = {
    "hypothesis_bridge",
    "package_reprojection",
    "surrogate_or_vacuous",
}


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Coarse-grain the maintained DAG reports into a first semantic quotient: "
            "presentation duplicates, transport projections, and suspicious theorem "
            "surfaces are contracted into their constructive trunks before reranking knots."
        )
    )
    ap.add_argument("--hotspots", default=DEFAULT_HOTSPOTS)
    ap.add_argument("--fibers", default=DEFAULT_FIBERS)
    ap.add_argument("--dedup", default=DEFAULT_DEDUP)
    ap.add_argument("--surface", default=DEFAULT_SURFACE)
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    ap.add_argument("--top", type=int, default=15, help="Rows to show in markdown tables.")
    return ap.parse_args()


# [lossless-compact] load_json folded into igf.common.json_io.load_json
from igf.common.json_io import load_json


def parse_module_list(value: Any) -> list[str]:
    if isinstance(value, list):
        return [str(x).strip() for x in value if str(x).strip()]
    text = str(value or "").strip()
    if not text:
        return []
    return [chunk.strip() for chunk in text.split(",") if chunk.strip()]


def safe_float(value: Any) -> float:
    try:
        return float(value)
    except Exception:
        return 0.0


def is_compatibility_alias_dedup(row: dict[str, Any]) -> bool:
    return (
        str(row.get("relation_subtype", "")) == "compatibility_alias_candidate"
        or str(row.get("recommended_action", "")) == "review_as_alias_family"
    )


def build_surface_maps(payload: dict[str, Any]) -> tuple[dict[str, str], dict[str, dict[str, int]]]:
    decl_category: dict[str, str] = {}
    module_counts: dict[str, dict[str, int]] = defaultdict(
        lambda: {
            "theorem_total": 0,
            "likely_constructive": 0,
            "hypothesis_bridge": 0,
            "package_reprojection": 0,
            "surrogate_or_vacuous": 0,
        }
    )
    for row in payload.get("rows", []):
        if not isinstance(row, dict):
            continue
        name = str(row.get("name", "")).strip()
        module = str(row.get("module", "")).strip()
        category = str(row.get("category", "")).strip()
        kind = str(row.get("kind", "")).strip()
        if name:
            decl_category[name] = category
        if kind != "theorem" or not module:
            continue
        module_counts[module]["theorem_total"] += 1
        if category in module_counts[module]:
            module_counts[module][category] += 1
    return decl_category, dict(module_counts)


def theorem_shell_ratio(counts: dict[str, int]) -> float:
    total = max(1, int(counts.get("theorem_total", 0) or 0))
    weighted = (
        0.5 * int(counts.get("hypothesis_bridge", 0) or 0)
        + 1.0 * int(counts.get("package_reprojection", 0) or 0)
        + 1.25 * int(counts.get("surrogate_or_vacuous", 0) or 0)
    )
    return min(1.0, weighted / total)


def packet_contractibility(packet: dict[str, Any], decl_category: dict[str, str]) -> tuple[float, list[str]]:
    kind = str(packet.get("packet_kind", "")).strip()
    wrappers = int(packet.get("presentation_wrapper_count", 0) or 0)
    endpoint = str(packet.get("candidate_canonical_endpoint", "")).strip()
    endpoint_category = decl_category.get(endpoint, "")

    weight = 0.0
    reasons: list[str] = []
    if kind == "presentation_duplicate":
        weight = 1.0
        reasons.append("presentation_duplicate")
    elif kind == "transport_projection":
        weight = 0.4
        reasons.append("transport_projection")

    if wrappers > 0:
        weight = max(weight, 0.55)
        weight = min(1.0, weight + 0.15)
        reasons.append(f"wrappers:{wrappers}")

    if endpoint_category == "surrogate_or_vacuous":
        weight = min(1.0, max(weight, 0.8) + 0.2)
        reasons.append("surrogate_endpoint")
    elif endpoint_category == "package_reprojection":
        weight = min(1.0, max(weight, 0.7) + 0.15)
        reasons.append("package_endpoint")
    elif endpoint_category == "hypothesis_bridge":
        weight = min(1.0, max(weight, 0.45) + 0.1)
        reasons.append("hypothesis_endpoint")

    return weight, reasons


def classify_residual(retained_score: float, raw_score: float) -> str:
    if raw_score <= 0:
        return "inactive"
    ratio = retained_score / raw_score
    if ratio <= 0.33:
        return "shell_heavy"
    if ratio <= 0.66:
        return "mixed"
    return "constructive_core"


def md_table(headers: list[str], rows: list[list[str]]) -> str:
    out = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join(["---"] * len(headers)) + " |",
    ]
    for row in rows:
        out.append("| " + " | ".join(row) + " |")
    return "\n".join(out)


def main() -> int:
    args = parse_args()
    root = repo_root()
    hotspots_path = normalize_user_path(args.hotspots, root / DEFAULT_HOTSPOTS)
    fibers_path = normalize_user_path(args.fibers, root / DEFAULT_FIBERS)
    dedup_path = normalize_user_path(args.dedup, root / DEFAULT_DEDUP)
    surface_path = normalize_user_path(args.surface, root / DEFAULT_SURFACE)
    json_out = normalize_user_path(args.json_out, root / DEFAULT_JSON_OUT)
    md_out = normalize_user_path(args.md_out, root / DEFAULT_MD_OUT)

    hotspots = load_json(hotspots_path)
    fibers = load_json(fibers_path)
    dedup = load_json(dedup_path)
    surface = load_json(surface_path)

    decl_category, module_surface_counts = build_surface_maps(surface)

    packets_by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)
    packet_rows: list[dict[str, Any]] = []
    for row in fibers.get("packet_fibers", []):
        if not isinstance(row, dict):
            continue
        packet_rows.append(row)
        modules = parse_module_list(row.get("sink_family"))
        for module in modules:
            packets_by_module[module].append(row)

    dedup_by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)
    suppressed_alias_dedup_by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)
    suppressed_alias_dedup_total = 0
    for row in dedup.get("dedup_families", []):
        if not isinstance(row, dict):
            continue
        modules = parse_module_list(row.get("shared_sink_family"))
        if is_compatibility_alias_dedup(row):
            suppressed_alias_dedup_total += 1
            for module in modules:
                suppressed_alias_dedup_by_module[module].append(row)
            continue
        for module in modules:
            dedup_by_module[module].append(row)

    module_rows: list[dict[str, Any]] = []
    contractible_packets: list[dict[str, Any]] = []
    shell_class_counts: Counter[str] = Counter()

    for row in hotspots.get("rows", []):
        if not isinstance(row, dict):
            continue
        module = str(row.get("module", "")).strip()
        raw_score = safe_float(row.get("selector_score"))
        counts = module_surface_counts.get(
            module,
            {
                "theorem_total": 0,
                "likely_constructive": 0,
                "hypothesis_bridge": 0,
                "package_reprojection": 0,
                "surrogate_or_vacuous": 0,
            },
        )
        th_shell = theorem_shell_ratio(counts)
        packet_rows_for_module = packets_by_module.get(module, [])
        packet_total = 0.0
        packet_contractible = 0.0
        packet_contractible_count = 0
        for packet in packet_rows_for_module:
            packet_score = safe_float(packet.get("packet_score"))
            weight, reasons = packet_contractibility(packet, decl_category)
            packet_total += packet_score
            if weight > 0:
                packet_contractible += packet_score * weight
                packet_contractible_count += 1
                contractible_packets.append(
                    {
                        "module": module,
                        "packet_id": str(packet.get("packet_id", "")),
                        "sink_family": str(packet.get("sink_family", "")),
                        "packet_kind": str(packet.get("packet_kind", "")),
                        "candidate_canonical_endpoint": str(packet.get("candidate_canonical_endpoint", "")),
                        "endpoint_category": decl_category.get(
                            str(packet.get("candidate_canonical_endpoint", "")), ""
                        ),
                        "packet_score": packet_score,
                        "contractibility_weight": weight,
                        "contracted_mass": packet_score * weight,
                        "presentation_wrapper_count": int(packet.get("presentation_wrapper_count", 0) or 0),
                        "source_modules": parse_module_list(packet.get("source_modules")),
                        "reasons": reasons,
                    }
                )
        packet_shell = min(1.0, packet_contractible / packet_total) if packet_total > 0 else 0.0

        dedup_rows_for_module = dedup_by_module.get(module, [])
        dedup_score = sum(safe_float(x.get("family_score")) for x in dedup_rows_for_module)
        dedup_norm = min(1.0, dedup_score / max(raw_score, 1.0))
        suppressed_alias_rows_for_module = suppressed_alias_dedup_by_module.get(module, [])
        suppressed_alias_score = sum(safe_float(x.get("family_score")) for x in suppressed_alias_rows_for_module)

        shell_ratio = min(1.0, 0.5 * th_shell + 0.35 * packet_shell + 0.15 * dedup_norm)
        retained_score = raw_score * (1.0 - shell_ratio)
        shell_class = classify_residual(retained_score, raw_score)
        shell_class_counts[shell_class] += 1

        reasons: list[str] = []
        if th_shell >= 0.3:
            reasons.append("theorem-surface shell")
        if packet_shell >= 0.3:
            reasons.append("packet duplication/projection")
        if dedup_norm >= 0.3:
            reasons.append("dedup family overlap")
        if not reasons:
            reasons.append("mostly retained after contraction")

        module_rows.append(
            {
                "module": module,
                "raw_selector_score": raw_score,
                "quotient_retained_score": round(retained_score, 4),
                "quotient_shell_ratio": round(shell_ratio, 4),
                "residual_class": shell_class,
                "top_root_witness": str(row.get("top_root_witness", "")),
                "theorem_total": int(counts.get("theorem_total", 0) or 0),
                "likely_constructive": int(counts.get("likely_constructive", 0) or 0),
                "hypothesis_bridge": int(counts.get("hypothesis_bridge", 0) or 0),
                "package_reprojection": int(counts.get("package_reprojection", 0) or 0),
                "surrogate_or_vacuous": int(counts.get("surrogate_or_vacuous", 0) or 0),
                "theorem_shell_ratio": round(th_shell, 4),
                "packet_count": len(packet_rows_for_module),
                "contractible_packet_count": packet_contractible_count,
                "packet_score_total": round(packet_total, 4),
                "contractible_packet_mass": round(packet_contractible, 4),
                "packet_shell_ratio": round(packet_shell, 4),
                "dedup_family_count": len(dedup_rows_for_module),
                "dedup_family_score": round(dedup_score, 4),
                "suppressed_alias_dedup_family_count": len(suppressed_alias_rows_for_module),
                "suppressed_alias_dedup_family_score": round(suppressed_alias_score, 4),
                "dominant_shell_drivers": reasons,
            }
        )

    module_rows.sort(key=lambda row: (-row["quotient_retained_score"], row["module"]))
    contractible_packets.sort(key=lambda row: (-row["contracted_mass"], row["module"], row["packet_id"]))
    shell_heavy_rows = sorted(
        module_rows,
        key=lambda row: (-(row["raw_selector_score"] - row["quotient_retained_score"]), row["module"]),
    )

    summary = {
        "hotspot_count": len(module_rows),
        "top_raw_module": hotspots.get("rows", [{}])[0].get("module", "") if hotspots.get("rows") else "",
        "top_quotient_module": module_rows[0]["module"] if module_rows else "",
        "top_shell_module": shell_heavy_rows[0]["module"] if shell_heavy_rows else "",
        "shell_class_counts": dict(shell_class_counts),
        "contractible_packet_count": len(contractible_packets),
        "suppressed_alias_dedup_family_count": suppressed_alias_dedup_total,
    }

    payload = {
        "kind": "semantic_quotient",
        "inputs": {
            "hotspots": str(hotspots_path),
            "fibers": str(fibers_path),
            "dedup": str(dedup_path),
            "surface": str(surface_path),
        },
        "summary": summary,
        "hotspot_rows": module_rows,
        "contractible_packets": contractible_packets[: max(args.top, 25)],
    }

    md_lines: list[str] = [
        "# Semantic Quotient",
        "",
        "This report contracts presentation-duplicate packets, transport projections, and suspicious theorem-surface shells before reranking structural hotspots.",
        "It is a heuristic quotient, not kernel truth.",
        "",
        "## Summary",
        f"- structural hotspots analyzed: `{summary['hotspot_count']}`",
        f"- top raw hotspot: `{summary['top_raw_module']}`",
        f"- top residual knot after contraction: `{summary['top_quotient_module']}`",
        f"- top shell-heavy hotspot: `{summary['top_shell_module']}`",
        f"- shell classes: `{summary['shell_class_counts']}`",
        f"- contractible packet candidates: `{summary['contractible_packet_count']}`",
        f"- suppressed compatibility-alias dedup families: `{summary['suppressed_alias_dedup_family_count']}`",
        "",
        "## Residual Knots",
        md_table(
            ["Rank", "Module", "Raw", "Residual", "Shell", "Class", "Drivers"],
            [
                [
                    str(idx),
                    f"`{row['module']}`",
                    f"{row['raw_selector_score']:.1f}",
                    f"{row['quotient_retained_score']:.1f}",
                    f"{row['quotient_shell_ratio']:.2f}",
                    row["residual_class"],
                    ", ".join(row["dominant_shell_drivers"]),
                ]
                for idx, row in enumerate(module_rows[: args.top], start=1)
            ],
        ),
        "",
        "## Shell-Heavy Hotspots",
        md_table(
            ["Module", "Raw", "Residual", "Theorem shell", "Packet shell", "Dedup", "Top witness"],
            [
                [
                    f"`{row['module']}`",
                    f"{row['raw_selector_score']:.1f}",
                    f"{row['quotient_retained_score']:.1f}",
                    f"{row['theorem_shell_ratio']:.2f}",
                    f"{row['packet_shell_ratio']:.2f}",
                    f"{row['dedup_family_score']:.1f}",
                    f"`{row['top_root_witness']}`" if row["top_root_witness"] else "-",
                ]
                for row in shell_heavy_rows[: args.top]
            ],
        ),
        "",
        "## Contractible Packet Candidates",
        md_table(
            ["Module", "Packet", "Kind", "Endpoint", "Mass", "Why"],
            [
                [
                    f"`{row['module']}`",
                    f"`{row['packet_id']}`",
                    row["packet_kind"],
                    f"`{row['candidate_canonical_endpoint']}`" if row["candidate_canonical_endpoint"] else "-",
                    f"{row['contracted_mass']:.1f}",
                    ", ".join(row["reasons"]),
                ]
                for row in contractible_packets[: args.top]
            ],
        ),
        "",
        "## Method",
        "- theorem-surface shell uses weighted suspicious theorem categories from `theorem-surface-index.json`",
        "- packet shell contracts `presentation_duplicate` packets by default and discounts `transport_projection` packets",
        "- compatibility-alias dedup families are suppressed from shell pressure by default and reported separately",
        "- dedup families contribute extra shell pressure where a hotspot still carries exact repeated sink surfaces",
        "- residual score = raw structural score after removing the estimated shell ratio",
    ]

    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    md_out.write_text("\n".join(md_lines) + "\n", encoding="utf-8")

    print(f"[semantic-quotient] wrote {json_out}")
    print(f"[semantic-quotient] wrote {md_out}")
    if module_rows:
        top = module_rows[0]
        print(
            "[semantic-quotient] top residual: "
            f"{top['module']} (raw={top['raw_selector_score']:.1f}, residual={top['quotient_retained_score']:.1f})"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
