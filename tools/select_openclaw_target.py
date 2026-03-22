#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


NOISE_LABEL_PATTERNS = (
    '._',
    '.inj',
    '.rec',
    '.casesOn',
    '.match_',
    '.proof_',
    '.brecOn',
    '.below',
    '.sizeOf_spec',
)

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from pathing import repo_root
else:
    from tools.pathing import repo_root


def parse_args() -> argparse.Namespace:
    root = repo_root()
    ap = argparse.ArgumentParser(
        description=(
            "Rank actionable OpenClaw targets from the absolute causal-order report. "
            "This turns root-depth stratigraphy into concrete Skynet and optimization-cycle next steps."
        )
    )
    ap.add_argument(
        "--input",
        default=str(root / "reports" / "dag" / "true-root-order.json"),
        help="Path to true-root-order.json.",
    )
    ap.add_argument(
        "--json-out",
        default=str(root / "reports" / "dag" / "openclaw-targets.json"),
        help="Output JSON payload path.",
    )
    ap.add_argument(
        "--md-out",
        default=str(root / "reports" / "dag" / "openclaw-targets.md"),
        help="Output markdown report path.",
    )
    ap.add_argument(
        "--top-bedrock",
        type=int,
        default=12,
        help="How many soft-bedrock targets to emit.",
    )
    ap.add_argument(
        "--top-young",
        type=int,
        default=12,
        help="How many low-depth soft-support targets to emit.",
    )
    ap.add_argument(
        "--top-capstones",
        type=int,
        default=10,
        help="How many fragile capstones to emit.",
    )
    ap.add_argument(
        "--young-max-depth",
        type=int,
        default=2,
        help="Maximum depth for the low-depth support bucket.",
    )
    return ap.parse_args()


def slugify(value: str) -> str:
    slug = re.sub(r"[^a-zA-Z0-9]+", "-", value).strip("-").lower()
    return slug or "target"


def seed_for_component(row: dict[str, Any]) -> str:
    members = row.get("members", [])
    if members:
        return str(members[0])
    label = str(row.get("label", ""))
    return label.split(" (+", 1)[0] if label else "KasparovCycle.analyticalIndex"


def is_operational_label(label: str) -> bool:
    return not any(pattern in label for pattern in NOISE_LABEL_PATTERNS)


def root_bonus(note: str) -> float:
    lowered = note.lower()
    if "soft bedrock" in lowered:
        return 16.0
    if "bedrock" in lowered:
        return 8.0
    if "capstone" in lowered:
        return -4.0
    return 0.0


def capstone_bonus(note: str) -> float:
    lowered = note.lower()
    if "capstone" in lowered:
        return 10.0
    if "soft bedrock" in lowered:
        return -3.0
    if "bedrock" in lowered:
        return -1.0
    return 0.0


def soft_bedrock_score(row: dict[str, Any]) -> float:
    load = float(row.get("load", 0.0))
    debt = float(row.get("debt", 0.0))
    inertia = float(row.get("inertia", 0.0))
    depth = float(row.get("depth_max", 0))
    cap_support = float(row.get("capstones_supported", 0.0))
    note = str(row.get("note", ""))
    return (
        4.0 * load
        + 3.0 * debt
        + 2.0 * cap_support
        - 1.5 * inertia
        - 1.0 * depth
        + root_bonus(note)
    )


def young_support_score(row: dict[str, Any]) -> float:
    load = float(row.get("load", 0.0))
    debt = float(row.get("debt", 0.0))
    inertia = float(row.get("inertia", 0.0))
    depth = float(row.get("depth_max", 0))
    note = str(row.get("note", ""))
    return 3.0 * load + 2.0 * debt - 1.5 * inertia - 0.75 * depth + root_bonus(note)


def fragile_capstone_score(row: dict[str, Any]) -> float:
    load = float(row.get("load", 0.0))
    debt = float(row.get("debt", 0.0))
    inertia = float(row.get("inertia", 0.0))
    depth = float(row.get("depth_max", 0))
    note = str(row.get("note", ""))
    chain = row.get("longest_chain", [])
    return 2.0 * depth + 1.5 * debt + 1.0 * load - 1.75 * inertia + 0.25 * len(chain) + capstone_bonus(note)


def skynet_paths(bucket: str, slug: str) -> tuple[str, str]:
    return (
        f"reports/dag/skynet-v2-frontier-{bucket}-{slug}.json",
        f"reports/dag/skynet-v2-frontier-{bucket}-{slug}.md",
    )


def make_recommended_commands(bucket: str, row: dict[str, Any]) -> dict[str, str]:
    seed = seed_for_component(row)
    slug = slugify(seed)
    frontier_json, frontier_md = skynet_paths(bucket, slug)
    skynet_cmd = (
        f"python3 tools/skynet_v2.py --seed {json.dumps(seed)} --walk reverse "
        f"--json-out {json.dumps(frontier_json)} --md-out {json.dumps(frontier_md)}"
    )
    opt_cmd = (
        f"python3 tools/run_optimization_cycle.py --frontier-json {json.dumps(frontier_json)} "
        f"--frontier-index 0 --fresh-worktree"
    )
    return {"seed": seed, "skynet": skynet_cmd, "optimization_cycle": opt_cmd}


def rank_bucket(
    rows: list[dict[str, Any]],
    score_fn,
    bucket: str,
    limit: int,
) -> list[dict[str, Any]]:
    ranked: list[dict[str, Any]] = []
    for row in rows:
        score = score_fn(row)
        enriched = dict(row)
        enriched["target_score"] = round(score, 4)
        enriched["recommended"] = make_recommended_commands(bucket, row)
        ranked.append(enriched)
    ranked.sort(
        key=lambda row: (
            float(row["target_score"]),
            float(row.get("load", 0.0)),
            float(row.get("debt", 0.0)),
            -float(row.get("inertia", 0.0)),
            str(row.get("label", "")),
        ),
        reverse=True,
    )
    return ranked[:limit]


def low_depth_components(payload: dict[str, Any], max_depth: int) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for layer in payload.get("layers", []):
        depth = int(layer.get("depth", 10**9))
        if depth > max_depth:
            continue
        for row in layer.get("components", []):
            out.append(row)
    return out


def build_payload(payload: dict[str, Any], args: argparse.Namespace) -> dict[str, Any]:
    roots = payload.get("roots", [])
    low_depth = low_depth_components(payload, args.young_max_depth)
    capstones = payload.get("deepest_capstones", [])
    root_ids = {row.get("id") for row in roots}

    soft_bedrock_rows = [
        row
        for row in roots
        if "soft bedrock" in str(row.get("note", "")).lower()
        and is_operational_label(str(row.get("label", "")))
    ]
    young_support_rows = [
        row
        for row in low_depth
        if row.get("id") not in root_ids
        and float(row.get("debt", 0.0)) > 0.0
        and "capstone" not in str(row.get("note", "")).lower()
        and is_operational_label(str(row.get("label", "")))
    ]
    fragile_capstone_rows = [
        row
        for row in capstones
        if is_operational_label(str(row.get("label", "")))
        and (
            float(row.get("debt", 0.0)) > 0.0
            or float(row.get("inertia", 0.0)) < float(row.get("load", 0.0))
        )
    ]

    ranked_bedrock = rank_bucket(soft_bedrock_rows, soft_bedrock_score, "soft-bedrock", args.top_bedrock)
    ranked_young = rank_bucket(young_support_rows, young_support_score, "young-support", args.top_young)
    ranked_capstones = rank_bucket(
        fragile_capstone_rows, fragile_capstone_score, "fragile-capstone", args.top_capstones
    )

    primary_target = None
    if ranked_bedrock:
        primary_target = {"bucket": "soft_bedrock", **ranked_bedrock[0]}
    elif ranked_young:
        primary_target = {"bucket": "young_support", **ranked_young[0]}
    elif ranked_capstones:
        primary_target = {"bucket": "fragile_capstone", **ranked_capstones[0]}

    return {
        "source": {
            "true_root_order_summary": payload.get("summary", {}),
            "orientation": payload.get("orientation", {}),
        },
        "selection_policy": {
            "soft_bedrock": "Prefer low-depth high-load debt-bearing roots because they stabilize the largest causal cone.",
            "young_support": "Prefer low-depth debt-bearing support nodes after roots; these are next-best structural hardening targets.",
            "fragile_capstone": "Use only after bedrock/support hardening or when targeting synthesis-specific debt.",
        },
        "primary_target": primary_target,
        "soft_bedrock_targets": ranked_bedrock,
        "young_support_targets": ranked_young,
        "fragile_capstone_targets": ranked_capstones,
    }


def render_markdown(result: dict[str, Any]) -> str:
    summary = result.get("source", {}).get("true_root_order_summary", {})
    lines: list[str] = []
    lines.append("# OpenClaw Target Selector")
    lines.append("")
    lines.append("This report converts absolute causal stratigraphy into ranked operational targets.")
    lines.append("")
    lines.append("Selection policy:")
    lines.append("- prioritize soft bedrock before deep capstones")
    lines.append("- prefer high reverse load and real debt over raw chain length")
    lines.append("- use fragile capstones only after support hardening or for synthesis-specific passes")
    lines.append("")
    lines.append("## Source Summary")
    lines.append(f"- declaration nodes: `{summary.get('declaration_nodes', 0)}`")
    lines.append(f"- SCC components: `{summary.get('scc_components', 0)}`")
    lines.append(f"- layers: `{summary.get('layers', 0)}`")
    lines.append(f"- roots: `{summary.get('roots', 0)}`")
    lines.append(f"- capstones: `{summary.get('capstones', 0)}`")
    lines.append("")

    primary = result.get("primary_target")
    lines.append("## Primary Target")
    if primary:
        lines.append(
            f"- `{primary.get('label')}` from `{primary.get('bucket')}` "
            f"| score `{primary.get('target_score')}` "
            f"| load `{primary.get('load')}` "
            f"| debt `{primary.get('debt')}` "
            f"| inertia `{primary.get('inertia')}`"
        )
        rec = primary.get("recommended", {})
        lines.append(f"- seed: `{rec.get('seed', '')}`")
        lines.append(f"- skynet: `{rec.get('skynet', '')}`")
        lines.append(f"- optimization: `{rec.get('optimization_cycle', '')}`")
    else:
        lines.append("- none")
    lines.append("")

    sections = [
        ("Soft Bedrock Targets", "soft_bedrock_targets"),
        ("Young Support Targets", "young_support_targets"),
        ("Fragile Capstone Targets", "fragile_capstone_targets"),
    ]
    for title, key in sections:
        lines.append(f"## {title}")
        rows = result.get(key, [])
        if not rows:
            lines.append("- none")
            lines.append("")
            continue
        for row in rows:
            rec = row.get("recommended", {})
            lines.append(
                f"- `{row.get('label')}` | score `{row.get('target_score')}` | depth `{row.get('depth_max')}` "
                f"| load `{row.get('load')}` | debt `{row.get('debt')}` | inertia `{row.get('inertia')}`"
            )
            lines.append(f"  seed: `{rec.get('seed', '')}`")
            lines.append(f"  skynet: `{rec.get('skynet', '')}`")
            lines.append(f"  optimization: `{rec.get('optimization_cycle', '')}`")
        lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    args = parse_args()
    payload = json.loads(Path(args.input).read_text(encoding="utf-8"))
    result = build_payload(payload, args)

    json_out = Path(args.json_out)
    md_out = Path(args.md_out)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    md_out.write_text(render_markdown(result), encoding="utf-8")

    print(f"[select-openclaw-target] wrote {json_out}")
    print(f"[select-openclaw-target] wrote {md_out}")
    primary = result.get("primary_target")
    if primary:
        print(
            "[select-openclaw-target] primary:",
            primary.get("label"),
            f"(bucket={primary.get('bucket')}, score={primary.get('target_score')})",
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
