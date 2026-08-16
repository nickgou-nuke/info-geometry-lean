#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import repo_root
else:
    from tools.pathing import repo_root


DEFAULT_STRUCTURAL_HOTSPOTS = "reports/dag/structural-hotspots.json"


def parse_args() -> argparse.Namespace:
    root = repo_root()
    ap = argparse.ArgumentParser(
        description=(
            "Select actionable OpenClaw targets from graph-coverage gaps first and "
            "native structural hotspots second."
        )
    )
    ap.add_argument(
        "--input",
        default=str(root / "reports" / "dag" / "true-root-order.json"),
        help="Path to true-root-order.json.",
    )
    ap.add_argument(
        "--structural-hotspots",
        default=str(root / DEFAULT_STRUCTURAL_HOTSPOTS),
        help="Path to structural-hotspots.json.",
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
    ap.add_argument("--top-structural", type=int, default=12)
    ap.add_argument("--top-uncovered", type=int, default=10)
    return ap.parse_args()


def load_json_file(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    raw = json.loads(path.read_text(encoding="utf-8"))
    return raw if isinstance(raw, dict) else {}


def seed_for_row(row: dict[str, Any]) -> str:
    top_root = str(row.get("top_root_witness", ""))
    if top_root:
        return top_root
    supporting = row.get("supporting_atomic_decls", [])
    if supporting:
        return str(supporting[0])
    return str(row.get("module", row.get("label", "KasparovCycle.analyticalIndex")))


# [lossless-compact] slugify folded into igf.common.strings.slugify
from igf.common.strings import slugify


def make_structural_commands(row: dict[str, Any], bucket: str) -> dict[str, str]:
    seed = seed_for_row(row)
    slug = slugify(seed)
    frontier_json = f"reports/dag/skynet-v2-frontier-{bucket}-{slug}.json"
    frontier_md = f"reports/dag/skynet-v2-frontier-{bucket}-{slug}.md"
    return {
        "seed": seed,
        "skynet": (
            f"python3 tools/skynet_v2.py --seed {json.dumps(seed)} --walk reverse "
            f"--json-out {json.dumps(frontier_json)} --md-out {json.dumps(frontier_md)}"
        ),
        "optimization_cycle": (
            f"python3 tools/run_optimization_cycle.py --frontier-json {json.dumps(frontier_json)} "
            f"--frontier-index 0 --fresh-worktree"
        ),
    }


def make_uncovered_debt_commands(row: dict[str, Any]) -> dict[str, str]:
    file_name = str(row.get("file", ""))
    lines = row.get("lines", [])
    start = 1
    end = 80
    if lines:
        start = max(1, int(lines[0]) - 8)
        end = int(lines[0]) + 8
    inspect_cmd = f"sed -n '{start},{end}p' {json.dumps(file_name)}"
    return {
        "inspect": inspect_cmd,
        "refresh": "python3 tools/update_repo_docs.py --skip-frontier",
    }


def normalize_uncovered_debt_rows(coverage: dict[str, Any], limit: int) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for row in coverage.get("uncovered_debt_files", []):
        enriched = {
            "label": str(row.get("file", "")),
            "file": str(row.get("file", "")),
            "debt": float(row.get("score", 0.0)),
            "finding_count": int(row.get("finding_count", 0)),
            "priorities": list(row.get("priorities", [])),
            "categories": list(row.get("categories", [])),
            "lines": list(row.get("lines", [])),
        }
        enriched["target_score"] = round(4.0 * enriched["debt"] + 2.0 * enriched["finding_count"], 4)
        enriched["recommended"] = make_uncovered_debt_commands(enriched)
        rows.append(enriched)
    rows.sort(
        key=lambda row: (
            -float(row["target_score"]),
            -float(row.get("debt", 0.0)),
            -int(row.get("finding_count", 0)),
            row.get("file", ""),
        )
    )
    return rows[:limit]


def normalize_structural_rows(
    structural_payload: dict[str, Any],
    limit: int,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    rows = [row for row in structural_payload.get("rows", []) if isinstance(row, dict)]
    for row in rows:
        row.setdefault("label", str(row.get("module", row.get("hydrated_id", ""))))
        row.setdefault("target_score", round(float(row.get("selector_score", 0.0)), 4))
        row["recommended"] = make_structural_commands(row, "structural-hotspot")
    rows.sort(
        key=lambda row: (
            -float(row.get("selector_score", 0.0)),
            -int(row.get("bleed_source_count", 0)),
            -int(row.get("bleed_missing_mass", 0)),
            -int(row.get("native_dominator_pressure", 0)),
            -int(row.get("native_corridor_reuse", 0)),
            row.get("module", row.get("hydrated_id", "")),
        )
    )
    summary = structural_payload.get("summary", {})
    if not isinstance(summary, dict):
        summary = {}
    return rows[:limit], summary


def build_payload(
    causal_payload: dict[str, Any],
    structural_payload: dict[str, Any],
    args: argparse.Namespace,
) -> dict[str, Any]:
    summary = causal_payload.get("summary", {})
    if not isinstance(summary, dict):
        summary = {}
    orientation = causal_payload.get("orientation", {})
    if not isinstance(orientation, dict):
        orientation = {}
    coverage = causal_payload.get("coverage", {})
    if not isinstance(coverage, dict):
        coverage = {}

    uncovered_debt_targets = normalize_uncovered_debt_rows(coverage, args.top_uncovered)
    structural_targets, structural_summary = normalize_structural_rows(
        structural_payload, args.top_structural
    )

    primary_target: dict[str, Any] | None = None
    if uncovered_debt_targets:
        primary_target = {"bucket": "uncovered_debt", **uncovered_debt_targets[0]}
    elif structural_targets:
        primary_target = {"bucket": "structural_hotspot", **structural_targets[0]}

    return {
        "source": {
            "true_root_order_summary": summary,
            "orientation": orientation,
            "coverage": coverage,
            "structural_hotspots_summary": structural_summary,
        },
        "selection_policy": {
            "uncovered_debt": "If declaration-bearing files are outside graph coverage, target those first.",
            "structural_hotspot": "Otherwise select directly from native structural hotspots ranked by anti-bleed pressure, dominator pressure, and corridor reuse.",
        },
        "primary_target": primary_target,
        "uncovered_debt_targets": uncovered_debt_targets,
        "structural_hotspot_targets": structural_targets,
    }


def render_primary(lines: list[str], primary: dict[str, Any] | None) -> None:
    lines.append("## Primary Target")
    if not primary:
        lines.append("- none")
        lines.append("")
        return

    bucket = str(primary.get("bucket", ""))
    if bucket == "uncovered_debt":
        lines.append(
            f"- `{primary.get('label')}` from `{bucket}` | score `{primary.get('target_score')}` | debt `{primary.get('debt')}` | findings `{primary.get('finding_count')}` | priorities `{', '.join(primary.get('priorities', [])) or '-'}`"
        )
        rec = primary.get("recommended", {})
        lines.append(f"- inspect: `{rec.get('inspect', '')}`")
        lines.append(f"- refresh: `{rec.get('refresh', '')}`")
        lines.append("")
        return

    lines.append(
        f"- `{primary.get('label')}` from `{bucket}` | score `{primary.get('target_score')}` | bleed-src `{primary.get('bleed_source_count', 0)}` | bleed-tgt `{primary.get('bleed_target_count', 0)}` | missing `{primary.get('bleed_missing_mass', 0)}` | dom-pressure `{primary.get('native_dominator_pressure', 0)}` | corridor-reuse `{primary.get('native_corridor_reuse', 0)}`"
    )
    lines.append(f"- anchor-status: `{primary.get('anchor_status', '-')}`")
    rec = primary.get("recommended", {})
    lines.append(f"- seed: `{rec.get('seed', '')}`")
    lines.append(f"- skynet: `{rec.get('skynet', '')}`")
    lines.append(f"- optimization: `{rec.get('optimization_cycle', '')}`")
    lines.append("")


def render_markdown(result: dict[str, Any]) -> str:
    source = result.get("source", {})
    summary = source.get("true_root_order_summary", {})
    coverage = source.get("coverage", {})
    structural = source.get("structural_hotspots_summary", {})

    lines: list[str] = []
    lines.append("# OpenClaw Target Selector")
    lines.append("")
    lines.append(
        "This report selects operational targets from graph coverage first and native structural hotspots second."
    )
    lines.append("")
    lines.append("## Source Summary")
    lines.append(f"- declaration nodes: `{summary.get('declaration_nodes', 0)}`")
    lines.append(f"- SCC components: `{summary.get('scc_components', 0)}`")
    lines.append(f"- layers: `{summary.get('layers', 0)}`")
    lines.append(f"- roots: `{summary.get('roots', 0)}`")
    lines.append(f"- capstones: `{summary.get('capstones', 0)}`")
    lines.append(f"- structural active carriers: `{structural.get('active_carrier_count', 0)}`")
    lines.append(f"- structural top selector score: `{structural.get('top_selector_score', 0.0)}`")
    if coverage:
        lines.append(
            f"- declaration-index files: `{coverage.get('decl_index_files', 0)}` / declaration-bearing source files `{coverage.get('repo_decl_files', coverage.get('repo_lean_files', 0))}`"
        )
        lines.append(
            f"- import-only / umbrella Lean files: `{coverage.get('import_only_files_count', 0)}`"
        )
        lines.append(
            f"- missing declaration-bearing files from graph coverage: `{coverage.get('missing_decl_files_count', coverage.get('missing_repo_files_count', 0))}`"
        )
        lines.append(
            f"- debt files outside graph coverage: `{coverage.get('uncovered_debt_file_count', 0)}`"
        )
    lines.append("")

    render_primary(lines, result.get("primary_target"))

    lines.append("## Uncovered Debt Targets")
    if not result.get("uncovered_debt_targets"):
        lines.append("- none")
    else:
        for row in result["uncovered_debt_targets"]:
            rec = row.get("recommended", {})
            lines.append(
                f"- `{row.get('label')}` | score `{row.get('target_score')}` | debt `{row.get('debt')}` | findings `{row.get('finding_count')}` | priorities `{', '.join(row.get('priorities', [])) or '-'}`"
            )
            lines.append(f"- inspect: `{rec.get('inspect', '')}`")
            lines.append(f"- refresh: `{rec.get('refresh', '')}`")
    lines.append("")

    lines.append("## Structural Hotspot Targets")
    if not result.get("structural_hotspot_targets"):
        lines.append("- none")
    else:
        for row in result["structural_hotspot_targets"]:
            rec = row.get("recommended", {})
            lines.append(
                f"- `{row.get('label')}` | score `{row.get('target_score')}` | bleed-src `{row.get('bleed_source_count', 0)}` | bleed-tgt `{row.get('bleed_target_count', 0)}` | missing `{row.get('bleed_missing_mass', 0)}` | dom-pressure `{row.get('native_dominator_pressure', 0)}` | corridor-reuse `{row.get('native_corridor_reuse', 0)}`"
            )
            lines.append(f"- anchor-status: `{row.get('anchor_status', '-')}`")
            lines.append(f"- seed: `{rec.get('seed', '')}`")
            lines.append(f"- skynet: `{rec.get('skynet', '')}`")
            lines.append(f"- optimization: `{rec.get('optimization_cycle', '')}`")
    lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    args = parse_args()
    causal_payload = load_json_file(Path(args.input))
    structural_payload = load_json_file(Path(args.structural_hotspots))
    result = build_payload(causal_payload, structural_payload, args)

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
