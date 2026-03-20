#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from pathing import repo_root
else:
    from tools.pathing import repo_root


DEFAULT_FRONTIER_JSON = "reports/dag/skynet-v2-frontier-reverse.json"
DEFAULT_OUT = "skills/info-geometry-repo/references/bridge-candidates.md"


def normalize_user_path(path: str | None, default: Path) -> Path:
    if not path:
        return default
    candidate = Path(path)
    if candidate.is_absolute():
        return candidate
    return (repo_root() / candidate).resolve()


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Generate a report-only bridge-candidate packet directly from a trusted "
            "Skynet v2 frontier JSON."
        )
    )
    ap.add_argument(
        "--frontier-json",
        default=DEFAULT_FRONTIER_JSON,
        help="Trusted frontier JSON to consume.",
    )
    ap.add_argument(
        "--out",
        default=DEFAULT_OUT,
        help="Markdown packet path to write.",
    )
    ap.add_argument(
        "--top",
        type=int,
        default=5,
        help="Number of frontier rows to turn into candidate sections.",
    )
    return ap.parse_args()


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def safe_slug(value: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9_]+", "_", value)
    slug = re.sub(r"_+", "_", slug).strip("_")
    return slug or "candidate"


def decl_tail(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def infer_transport_shape(decl_name: str) -> tuple[str, str]:
    lower = decl_name.lower()
    if "invariant" in lower:
        return (
            "transport / invariance theorem",
            "close an invariance step feeding the frontier declaration",
        )
    if "equivalence" in lower or "correspondence" in lower:
        return (
            "equivalence / correspondence theorem",
            "close a two-way bridge feeding the frontier declaration",
        )
    if "package" in lower or "launchpad" in lower:
        return (
            "package reduction theorem",
            "replace package-level forwarding with a direct derivation of the target package",
        )
    if "_eq_" in lower or lower.endswith("_eq"):
        return (
            "transport equality theorem",
            "derive a nontrivial equality that feeds the frontier declaration",
        )
    return (
        "bridge theorem",
        "insert a small bridge theorem feeding the frontier declaration",
    )


def risk_from_row(row: dict[str, Any]) -> str:
    module_status = str(row.get("moduleStatus") or "")
    adjustments = row.get("scoreAdjustments", [])
    if any(
        item.get("kind") in {"thinness_debt_bonus", "surrogate_debt_bonus", "vacuity_debt_bonus"}
        for item in adjustments
    ):
        return "medium"
    if module_status in {"packaging_heavy_bridge_surface", "mixed_capstone_surface"}:
        return "medium"
    return "low"


def display_source_file(row: dict[str, Any]) -> str:
    return str(row.get("repoSourceFile") or row.get("sourceFile", "unknown"))


def signature_sketch(seed_name: str, row: dict[str, Any], ordinal: int) -> str:
    target = str(row.get("primaryProduces", ["unknown_target"])[0])
    slug = safe_slug(decl_tail(target))
    shape, _ = infer_transport_shape(target)
    return "\n".join(
        [
            f"theorem auto_{slug}_from_seed_{ordinal}",
            f"    -- seed anchor: `{seed_name}`",
            f"    -- frontier target: `{target}`",
            f"    -- intended role: {shape}",
            "    (... local hypotheses specialized to the target declaration ...)",
            "    : (... direct transport / invariance / closure statement feeding the frontier ...) := by",
            "  -- quarantine sketch only",
        ]
    )


def candidate_name(seed_name: str, row: dict[str, Any], ordinal: int) -> str:
    target = str(row.get("primaryProduces", ["unknown_target"])[0])
    return f"AutoCandidate.{safe_slug(decl_tail(target))}_from_{safe_slug(decl_tail(seed_name))}_{ordinal}"


def render_packet(frontier_obj: dict[str, Any], top: int) -> str:
    seed_names = [str(x) for x in frontier_obj.get("seedNames", [])]
    frontier = list(frontier_obj.get("frontier", []))[:top]
    audit_signals = frontier_obj.get("auditSignals", {})
    node_count = frontier_obj.get("nodeCount", "?")
    edge_count = frontier_obj.get("edgeCount", "?")
    cross_edges = frontier_obj.get("crossModuleEdgesAdded", "?")
    walk = str(frontier_obj.get("walk", "unknown"))
    seed_name = seed_names[0] if seed_names else "seed"

    lines: list[str] = []
    lines.append("# Bridge Candidates")
    lines.append("")
    lines.append("This note is a report-only frontier packet derived from the current trusted")
    lines.append("`Skynet v2` semantic frontier.")
    lines.append("")
    lines.append("It is not a proof artifact.")
    lines.append("")
    lines.append("The purpose is to pin the first small bridge lemmas suggested by the current")
    lines.append("frontier, ranked with debt-aware scheduling signals.")
    lines.append("")
    lines.append("## Trusted Graph Context")
    lines.append("")
    lines.append("Current trusted semantic graph facts:")
    lines.append("")
    lines.append("- `Skynet v2` graph:")
    lines.append(f"  - `{node_count}` nodes")
    lines.append(f"  - `{edge_count}` edges")
    lines.append(f"  - `{cross_edges}` cross-module edges")
    lines.append(f"- walk mode: `{walk}`")
    lines.append("- audit signals:")
    lines.append(f"  - thinness findings: `{audit_signals.get('thinnessCount', '?')}`")
    lines.append(f"  - vacuity findings: `{audit_signals.get('vacuityCount', '?')}`")
    lines.append(f"  - surrogate findings: `{audit_signals.get('surrogateCount', '?')}`")
    lines.append(f"  - unification modules tracked: `{audit_signals.get('unificationModuleCount', '?')}`")
    lines.append("- seed declarations:")
    for seed in seed_names:
        lines.append(f"  - `{seed}`")

    for ordinal, row in enumerate(frontier, start=1):
        target = str(row.get("primaryProduces", ["unknown_target"])[0])
        source_file = display_source_file(row)
        _, why_line = infer_transport_shape(target)
        adjustments = row.get("scoreAdjustments", [])
        raw_score = float(row.get("rawScore", 0.0))
        priority_score = float(row.get("score", raw_score))
        module_status = str(row.get("moduleStatus") or "untracked")
        adjustment_summary = ", ".join(
            f"{item.get('kind', 'adjustment')} {float(item.get('value', 0.0)):+.3f}"
            for item in adjustments
        ) or "none"
        lines.extend(
            [
                "",
                f"## Candidate {ordinal}",
                "",
                "`name`",
                "",
                f"`{candidate_name(seed_name, row, ordinal)}`",
                "",
                "`Lean-style signature sketch`",
                "",
                "```lean",
                signature_sketch(seed_name, row, ordinal),
                "```",
                "",
                "`why this closes a real frontier edge`",
                "",
                (
                    f"This candidate is generated directly from the frontier row "
                    f"`{target}` in `{source_file}`. It is intended to {why_line}. "
                    f"The seed-to-frontier link kinds currently visible are "
                    f"`{', '.join(row.get('seedLinkKinds', [])) or '-'}`. "
                    f"The current raw/priority scores are `{raw_score:.6f}` / `{priority_score:.6f}`, "
                    f"with module status `{module_status}` and adjustments `{adjustment_summary}`."
                ),
                "",
                "`likely proof ingredients already present in repo`",
                "",
            ]
        )
        proof_ingredients: list[str] = []
        for detail in row.get("seedLinkDetails", []):
            proof_ingredients.append(str(detail))
        proof_ingredients.append(target)
        proof_ingredients.append(source_file)
        proof_ingredients.append(f"frontier rawScore: {raw_score:.6f}")
        proof_ingredients.append(f"frontier score: {priority_score:.6f}")
        proof_ingredients.append(f"module status: {module_status}")
        for adjustment in adjustments:
            proof_ingredients.append(
                f"score adjustment: {adjustment.get('kind', 'adjustment')} {float(adjustment.get('value', 0.0)):+.3f}"
            )
        deduped: list[str] = []
        seen: set[str] = set()
        for item in proof_ingredients:
            if item in seen:
                continue
            seen.add(item)
            deduped.append(item)
        for item in deduped[:5]:
            lines.append(f"- `{item}`")
        lines.extend(
            [
                "",
                "`risk level`",
                "",
                f"`{risk_from_row(row)}`",
            ]
        )

    if not frontier:
        lines.extend(
            [
                "",
                "## Candidate 1",
                "",
                "`name`",
                "",
                "`AutoCandidate.no_frontier_available`",
                "",
                "`Lean-style signature sketch`",
                "",
                "```lean",
                "theorem auto_no_frontier_available",
                "    : Prop := by",
                "  -- no frontier rows were available",
                "```",
                "",
                "`why this closes a real frontier edge`",
                "",
                "No frontier rows were available in the input JSON.",
                "",
                "`likely proof ingredients already present in repo`",
                "",
                "- none",
                "",
                "`risk level`",
                "",
                "`high`",
            ]
        )

    lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    args = parse_args()
    frontier_json = normalize_user_path(args.frontier_json, repo_root() / args.frontier_json)
    out_path = normalize_user_path(args.out, repo_root() / args.out)
    frontier_obj = load_json(frontier_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(render_packet(frontier_obj, top=args.top), encoding="utf-8")
    print(f"[generate-bridge-candidates] wrote {out_path}")
    print(f"[generate-bridge-candidates] frontier_rows={len(frontier_obj.get('frontier', []))} emitted={min(args.top, len(frontier_obj.get('frontier', [])))}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
