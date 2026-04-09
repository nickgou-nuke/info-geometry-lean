#!/usr/bin/env python3
from __future__ import annotations

if __package__ in (None, ""):
    import sys

    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
    from tools.infra.reports.common import load_json
    from tools.pathing import repo_root
else:
    from tools.infra.reports.common import load_json
    from tools.pathing import repo_root


def frontier_names(frontier_obj: dict[str, Any], limit: int = 6) -> list[str]:
    out: list[str] = []
    for row in frontier_obj.get("frontier", [])[:limit]:
        produces = row.get("primaryProduces", [])
        if produces:
            out.append(str(produces[0]))
        else:
            out.append(str(row.get("stableId", "")))
    return out


def render_report(both_frontier: dict[str, Any], reverse_frontier: dict[str, Any]) -> str:
    kernel = frontier_names(both_frontier, limit=6)
    downstream = frontier_names(reverse_frontier, limit=8)
    seed_blocks = both_frontier.get("seedBlocks", [])
    seed_names = both_frontier.get("seedNames", [])

    lines: list[str] = []
    lines.append("# Self-Optimization Cycle")
    lines.append("")
    lines.append("Status:")
    lines.append("- generated from current trusted frontier artifacts")
    lines.append("- report-only: this file does not propose direct automatic edits")
    lines.append("- use it as the current cycle sheet for safe graph-guided improvement")
    lines.append("")
    lines.append("## Trusted Snapshot")
    lines.append(f"- walk mode (local kernel): `{both_frontier.get('walk', 'unknown')}`")
    lines.append(f"- walk mode (downstream): `{reverse_frontier.get('walk', 'unknown')}`")
    lines.append(f"- graph nodes: `{both_frontier.get('nodeCount', 0)}`")
    lines.append(f"- graph edges: `{both_frontier.get('edgeCount', 0)}`")
    lines.append(f"- cross-module edges: `{both_frontier.get('crossModuleEdgesAdded', 0)}`")
    lines.append(f"- seed blocks: `{len(seed_blocks)}`")
    if seed_names:
        lines.append(f"- seed declarations: `{', '.join(str(x) for x in seed_names)}`")
    lines.append("")
    lines.append("## Local Bridge Kernel")
    for name in kernel:
        lines.append(f"- `{name}`")
    lines.append("")
    lines.append("## Downstream Consumer Frontier")
    for name in downstream:
        lines.append(f"- `{name}`")
    lines.append("")
    lines.append("## Safe Iteration Loop")
    lines.append("1. Refresh trusted semantic exports and frontier packets.")
    lines.append("2. Select one narrow bridge or cleanup target from the current frontier.")
    lines.append("3. Generate candidate statements or attack plans, not proofs by authority.")
    lines.append("4. Implement in quarantine or a tightly scoped branch/clone.")
    lines.append("5. Validate with targeted builds, then `lake build -R` if promoted.")
    lines.append("6. Refresh the graph and compare the frontier before merging.")
    lines.append("")
    lines.append("## Immediate Recommended Pressure Points")
    lines.append("- strengthen the KK -> AnalyticalIndex bridge layer")
    lines.append("- close more AnalyticalIndex -> GrandSynthesis consumer obligations")
    lines.append("- keep generated proposals out of canonical files until Lean validation")
    lines.append("")
    lines.append("## Canonical Inputs For The Next Cycle")
    lines.append("- `skills/info-geometry-repo/references/frontier-prompt.md`")
    lines.append("- `skills/info-geometry-repo/references/bridge-candidates.md`")
    lines.append("- `docs/auto/index.md`")
    lines.append("- `SELF_OPTIMIZATION_PROTOCOL.md`")
    lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    root = repo_root()
    reports = root / "reports" / "dag"
    both_path = reports / "skynet-v2-frontier.json"
    reverse_path = reports / "skynet-v2-frontier-reverse.json"
    if not both_path.exists() or not reverse_path.exists():
        missing = [str(p.relative_to(root)) for p in (both_path, reverse_path) if not p.exists()]
        raise SystemExit("missing required frontier artifact(s):\n" + "\n".join(f"- {m}" for m in missing))

    both_frontier = load_json(both_path)
    reverse_frontier = load_json(reverse_path)
    out = render_report(both_frontier, reverse_frontier)
    out_path = reports / "self-optimization-cycle.md"
    out_path.write_text(out, encoding="utf-8")
    print(f"[self-opt-report] wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
