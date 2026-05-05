#!/usr/bin/env python3
"""Render a causal/chiral cone prompt packet as a small offline HTML view.

Input is the JSON emitted by:

    tools/infra/arango_causal_chiral_cone_prompt.py

This viewer is intentionally dependency-free.  It is a debug/readability layer
for humans before the packet is fed to an LLM.  It does not prove anything and
it does not recompute graph topology; it only renders the already-derived
packet.
"""

from __future__ import annotations

import argparse
import html
import json
from pathlib import Path
from typing import Any


def _component_key(component: dict[str, Any]) -> str:
    return str(component.get("_key") or component.get("component_key") or component.get("_id") or "")


def _component_label(component: dict[str, Any]) -> str:
    rep = component.get("representative")
    key = _component_key(component)
    if isinstance(rep, str) and rep:
        return rep
    return key


def _short(s: str, limit: int = 72) -> str:
    return s if len(s) <= limit else s[: limit - 1] + "…"


def _overlay_component_keys(packet: dict[str, Any]) -> dict[str, set[str]]:
    overlays = packet.get("overlays") if isinstance(packet.get("overlays"), dict) else {}
    out: dict[str, set[str]] = {
        "chiral": set(),
        "dominators": set(),
        "process": set(),
        "motifs": set(),
    }

    for row in overlays.get("chiral") or []:
        key = row.get("component_key") or row.get("component")
        if key:
            out["chiral"].add(str(key))

    for row in overlays.get("dominators") or []:
        key = row.get("component_key") or row.get("component")
        if key:
            out["dominators"].add(str(key))

    for row in overlays.get("process_flows") or []:
        for field in ("source_key", "target_key"):
            key = row.get(field)
            if key:
                out["process"].add(str(key))

    for row in overlays.get("motifs") or []:
        for key in row.get("mapping_keys") or []:
            out["motifs"].add(str(key))

    return out


def _collect_nodes(packet: dict[str, Any]) -> tuple[dict[str, dict[str, Any]], list[tuple[str, str, str]]]:
    apex = packet.get("apex") if isinstance(packet.get("apex"), dict) else {}
    apex_component = apex.get("component") if isinstance(apex.get("component"), dict) else {}
    apex_key = str(apex.get("component_key") or _component_key(apex_component))

    nodes: dict[str, dict[str, Any]] = {}
    edges: list[tuple[str, str, str]] = []

    if apex_key:
        nodes[apex_key] = {
            "key": apex_key,
            "label": _component_label(apex_component) or str(apex.get("name") or apex_key),
            "depth": 0,
            "side": "apex",
            "component": apex_component,
        }

    for side, packet_key in (("backward", "backward_cone"), ("forward", "forward_cone")):
        rows = packet.get(packet_key) or []
        for row in rows:
            component = row.get("component") if isinstance(row.get("component"), dict) else {}
            key = _component_key(component)
            if not key:
                continue
            depth = int(row.get("depth") or 0)
            prior = nodes.get(key)
            if prior is None or (prior.get("side") != "apex" and depth < int(prior.get("depth") or depth)):
                nodes[key] = {
                    "key": key,
                    "label": _component_label(component),
                    "depth": depth,
                    "side": side,
                    "component": component,
                }

            path_keys = [str(x) for x in (row.get("path_keys") or []) if x is not None]
            if len(path_keys) >= 2:
                for a, b in zip(path_keys, path_keys[1:]):
                    edges.append((a, b, side))
            elif apex_key:
                if side == "backward":
                    edges.append((apex_key, key, side))
                else:
                    edges.append((key, apex_key, side))

    known = set(nodes)
    edges = [(a, b, side) for (a, b, side) in edges if a in known and b in known]
    return nodes, edges


def _layout(nodes: dict[str, dict[str, Any]]) -> dict[str, tuple[float, float]]:
    buckets: dict[tuple[str, int], list[str]] = {}
    for key, node in nodes.items():
        side = str(node.get("side"))
        depth = int(node.get("depth") or 0)
        buckets.setdefault((side, depth), []).append(key)

    for keys in buckets.values():
        keys.sort()

    pos: dict[str, tuple[float, float]] = {}
    center_x = 640.0
    center_y = 360.0
    x_gap = 190.0
    y_gap = 74.0

    for (side, depth), keys in buckets.items():
        if side == "apex":
            x = center_x
        elif side == "backward":
            x = center_x - x_gap * max(depth, 1)
        else:
            x = center_x + x_gap * max(depth, 1)
        start_y = center_y - y_gap * (len(keys) - 1) / 2.0
        for idx, key in enumerate(keys):
            pos[key] = (x, start_y + idx * y_gap)
    return pos


def _render_svg(packet: dict[str, Any]) -> str:
    nodes, edges = _collect_nodes(packet)
    overlays = _overlay_component_keys(packet)
    pos = _layout(nodes)
    width = 1280
    height = 720

    edge_lines: list[str] = []
    for a, b, side in sorted(set(edges)):
        x1, y1 = pos[a]
        x2, y2 = pos[b]
        color = "#6b7280" if side == "backward" else "#2563eb"
        dash = "" if side == "backward" else " stroke-dasharray=\"6 4\""
        edge_lines.append(
            f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
            f'stroke="{color}" stroke-width="1.4" opacity="0.62"{dash} marker-end="url(#arrow)" />'
        )

    node_lines: list[str] = []
    for key, node in sorted(nodes.items(), key=lambda item: (str(item[1].get("side")), int(item[1].get("depth") or 0), item[0])):
        x, y = pos[key]
        side = str(node.get("side"))
        label = html.escape(_short(str(node.get("label") or key), 54))
        key_text = html.escape(_short(key, 28))
        classes = ["node", side]
        badges: list[str] = []
        if key in overlays["chiral"]:
            classes.append("has-chiral")
            badges.append("χ")
        if key in overlays["dominators"]:
            classes.append("has-dominator")
            badges.append("D")
        if key in overlays["process"]:
            classes.append("has-process")
            badges.append("P")
        if key in overlays["motifs"]:
            classes.append("has-motif")
            badges.append("M")
        badge_text = " ".join(badges)
        node_lines.append(
            f'<g class="{" ".join(classes)}">'
            f'<title>{html.escape(str(node.get("label") or key))}</title>'
            f'<rect x="{x - 82:.1f}" y="{y - 24:.1f}" width="164" height="48" rx="12" />'
            f'<text class="label" x="{x:.1f}" y="{y - 4:.1f}">{label}</text>'
            f'<text class="key" x="{x:.1f}" y="{y + 14:.1f}">{key_text}</text>'
            f'<text class="badge" x="{x + 72:.1f}" y="{y - 10:.1f}">{html.escape(badge_text)}</text>'
            f'</g>'
        )

    return f"""
<svg viewBox="0 0 {width} {height}" role="img" aria-label="causal cone graph">
  <defs>
    <marker id="arrow" markerWidth="8" markerHeight="8" refX="7" refY="3" orient="auto" markerUnits="strokeWidth">
      <path d="M0,0 L0,6 L7,3 z" fill="#475569" />
    </marker>
  </defs>
  <text class="axis" x="210" y="38">Backward cone: prerequisites</text>
  <text class="axis" x="560" y="38">Apex</text>
  <text class="axis" x="865" y="38">Forward cone: users / consequences</text>
  {''.join(edge_lines)}
  {''.join(node_lines)}
</svg>
"""


def _render_summary(packet: dict[str, Any]) -> str:
    apex = packet.get("apex") if isinstance(packet.get("apex"), dict) else {}
    overlays = packet.get("overlays") if isinstance(packet.get("overlays"), dict) else {}
    rows = [
        ("Declaration", str(apex.get("name") or "")),
        ("SCC component", str(apex.get("component_key") or "")),
        ("Backward rows", str(len(packet.get("backward_cone") or []))),
        ("Forward rows", str(len(packet.get("forward_cone") or []))),
        ("Chiral rows", str(len(overlays.get("chiral") or []))),
        ("Hodge rows", str(len(overlays.get("hodge") or []))),
        ("Dirac rows", str(len(overlays.get("dirac") or []))),
        ("Motifs", str(len(overlays.get("motifs") or []))),
        ("Process flows", str(len(overlays.get("process_flows") or []))),
        ("Dominators", str(len(overlays.get("dominators") or []))),
    ]
    return "\n".join(
        f"<tr><th>{html.escape(k)}</th><td><code>{html.escape(v)}</code></td></tr>" for k, v in rows
    )


def render_html(packet: dict[str, Any]) -> str:
    schema = html.escape(str(packet.get("schema") or "unknown"))
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8" />
<meta name="viewport" content="width=device-width, initial-scale=1" />
<title>Causal Chiral Cone Packet Viewer</title>
<style>
  :root {{
    color-scheme: light;
    --ink: #172033;
    --muted: #64748b;
    --paper: #f8fafc;
    --panel: #ffffff;
    --line: #cbd5e1;
    --apex: #111827;
    --back: #f59e0b;
    --fwd: #38bdf8;
    --chiral: #ec4899;
    --dom: #16a34a;
    --proc: #7c3aed;
    --motif: #dc2626;
  }}
  body {{
    margin: 0;
    font: 14px/1.45 ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
    color: var(--ink);
    background: radial-gradient(circle at top left, #eef2ff, transparent 34rem), var(--paper);
  }}
  main {{ max-width: 1320px; margin: 0 auto; padding: 28px; }}
  h1 {{ margin: 0 0 4px; font-size: 26px; letter-spacing: -0.02em; }}
  .subtitle {{ color: var(--muted); margin-bottom: 20px; }}
  .grid {{ display: grid; grid-template-columns: 360px 1fr; gap: 18px; align-items: start; }}
  .panel {{
    background: color-mix(in srgb, var(--panel) 92%, transparent);
    border: 1px solid var(--line);
    border-radius: 18px;
    box-shadow: 0 18px 40px rgba(15, 23, 42, 0.08);
    overflow: hidden;
  }}
  .panel h2 {{ margin: 0; padding: 14px 16px; font-size: 15px; border-bottom: 1px solid var(--line); }}
  table {{ width: 100%; border-collapse: collapse; }}
  th, td {{ text-align: left; vertical-align: top; padding: 8px 12px; border-bottom: 1px solid #e2e8f0; }}
  th {{ color: var(--muted); font-weight: 650; width: 120px; }}
  code {{ font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; font-size: 12px; }}
  .legend {{ padding: 12px 16px; display: grid; gap: 8px; }}
  .legend span {{ display: inline-flex; align-items: center; gap: 8px; }}
  .swatch {{ width: 12px; height: 12px; border-radius: 999px; display: inline-block; }}
  svg {{ width: 100%; height: auto; min-height: 620px; display: block; background: linear-gradient(135deg, #ffffff, #f8fafc); }}
  .axis {{ font-size: 15px; font-weight: 700; fill: #475569; }}
  .node rect {{ fill: white; stroke: #94a3b8; stroke-width: 1.2; }}
  .node.apex rect {{ fill: #111827; stroke: #111827; }}
  .node.backward rect {{ fill: #fff7ed; stroke: var(--back); }}
  .node.forward rect {{ fill: #ecfeff; stroke: var(--fwd); }}
  .node.has-chiral rect {{ stroke-width: 2.6; stroke: var(--chiral); }}
  .node.has-dominator rect {{ filter: drop-shadow(0 0 5px rgba(22, 163, 74, 0.38)); }}
  .node .label {{ text-anchor: middle; font-size: 10.5px; font-weight: 700; fill: #172033; }}
  .node .key {{ text-anchor: middle; font-size: 9px; fill: #64748b; }}
  .node.apex .label {{ fill: white; }}
  .node.apex .key {{ fill: #cbd5e1; }}
  .badge {{ font-size: 11px; font-weight: 800; fill: #334155; }}
  .note {{ margin-top: 18px; color: var(--muted); }}
</style>
</head>
<body>
<main>
  <h1>Causal Chiral Cone Packet Viewer</h1>
  <div class="subtitle">Schema: <code>{schema}</code>. This is navigation/debug context, not proof.</div>
  <div class="grid">
    <aside class="panel">
      <h2>Packet summary</h2>
      <table>{_render_summary(packet)}</table>
      <h2>Overlay legend</h2>
      <div class="legend">
        <span><i class="swatch" style="background: var(--back)"></i> backward prerequisite component</span>
        <span><i class="swatch" style="background: var(--fwd)"></i> forward user/consequence component</span>
        <span><i class="swatch" style="background: var(--chiral)"></i> χ chiral overlay hit</span>
        <span><i class="swatch" style="background: var(--dom)"></i> D dominator overlay hit</span>
        <span><i class="swatch" style="background: var(--proc)"></i> P process-flow overlay hit</span>
        <span><i class="swatch" style="background: var(--motif)"></i> M motif overlay hit</span>
      </div>
    </aside>
    <section class="panel">
      {_render_svg(packet)}
    </section>
  </div>
  <p class="note">Rule: if a visual edge matters mathematically, descend back to the raw Lean declaration and prove the relation in Lean.</p>
</main>
</body>
</html>
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-in", type=Path, required=True, help="Packet JSON from arango_causal_chiral_cone_prompt.py")
    parser.add_argument("--html-out", type=Path, required=True, help="Offline HTML output path")
    args = parser.parse_args()

    packet = json.loads(args.json_in.read_text(encoding="utf-8"))
    args.html_out.parent.mkdir(parents=True, exist_ok=True)
    args.html_out.write_text(render_html(packet), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
