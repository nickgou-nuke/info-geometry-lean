#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
    from tools.infra.decl_graph_support import load_decl_graph, resolve_graph_profile
    from tools.infra.reports.common import generated_timestamp, normalize_user_path, write_text
    from tools.pathing import repo_root
else:
    from tools.infra.decl_graph_support import load_decl_graph, resolve_graph_profile
    from tools.infra.reports.common import generated_timestamp, normalize_user_path, write_text
    from tools.pathing import repo_root

@dataclass(frozen=True)
class Finding:
    file: str
    line: int
    category: str
    priority: str
    name: str
    note: str
    graph_load_bearing_score: float = 0.0
    reverse_value_users: int = 0

FOCUS_FILES = [
    'lean/InfoGeometry/Krein/HilbertBridge.lean',
    'lean/InfoGeometry/Krein/DoubledAdjoint.lean',
    'lean/InfoGeometry/Krein/Clifford.lean',
    'lean/InfoGeometry/Krein/README.lean',
]
DEFAULT_OUT = 'VACUITY_INDEX.md'
COMMENT_MARKER_RE = re.compile(r'(current alias model|identity under aliasing|compatibility alias|compatibility layer)', re.IGNORECASE)
CARRIER_ALIAS_RE = re.compile(r'^abbrev\s+(?P<name>HilbertDoubled|NeutralSpace)\b.*:=\s*DoubledSpace\b')


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description='Generate the vacuity index markdown report.')
    parser.add_argument('--out', default=DEFAULT_OUT, help='Output markdown path.')
    return parser.parse_args()


def active_priority(load: float) -> str:
    return 'high' if load > 0 else 'medium'


def collect_findings(root: Path) -> list[Finding]:
    _, graph_profiles = load_decl_graph(root)
    findings: list[Finding] = []
    for rel in FOCUS_FILES:
        path = root / rel
        if not path.exists():
            continue
        lines = path.read_text(encoding='utf-8').splitlines()
        for i, line in enumerate(lines, start=1):
            stripped = line.strip()
            carrier_match = CARRIER_ALIAS_RE.match(stripped)
            if carrier_match:
                name = carrier_match.group('name')
                profile = resolve_graph_profile(file_rel=rel, leaf_name_hint=name, line=i, graph_profiles=graph_profiles, max_line_delta=3)
                load = 0.0 if profile is None else profile.graph_load_bearing_score
                users = 0 if profile is None else profile.reverse_value_users
                findings.append(Finding(rel, i, 'carrier_alias', active_priority(load), name, f'carrier alias of `DoubledSpace`; graph_load_bearing_score={load}', load, users))
            elif re.match(r'^noncomputable\s+abbrev\s+doubledToHilbert\b', stripped):
                window = '\n'.join(lines[i - 1 : min(i + 3, len(lines))])
                if 'ContinuousLinearEquiv.refl' in window:
                    profile = resolve_graph_profile(file_rel=rel, leaf_name_hint='doubledToHilbert', line=i, graph_profiles=graph_profiles, max_line_delta=3)
                    load = 0.0 if profile is None else profile.graph_load_bearing_score
                    users = 0 if profile is None else profile.reverse_value_users
                    findings.append(Finding(rel, i, 'identity_transport', active_priority(load), 'doubledToHilbert', f'identity transport under aliasing; graph_load_bearing_score={load}', load, users))
            elif COMMENT_MARKER_RE.search(stripped):
                findings.append(Finding(rel, i, 'explicit_vacuity_marker', 'medium', 'comment', stripped, 0.0, 0))
    return findings


def render_md(findings: list[Finding]) -> str:
    now = generated_timestamp()
    total = len(findings)
    high = sum(1 for f in findings if f.priority == 'high')
    medium = sum(1 for f in findings if f.priority == 'medium')
    low = sum(1 for f in findings if f.priority == 'low')
    queue = sorted(findings, key=lambda f: (0 if f.priority == 'high' else 1, -f.graph_load_bearing_score, f.file, f.line))
    lines = ['# Vacuity Index','',f'Generated: `{now}`','', 'This report tracks alias-driven and identity-transport surfaces, prioritized by whether they are actually graph-active in the exported declaration graph.','', '## Status', f"- vacuity gate: **{'FAIL' if high > 0 else 'PASS'}**", '- interpretation: `FAIL` means at least one alias/identity-transport surface is active in the graph-backed theory path', '', '## Counts', f'- total tracked findings: **{total}**', f'- high-priority active alias/identity findings: **{high}**', f'- medium-priority inactive or documentary findings: **{medium}**', f'- low-priority findings: **{low}**', '', '## Aggressive Replacement Queue']
    if queue:
        for item in queue:
            lines.append(f"- `{item.priority}` `{item.category}` `{item.name}` at `{item.file}:{item.line}` graph_load={item.graph_load_bearing_score} value_users={item.reverse_value_users}")
    else:
        lines.append('- none')
    lines += ['', '## Policy', '- alias/identity surfaces matter most when they are graph-active', '- inactive alias surfaces remain documentary debt, but do not outrank active graph-facing debt', '- truth still lives in Lean; this report only prioritizes replacement pressure']
    return '\n'.join(lines) + '\n'


def main() -> int:
    args = parse_args()
    root = repo_root()
    findings = collect_findings(root)
    out_path = normalize_user_path(args.out, root / DEFAULT_OUT)
    write_text(out_path, render_md(findings))
    print(f'[generate-vacuity-index] wrote {out_path}')
    print(f"[generate-vacuity-index] findings={len(findings)} gate={'FAIL' if any(f.priority == 'high' for f in findings) else 'PASS'}")
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
