#!/usr/bin/env python3
from __future__ import annotations

import datetime as dt
import re
import sys
from dataclasses import dataclass
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
    from tools.infra.decl_graph_support import load_decl_graph, resolve_graph_profile, weak_graph_evidence
    from tools.infra.reports.common import relpath
    from tools.pathing import repo_root
else:
    from tools.infra.decl_graph_support import load_decl_graph, resolve_graph_profile, weak_graph_evidence
    from tools.infra.reports.common import relpath
    from tools.pathing import repo_root

DECL_START_RE = re.compile(r"^\s*(?:@\[[^\]]+\]\s*)*(?:noncomputable\s+)?(theorem|lemma)\s+([A-Za-z0-9_'.]+)")
DECL_BOUNDARY_RE = re.compile(r"^\s*(?:@\[[^\]]+\]\s*)*(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|structure|class|instance|axiom)\s+[A-Za-z0-9_'.]+")
TARGET_NAME_RE = re.compile(r"(bridge|launchpad|package|equivalence|correspondence)", re.IGNORECASE)
TARGET_FILE_RE = re.compile(r"(Bridge|Launchpad|Interface)\.lean$")
HELPER_NAME_RE = re.compile(r"^(?:fst|snd)_(?:coe|val)$|.*(?:_apply|_zero|_eq_1|_proof_[0-9_]+)$")
ARG_NAME_RE = re.compile(r"\(([A-Za-z_][A-Za-z0-9_']*)\s*:")
ONE_LINE_RFL_RE = re.compile(r"^\s*rfl\s*$")
BY_RFL_RE = re.compile(r"^\s*by\s+rfl\s*$", re.DOTALL)
EXACT_FORWARD_RE = re.compile(r"^\s*by\s+exact\s+([A-Za-z0-9_'.]+)", re.DOTALL)
SIMPA_USING_RE = re.compile(r"^\s*by\s+simpa(?:\s*\[[^\]]*\])?\s+using\s+([A-Za-z0-9_'.]+)", re.DOTALL)
PACKAGE_SHAPE_RE = re.compile(r"\brcases\b.*\bexact\s+⟨", re.DOTALL)

@dataclass(frozen=True)
class Finding:
    file: str
    line: int
    name: str
    category: str
    priority: str
    note: str
    structural_role: str = 'graph_unknown'
    theorem_users: int = 0


def priority_for(category: str) -> str:
    return {'definitional_identity':'high','direct_forwarder':'medium','underscore_hypothesis':'medium','package_orchestration':'low'}.get(category,'low')


def is_target(rel: str, name: str) -> bool:
    return not HELPER_NAME_RE.match(name) and bool(TARGET_NAME_RE.search(name) or TARGET_FILE_RE.search(Path(rel).name))


def trim_proof(proof: str) -> str:
    kept = [line for line in proof.splitlines() if not line.strip().startswith('/--') and not line.strip().startswith('--')]
    return '\n'.join(kept).strip()


def classify_block(rel: str, start_line: int, name: str, block_lines: list[str], graph_profiles) -> list[Finding]:
    findings: list[Finding] = []
    profile = resolve_graph_profile(file_rel=rel, leaf_name_hint=name, line=start_line, graph_profiles=graph_profiles)
    weak_graph = weak_graph_evidence(profile)
    joined = '\n'.join(block_lines)
    head = joined.split(':=', 1)[0]
    proof = trim_proof(joined.split(':=', 1)[1]) if ':=' in joined else ''

    if not weak_graph:
        return findings

    role = 'graph_unknown' if profile is None else profile.structural_role
    thm_users = 0 if profile is None else profile.reverse_theorem_users

    underscore_args = [arg for arg in ARG_NAME_RE.findall(head) if arg.startswith('_')]
    if underscore_args:
        findings.append(Finding(rel, start_line, name, 'underscore_hypothesis', priority_for('underscore_hypothesis'), 'declaration head contains underscore-prefixed hypotheses: ' + ', '.join(f'`{arg}`' for arg in underscore_args), role, thm_users))

    if proof:
        compact = '\n'.join(line.rstrip() for line in proof.splitlines()).strip()
        if ONE_LINE_RFL_RE.fullmatch(compact) or BY_RFL_RE.fullmatch(compact):
            findings.append(Finding(rel, start_line, name, 'definitional_identity', priority_for('definitional_identity'), f'proof body reduces directly to `rfl` on weak graph role `{role}`', role, thm_users))
        else:
            exact_match = EXACT_FORWARD_RE.match(compact)
            simpa_match = SIMPA_USING_RE.match(compact)
            if exact_match:
                findings.append(Finding(rel, start_line, name, 'direct_forwarder', priority_for('direct_forwarder'), f'proof body forwards directly via `exact {exact_match.group(1)}` on weak graph role `{role}`', role, thm_users))
            elif simpa_match:
                findings.append(Finding(rel, start_line, name, 'direct_forwarder', priority_for('direct_forwarder'), f'proof body is a `simpa ... using {simpa_match.group(1)}` forwarder on weak graph role `{role}`', role, thm_users))
            elif PACKAGE_SHAPE_RE.search(compact):
                findings.append(Finding(rel, start_line, name, 'package_orchestration', priority_for('package_orchestration'), f'proof body is primarily package/orchestration on weak graph role `{role}`', role, thm_users))
    return findings


def collect_findings(root: Path) -> list[Finding]:
    _, graph_profiles = load_decl_graph(root)
    findings: list[Finding] = []
    src = root / 'lean' / 'InfoGeometry'
    for path in sorted(src.rglob('*.lean')):
        rel = relpath(path, root)
        lines = path.read_text(encoding='utf-8').splitlines()
        i = 0
        while i < len(lines):
            match = DECL_START_RE.match(lines[i])
            if not match:
                i += 1
                continue
            kind, name = match.group(1), match.group(2)
            if kind not in {'theorem', 'lemma'} or not is_target(rel, name):
                i += 1
                continue
            start = i
            j = i + 1
            while j < len(lines) and not DECL_BOUNDARY_RE.match(lines[j]):
                j += 1
            findings.extend(classify_block(rel, start + 1, name, lines[start:j], graph_profiles))
            i = j
    return findings


def render_md(findings: list[Finding]) -> str:
    now = dt.datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    by_category: dict[str, int] = {}
    by_priority: dict[str, int] = {}
    for item in findings:
        by_category[item.category] = by_category.get(item.category, 0) + 1
        by_priority[item.priority] = by_priority.get(item.priority, 0) + 1
    order = {'high':0,'medium':1,'low':2}
    queue = sorted(findings, key=lambda f: (order.get(f.priority, 9), f.file, f.line, f.name))
    lines = ['# Bridge Thinness Index','',f'Generated: `{now}`','', 'This report flags bridge-facing theorem surfaces only when syntax-thin proofs also sit on weak DAG graph roles.','', '## Status', f"- thin-bridge gate: **{'FAIL' if by_priority.get('high', 0) else 'PASS'}**", '- interpretation: `FAIL` means at least one targeted theorem looks definitional and is graph-thin/isolated', '', '## Counts', f"- total tracked findings: **{len(findings)}**", f"- definitional identity findings: **{by_category.get('definitional_identity', 0)}**", f"- direct forwarder findings: **{by_category.get('direct_forwarder', 0)}**", f"- underscore-hypothesis findings: **{by_category.get('underscore_hypothesis', 0)}**", f"- package/orchestration findings: **{by_category.get('package_orchestration', 0)}**", '', '## Queue']
    if queue:
        for item in queue:
            lines.append(f"- `{item.priority}` `{item.category}` `{item.name}` at `{item.file}:{item.line}` role=`{item.structural_role}` theorem_users={item.theorem_users}")
    else:
        lines.append('- none')
    lines += ['', '## Policy', '- this is a graph-gated syntax audit, not a proof oracle', '- short proofs only enter the queue when the declaration is also graph-thin', '- load-bearing bridges are not demoted merely for having concise proofs']
    return '\n'.join(lines) + '\n'


def main() -> int:
    root = repo_root()
    findings = collect_findings(root)
    out_path = root / 'BRIDGE_THINNESS_INDEX.md'
    out_path.write_text(render_md(findings), encoding='utf-8')
    high = sum(1 for item in findings if item.priority == 'high')
    print(f'[generate-bridge-thinness-index] wrote {out_path}')
    print(f"[generate-bridge-thinness-index] findings={len(findings)} gate={'FAIL' if high else 'PASS'}")
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
