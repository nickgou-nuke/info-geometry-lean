#!/usr/bin/env python3
"""
⚖️ THE PAULI CANONICAL POLICY LINTER (Authority-Grounded)
Truth lives in Lean; structure lives in the graph.

This script enforces significance and structural policies on the Canonical layer.
It uses the Pauli Authority Bridge to distinguish between 'Trivialities'
and 'Deep Identifications' using formal causal mass.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.decl_graph_support import GraphProfile, load_decl_graph, weak_graph_evidence
else:
    from tools.infra.decl_graph_support import GraphProfile, load_decl_graph, weak_graph_evidence

ROOT = Path(__file__).resolve().parents[2]
BASELINE_PATH = Path(__file__).with_name('canonical_policy_baseline.json')

REPORT_PATHS = {
    'openclaw': ROOT / 'reports/dag/openclaw-targets.json',
    'semantic_quotient': ROOT / 'reports/dag/semantic-quotient.json',
    'projection_coloring': ROOT / 'reports/dag/projection-coloring.json',
    'structural_hotspots': ROOT / 'reports/dag/structural-hotspots.json',
    'theorem_surface_index': ROOT / 'reports/dag/theorem-surface-index.json',
}

INDEX_PATHS = {
    'decls': ROOT / 'artifacts/dag/index/decls.jsonl',
    'edges': ROOT / 'artifacts/dag/index/edges.jsonl',
}

PROP_PATTERNS = {
    'def': re.compile(r"^\s*def\s+([A-Za-z0-9_'.]+).*:\s*Prop\s*:="),
    'abbrev': re.compile(r"^\s*abbrev\s+([A-Za-z0-9_'.]+).*:\s*Prop\s*:="),
    'structure': re.compile(r"^\s*structure\s+([A-Za-z0-9_'.]+).*:\s*Prop(?:\s+where)?"),
}

THEOREM_CLASS_RE = re.compile(r"^\s*--\s*theorem-class:\s*([a-z][a-z-]*)\s*$")
ALLOWED_THEOREM_CLASSES = {
    'derived',
    'closure',
    'transport',
    'invariance',
    'bridge',
    'rigidity',
    'existence',
    'witness-elimination',
}
SUSPECT_THEOREM_CATEGORIES = {'surrogate_or_vacuous', 'package_reprojection', 'hypothesis_bridge'}
ALIASISH_THEOREM_NAME = re.compile(
    r"^(?:is|has|satisfies)[A-Z]|(?:State|Closure|Ready|Equilibrium|Phase|Nontrivial)$"
)
TRIVIAL_SAME_LINE_PATTERNS = [
    re.compile(r":=\s*rfl\b"),
    re.compile(r":=\s*Iff\.rfl\b"),
    re.compile(r":=\s*by\s+rfl\b"),
    re.compile(r":=\s*by\s+(?:simpa!?|simp!?)(?:\b|\s)"),
    re.compile(r":=\s*by\s+exact\b"),
]
TRIVIAL_MULTILINE_STEP = re.compile(
    r"^(?:simp!?|simpa!?|rfl|Iff\.rfl|exact\b.*|unfold\b.*|change\b.*|rw\b.*|dsimp\b.*)$"
)

SCAN_ROOTS = [ROOT / 'lean' / 'InfoGeometry']
SKIP_PARTS = {'Unstable', 'Archive', 'Generated'}
CANONICAL_PREFIX = 'lean/InfoGeometry/Canonical/'
SKIP_CANONICAL_THEOREM_FILES = {
    'lean/InfoGeometry/Canonical/All.lean',
    'lean/InfoGeometry/Canonical/Quantum.lean',
}

def normalize_decl_file(path_val: Any) -> str:
    path_str = str(path_val or "")
    if "/lean/InfoGeometry/" in path_str:
        return "lean/InfoGeometry/" + path_str.split("/lean/InfoGeometry/", 1)[1]
    return path_str

def coerce_line(line_val: Any) -> int:
    try:
        return int(line_val)
    except (ValueError, TypeError):
        return 0

@dataclass(frozen=True, order=True)
class PropSurface:
    kind: str
    file: str
    name: str
    line: int

    @property
    def key(self) -> tuple[str, str, str]:
        return (self.kind, self.file, self.name)


@dataclass(frozen=True, order=True)
class PublicTheorem:
    file: str
    name: str
    short_name: str
    line: int
    category: str
    dependent_theorem_count: int
    theorem_class: str | None
    trivial_proof: bool
    reverse_value_users: int
    reverse_type_users: int
    reverse_theorem_users: int
    graph_load_bearing_score: float
    structural_role: str
    graph_grounded_signal: bool
    heuristic_signal: bool
    hard_verdict_allowed: bool

    @property
    def key(self) -> tuple[str, str]:
        return (self.file, self.name)


@dataclass(frozen=True, order=True)
class SuspectTheorem:
    file: str
    name: str
    line: int
    reasons: list[str]

    @property
    def key(self) -> tuple[str, str]:
        return (self.file, self.name)


# [lossless-compact] load_json folded into igf.common.json_io.load_json
from igf.common.json_io import load_json


def surface_key(surface: PropSurface) -> tuple[str, str, str]:
    return (surface.kind, surface.file, surface.name)


def suspect_key(suspect: SuspectTheorem) -> tuple[str, str]:
    return (suspect.file, suspect.name)


def load_jsonl(path: Path) -> list[dict]:
    rows = []
    if not path.exists():
        return rows
    with path.open(encoding='utf-8') as handle:
        for raw in handle:
            raw = raw.strip()
            if raw:
                rows.append(json.loads(raw))
    return rows


def read_file_lines(path: Path, cache: dict[Path, list[str]]) -> list[str]:
    if path in cache:
        return cache[path]
    if not path.exists():
        return []
    try:
        lines = path.read_text(encoding='utf-8', errors='ignore').splitlines()
        cache[path] = lines
        return lines
    except Exception:
        return []


def has_valid_source_line(lines: list[str], line: int) -> bool:
    if line <= 0 or line > len(lines):
        return False
    return True


def theorem_is_private(lines: list[str], line: int) -> bool:
    if not has_valid_source_line(lines, line):
        return False
    text = lines[line - 1].lstrip()
    return text.startswith('private ') or text.startswith('protected ')


def theorem_class_tag(lines: list[str], line: int) -> str | None:
    for i in range(max(0, line - 10), line):
        m = THEOREM_CLASS_RE.match(lines[i])
        if m:
            return m.group(1)
    return None


def theorem_block(lines: list[str], line: int, next_line: int | None) -> str:
    end = next_line - 1 if next_line is not None else len(lines)
    return '\n'.join(lines[line - 1 : end])


def theorem_has_trivial_proof(block: str) -> bool:
    lines = block.splitlines()
    if not lines:
        return False
    first_line = lines[0]
    for pattern in TRIVIAL_SAME_LINE_PATTERNS:
        if pattern.search(first_line):
            return True
    if 'by' not in block:
        return False
    proof = block.split('by', 1)[1].strip()
    if not proof:
        return False
    steps = [step.strip() for step in proof.split('·') if step.strip()]
    if not steps:
        return False
    return all(TRIVIAL_MULTILINE_STEP.fullmatch(step) for step in steps)


def scan_prop_surfaces() -> list[PropSurface]:
    file_cache: dict[Path, list[str]] = {}
    surfaces = []
    for root_dir in SCAN_ROOTS:
        for path in root_dir.rglob('*.lean'):
            rel_parts = path.relative_to(ROOT).parts
            if any(part in SKIP_PARTS for part in rel_parts):
                continue
            file_rel = path.relative_to(ROOT).as_posix()
            lines = read_file_lines(path, file_cache)
            for i, line in enumerate(lines, start=1):
                for kind, pattern in PROP_PATTERNS.items():
                    m = pattern.search(line)
                    if m:
                        name = m.group(1)
                        surfaces.append(PropSurface(kind=kind, file=file_rel, name=name, line=i))
    return sorted(surfaces)


def scan_public_theorems() -> list[PublicTheorem]:
    theorem_index = load_json(REPORT_PATHS['theorem_surface_index'])
    rows = theorem_index.get('rows', [])
    decl_rows = load_jsonl(INDEX_PATHS['decls'])
    edge_rows = load_jsonl(INDEX_PATHS['edges'])
    _decl_key_to_full, graph_profiles = load_decl_graph(ROOT)

    theorem_kinds = {'theorem', 'lemma'}
    decl_kind_by_name = {row['name']: row.get('kind') for row in decl_rows if 'name' in row}
    file_decl_lines: dict[str, list[int]] = defaultdict(list)
    for row in decl_rows:
        file = normalize_decl_file(row.get('file'))
        line = coerce_line(row.get('line'))
        if file and line:
            file_decl_lines[file].append(line)
    for rel in file_decl_lines:
        file_decl_lines[rel].sort()

    theorem_dependents: dict[str, set[str]] = defaultdict(set)
    theorem_names = {name for name, kind in decl_kind_by_name.items() if kind in theorem_kinds}
    for edge in edge_rows:
        src = edge.get('src')
        dst = edge.get('dst')
        if src in theorem_names and dst in theorem_names and src != dst:
            theorem_dependents[dst].add(src)

    file_cache: dict[Path, list[str]] = {}
    public_theorems: list[PublicTheorem] = []
    for row in rows:
        if row.get('kind') not in theorem_kinds:
            continue
        file = normalize_decl_file(row.get('file'))
        if not file.startswith(CANONICAL_PREFIX):
            continue
        if file in SKIP_CANONICAL_THEOREM_FILES:
            continue
        name = row.get('name')
        short_name = row.get('short_name')
        line = coerce_line(row.get('line'))
        category = row.get('category')
        if not isinstance(name, str) or not isinstance(short_name, str) or line <= 0 or not isinstance(category, str):
            continue
        path = ROOT / file
        lines = read_file_lines(path, file_cache)
        if not has_valid_source_line(lines, line):
            continue
        if theorem_is_private(lines, line):
            continue

        next_line = None
        for candidate in file_decl_lines.get(file, []):
            if candidate > line:
                next_line = candidate
                break
        block = theorem_block(lines, line, next_line)
        profile = graph_profiles.get(name)
        
        # ⚖️ PAULI REFACTOR: Authority-grounded triviality audit
        is_trivial = theorem_has_trivial_proof(block)
        if is_trivial and profile is not None:
            # If the theorem has massive causal mass or depth, it is a Deep Identification, not a triviality.
            if profile.depth > 5 or profile.descendant_mass > 10:
                is_trivial = False
                
        graph_grounded_signal = profile is not None
        hard_verdict_allowed = profile is not None and not weak_graph_evidence(profile)
        heuristic_signal = bool(
            is_trivial
            or category in SUSPECT_THEOREM_CATEGORIES
            or ALIASISH_THEOREM_NAME.search(short_name)
        )

        public_theorems.append(
            PublicTheorem(
                file=file,
                name=name,
                short_name=short_name,
                line=line,
                category=category,
                dependent_theorem_count=len(theorem_dependents.get(name, set())),
                theorem_class=theorem_class_tag(lines, line),
                trivial_proof=is_trivial,
                reverse_value_users=0 if profile is None else profile.reverse_value_users,
                reverse_type_users=0 if profile is None else profile.reverse_type_users,
                reverse_theorem_users=0 if profile is None else profile.reverse_theorem_users,
                graph_load_bearing_score=0.0 if profile is None else profile.graph_load_bearing_score,
                structural_role='graph_unknown' if profile is None else profile.structural_role,
                graph_grounded_signal=graph_grounded_signal,
                heuristic_signal=heuristic_signal,
                hard_verdict_allowed=hard_verdict_allowed,
            )
        )
    return sorted(public_theorems)


def scan_suspect_theorems(public_theorems: list[PublicTheorem]) -> list[SuspectTheorem]:
    suspects: list[SuspectTheorem] = []
    for theorem in public_theorems:
        reasons: list[str] = []
        weak_graph = theorem_has_weak_graph_support(theorem)
        if theorem.category in SUSPECT_THEOREM_CATEGORIES and theorem.dependent_theorem_count == 0 and weak_graph:
            reasons.append(f'theorem-surface category {theorem.category} with no downstream theorem dependents and weak graph support ({theorem.structural_role})')
        if theorem.trivial_proof and theorem.dependent_theorem_count == 0 and weak_graph:
            reasons.append(f'proof is definitional/trivial with no downstream theorem dependents and weak graph support ({theorem.structural_role})')
        if theorem.dependent_theorem_count == 0 and weak_graph and (
            theorem.category in SUSPECT_THEOREM_CATEGORIES or ALIASISH_THEOREM_NAME.search(theorem.short_name)
        ):
            reasons.append('no downstream theorem dependents')

        if reasons:
            suspects.append(SuspectTheorem(file=theorem.file, name=theorem.name, line=theorem.line, reasons=reasons))
    return sorted(suspects)


def theorem_has_weak_graph_support(theorem: PublicTheorem) -> bool:
    if theorem.structural_role == 'graph_unknown':
        return theorem.dependent_theorem_count == 0
    return weak_graph_evidence(
        GraphProfile(
            name=theorem.name,
            kind='theorem',
            module='',
            file=theorem.file,
            line=theorem.line,
            rep_layer=None,
            rep_depth=None,
            reverse_value_users=theorem.reverse_value_users,
            reverse_type_users=theorem.reverse_type_users,
            reverse_theorem_users=theorem.reverse_theorem_users,
            reverse_public_fan_in=0,
            descendant_mass=0,
            transitive_reverse_reach=0,
            depth=0,
            scc_size=1,
            is_sink=False,
            significance_present=False,
            forward_value_theorems=tuple(),
            forward_value_defs=tuple(),
            graph_load_bearing_score=theorem.graph_load_bearing_score,
            structural_role=theorem.structural_role,
        )
    )


def main() -> int:
    parser = argparse.ArgumentParser(description='Canonical policy linter')
    parser.add_argument('--json-out', type=Path, help='Output report as JSON')
    parser.add_argument(
        '--fail-on',
        choices=('new', 'none'),
        default='new',
        help='Fail on unbaselined heuristic surfaces, or emit a review report only.',
    )
    args = parser.parse_args()

    baseline = load_json(BASELINE_PATH)
    prop_surfaces = scan_prop_surfaces()
    public_theorems = scan_public_theorems()
    suspect_theorems = scan_suspect_theorems(public_theorems)

    allowed_prop_surfaces = {
        (str(row.get('kind', '')), str(row.get('file', '')), str(row.get('name', '')))
        for row in baseline.get('allowed_prop_surfaces', [])
        if isinstance(row, dict)
    }
    allowed_suspect_theorems = {
        (str(row.get('file', '')), str(row.get('name', '')))
        for row in baseline.get('allowed_suspect_theorems', [])
        if isinstance(row, dict)
    }

    new_prop_surfaces = [p for p in prop_surfaces if surface_key(p) not in allowed_prop_surfaces]
    new_suspect_theorems = [s for s in suspect_theorems if suspect_key(s) not in allowed_suspect_theorems]

    report = {
        'schema': 'info_geometry.canonical_policy_lint.v1',
        'active_carriers': 0, # Legacy
        'proposition_surfaces': [
            {'kind': p.kind, 'file': p.file, 'name': p.name, 'line': p.line}
            for p in prop_surfaces
        ],
        'public_theorems': [
            {
                'file': t.file,
                'name': t.name,
                'short_name': t.short_name,
                'line': t.line,
                'category': t.category,
                'dependent_theorem_count': t.dependent_theorem_count,
                'theorem_class': t.theorem_class,
                'trivial_proof': t.trivial_proof,
                'structural_role': t.structural_role,
            }
            for t in public_theorems
        ],
        'suspect_theorems': [
            {'file': s.file, 'name': s.name, 'line': s.line, 'reasons': s.reasons}
            for s in suspect_theorems
        ],
        'new_prop_surfaces': [
            {'kind': p.kind, 'file': p.file, 'name': p.name, 'line': p.line}
            for p in new_prop_surfaces
        ],
        'new_suspect_theorems': [
            {'file': s.file, 'name': s.name, 'line': s.line, 'reasons': s.reasons}
            for s in new_suspect_theorems
        ],
        'gate_mode': args.fail_on,
    }

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')

    print(f"[canonical-policy] scanned {len(public_theorems)} public canonical theorems")
    print(f"[canonical-policy] identified {len(suspect_theorems)} suspect theorem surfaces")
    print(f"[canonical-policy] new suspect theorem surfaces {len(new_suspect_theorems)}")
    print(f"[canonical-policy] new proposition surfaces {len(new_prop_surfaces)}")

    if args.fail_on == 'new' and (new_suspect_theorems or new_prop_surfaces):
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
