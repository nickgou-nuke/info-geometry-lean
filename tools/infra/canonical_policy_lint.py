#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

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
LEAN_REPORT_PATH_RE = re.compile(r"^lean/InfoGeometry/.+\.lean$")


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

    @property
    def key(self) -> tuple[str, str]:
        return (self.file, self.name)

    def as_baseline_entry(self) -> dict[str, str]:
        return {'file': self.file, 'name': self.name}


@dataclass(frozen=True, order=True)
class SuspectTheorem:
    file: str
    name: str
    line: int
    category: str
    dependent_theorem_count: int
    reasons: tuple[str, ...]

    @property
    def key(self) -> tuple[str, str]:
        return (self.file, self.name)

    def as_baseline_entry(self) -> dict[str, object]:
        return {
            'file': self.file,
            'name': self.name,
            'category': self.category,
            'dependent_theorem_count': self.dependent_theorem_count,
            'reasons': list(self.reasons),
        }


def load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding='utf-8'))


def load_jsonl(path: Path) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    with path.open(encoding='utf-8') as handle:
        for raw in handle:
            raw = raw.strip()
            if raw:
                rows.append(json.loads(raw))
    return rows


def iter_embedded_lean_paths(value: object) -> Iterable[str]:
    if isinstance(value, str):
        if LEAN_REPORT_PATH_RE.match(value):
            yield value
        return
    if isinstance(value, dict):
        for nested in value.values():
            yield from iter_embedded_lean_paths(nested)
        return
    if isinstance(value, list):
        for nested in value:
            yield from iter_embedded_lean_paths(nested)


def stale_report_paths(payload: object) -> list[str]:
    missing = {
        rel
        for rel in iter_embedded_lean_paths(payload)
        if not (ROOT / rel).exists()
    }
    return sorted(missing)


def stale_report_failures(report_payloads: dict[str, object]) -> list[str]:
    failures: list[str] = []
    for report_name, payload in report_payloads.items():
        missing = stale_report_paths(payload)
        if not missing:
            continue
        sample = ', '.join(missing[:5])
        suffix = '' if len(missing) <= 5 else f" (+{len(missing) - 5} more)"
        failures.append(
            f"stale {report_name} report references missing Lean file(s): {sample}{suffix}"
        )
    return failures


def ensure_reports_exist() -> None:
    missing = [str(path) for path in REPORT_PATHS.values() if not path.exists()]
    missing += [str(path) for path in INDEX_PATHS.values() if not path.exists()]
    if missing:
        print('[canonical-policy] missing refreshed report artifacts:')
        for path in missing:
            print(f'  - {path}')
        print('[canonical-policy] run the maintained DAG refresh pipeline first.')
        raise SystemExit(1)


def scan_prop_surfaces() -> list[PropSurface]:
    surfaces: list[PropSurface] = []
    for root in SCAN_ROOTS:
        for path in sorted(root.rglob('*.lean')):
            if any(part in SKIP_PARTS for part in path.parts):
                continue
            rel = path.relative_to(ROOT).as_posix()
            for lineno, line in enumerate(path.read_text(encoding='utf-8').splitlines(), 1):
                for kind, pattern in PROP_PATTERNS.items():
                    match = pattern.match(line)
                    if match:
                        surfaces.append(PropSurface(kind=kind, file=rel, name=match.group(1), line=lineno))
    return surfaces


def read_file_lines(path: Path, cache: dict[Path, list[str]]) -> list[str]:
    if path not in cache:
        cache[path] = path.read_text(encoding='utf-8').splitlines()
    return cache[path]


def theorem_block(lines: list[str], start_line: int, next_decl_line: int | None) -> str:
    start = max(start_line - 1, 0)
    end = len(lines) if next_decl_line is None else max(next_decl_line - 1, start)
    return '\n'.join(lines[start:end])


def has_valid_source_line(lines: list[str], line: int) -> bool:
    return line > 0 and line <= len(lines)


def theorem_is_private(lines: list[str], line: int) -> bool:
    if not has_valid_source_line(lines, line):
        return False
    text = lines[line - 1].lstrip()
    return text.startswith('private theorem') or text.startswith('private lemma')


def theorem_class_tag(lines: list[str], line: int) -> str | None:
    if not has_valid_source_line(lines, line):
        return None
    # Scan backward from the line before the theorem, up to 5 lines up
    for idx in range(line - 2, max(-1, line - 7), -1):
        if idx < 0 or idx >= len(lines):
            continue
        text = lines[idx].strip()
        if not text:
            continue
        match = THEOREM_CLASS_RE.match(text)
        if match:
            return match.group(1)
        if text.startswith('--') or text.startswith('/-') or text.startswith('-/'):
            continue
        break
    return None


def theorem_has_trivial_proof(block: str) -> bool:
    normalized = ' '.join(
        line.strip()
        for line in block.splitlines()
        if line.strip() and not line.lstrip().startswith('--')
    )
    for pattern in TRIVIAL_SAME_LINE_PATTERNS:
        if pattern.search(normalized):
            return True
    if ':= by' not in normalized:
        return False
    proof = normalized.split(':= by', 1)[1].strip()
    if not proof:
        return False
    steps = [step.strip() for step in proof.split('·') if step.strip()]
    if not steps:
        return False
    return all(TRIVIAL_MULTILINE_STEP.fullmatch(step) for step in steps)


def compare_prop_baseline(baseline: dict[str, object], current: list[PropSurface]) -> list[str]:
    allowed = {
        (entry['kind'], entry['file'], entry['name'])
        for entry in baseline.get('allowed_prop_surfaces', [])
    }
    current_by_key = {surface.key: surface for surface in current}
    unexpected = sorted(current_by_key.keys() - allowed)
    return [
        f"new proposition surface: {kind} {name} at {file}:{current_by_key[(kind, file, name)].line}"
        for kind, file, name in unexpected
    ]


def scan_public_theorems() -> list[PublicTheorem]:
    theorem_index = load_json(REPORT_PATHS['theorem_surface_index'])
    rows = theorem_index.get('rows', [])
    decl_rows = load_jsonl(INDEX_PATHS['decls'])
    edge_rows = load_jsonl(INDEX_PATHS['edges'])

    theorem_kinds = {'theorem', 'lemma'}
    decl_kind_by_name = {row['name']: row.get('kind') for row in decl_rows if 'name' in row}
    file_decl_lines: dict[str, list[int]] = defaultdict(list)
    for row in decl_rows:
        file = row.get('file')
        line = row.get('line')
        if isinstance(file, str) and isinstance(line, int):
            rel = Path(file).relative_to(ROOT).as_posix() if file.startswith(str(ROOT)) else file
            file_decl_lines[rel].append(line)
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
        file = row.get('file')
        if not isinstance(file, str) or not file.startswith(CANONICAL_PREFIX):
            continue
        if file in SKIP_CANONICAL_THEOREM_FILES:
            continue
        name = row.get('name')
        short_name = row.get('short_name')
        line = row.get('line')
        category = row.get('category')
        if not isinstance(name, str) or not isinstance(short_name, str) or not isinstance(line, int) or not isinstance(category, str):
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
        public_theorems.append(
            PublicTheorem(
                file=file,
                name=name,
                short_name=short_name,
                line=line,
                category=category,
                dependent_theorem_count=len(theorem_dependents.get(name, set())),
                theorem_class=theorem_class_tag(lines, line),
                trivial_proof=theorem_has_trivial_proof(block),
            )
        )
    return sorted(public_theorems)


def scan_suspect_theorems(public_theorems: list[PublicTheorem]) -> list[SuspectTheorem]:
    suspects: list[SuspectTheorem] = []
    for theorem in public_theorems:
        reasons: list[str] = []
        if theorem.category in SUSPECT_THEOREM_CATEGORIES:
            reasons.append(f'theorem-surface category {theorem.category}')
        if theorem.trivial_proof:
            reasons.append('proof is definitional/trivial')
        if theorem.dependent_theorem_count == 0 and (
            theorem.category in SUSPECT_THEOREM_CATEGORIES or ALIASISH_THEOREM_NAME.search(theorem.short_name)
        ):
            reasons.append('no downstream theorem dependents')
        if reasons:
            suspects.append(
                SuspectTheorem(
                    file=theorem.file,
                    name=theorem.name,
                    line=theorem.line,
                    category=theorem.category,
                    dependent_theorem_count=theorem.dependent_theorem_count,
                    reasons=tuple(sorted(set(reasons))),
                )
            )
    return sorted(suspects)


def compare_new_public_theorems(baseline: dict[str, object], current: list[PublicTheorem]) -> list[str]:
    known = {
        (entry['file'], entry['name'])
        for entry in baseline.get('known_public_theorems', [])
    }
    failures: list[str] = []
    for theorem in current:
        if theorem.key in known:
            continue
        if theorem.theorem_class is None:
            failures.append(
                f"new public theorem missing theorem-class tag: {theorem.name} at {theorem.file}:{theorem.line}"
            )
        elif theorem.theorem_class not in ALLOWED_THEOREM_CLASSES:
            failures.append(
                f"new public theorem has invalid theorem-class tag '{theorem.theorem_class}': {theorem.name} at {theorem.file}:{theorem.line}"
            )
        if theorem.dependent_theorem_count == 0:
            failures.append(
                f"new public theorem has no downstream theorem dependents: {theorem.name} at {theorem.file}:{theorem.line}"
            )
        if theorem.trivial_proof:
            failures.append(
                f"new public theorem has definitional/trivial proof: {theorem.name} at {theorem.file}:{theorem.line}"
            )
        if theorem.category in SUSPECT_THEOREM_CATEGORIES:
            failures.append(
                f"new public theorem lands in suspect theorem-surface category {theorem.category}: {theorem.name} at {theorem.file}:{theorem.line}"
            )
    return failures


def compare_suspect_theorem_baseline(baseline: dict[str, object], current: list[SuspectTheorem]) -> list[str]:
    allowed = {
        (entry['file'], entry['name'])
        for entry in baseline.get('allowed_suspect_theorems', [])
    }
    current_by_key = {surface.key: surface for surface in current}
    unexpected = sorted(current_by_key.keys() - allowed)
    return [
        (
            f"new suspect theorem surface: {current_by_key[(file, name)].name} at "
            f"{file}:{current_by_key[(file, name)].line} "
            f"[{'; '.join(current_by_key[(file, name)].reasons)}]"
        )
        for file, name in unexpected
    ]


def write_baseline(
    path: Path,
    prop_surfaces: Iterable[PropSurface],
    public_theorems: Iterable[PublicTheorem],
    suspect_theorems: Iterable[SuspectTheorem],
) -> None:
    unique_props = sorted({surface.key for surface in prop_surfaces})
    unique_public_theorems = sorted({surface.key for surface in public_theorems})
    unique_suspect_theorems = sorted({surface.key for surface in suspect_theorems})
    suspect_lookup = {surface.key: surface for surface in suspect_theorems}
    payload = {
        'version': 3,
        'notes': [
            'Baseline of current proposition-valued surfaces and theorem-surface debt.',
            'The canonical policy linter rejects new proposition aliases, new suspect public theorem surfaces, and new unclassified public theorem surface.',
            'Removing existing entries is allowed; adding new ones requires an intentional baseline update and audit.',
        ],
        'allowed_report_failures': collect_report_failures(),
        'allowed_prop_surfaces': [
            {'kind': kind, 'file': file, 'name': name}
            for kind, file, name in unique_props
        ],
        'known_public_theorems': [
            {'file': file, 'name': name}
            for file, name in unique_public_theorems
        ],
        'allowed_suspect_theorems': [
            suspect_lookup[key].as_baseline_entry()
            for key in unique_suspect_theorems
        ],
    }
    path.write_text(json.dumps(payload, indent=2, sort_keys=False) + '\n', encoding='utf-8')


def collect_report_failures() -> list[str]:
    failures: list[str] = []

    openclaw = load_json(REPORT_PATHS['openclaw'])
    semantic_payload = load_json(REPORT_PATHS['semantic_quotient'])
    projection_payload = load_json(REPORT_PATHS['projection_coloring'])
    structural_payload = load_json(REPORT_PATHS['structural_hotspots'])
    failures.extend(
        stale_report_failures(
            {
                'openclaw': openclaw,
                'semantic_quotient': semantic_payload,
                'projection_coloring': projection_payload,
                'structural_hotspots': structural_payload,
            }
        )
    )

    structural_summary = openclaw.get('source', {}).get('structural_hotspots_summary', {})
    coverage = openclaw.get('coverage', {})
    audit_counts = openclaw.get('source', {}).get('true_root_order_summary', {}).get('audit_counts', {})

    if structural_summary.get('active_carrier_count', 0) != 0:
        failures.append(
            f"structural active carriers regressed to {structural_summary.get('active_carrier_count')}"
        )
    if float(structural_summary.get('top_selector_score', 0.0)) != 0.0:
        failures.append(
            f"top selector score regressed to {structural_summary.get('top_selector_score')}"
        )
    if openclaw.get('primary_target') is not None:
        failures.append(f"openclaw primary target reopened: {openclaw.get('primary_target')}")
    if openclaw.get('structural_hotspot_targets'):
        failures.append('structural hotspot targets are non-empty again')
    if openclaw.get('uncovered_debt_targets'):
        failures.append('uncovered debt targets are non-empty again')
    if coverage.get('missing_decl_files_count', 0) != 0:
        failures.append(
            f"missing declaration-bearing files: {coverage.get('missing_decl_files_count')}"
        )
    if coverage.get('uncovered_debt_file_count', 0) != 0:
        failures.append(
            f"uncovered debt files: {coverage.get('uncovered_debt_file_count')}"
        )
    for audit_name in ('thinness', 'vacuity', 'surrogate'):
        if audit_counts.get(audit_name, 0) != 0:
            failures.append(f"{audit_name} audit count regressed to {audit_counts.get(audit_name)}")

    semantic = semantic_payload.get('summary', {})
    if semantic.get('hotspot_count', 0) != 0:
        failures.append(f"semantic quotient hotspot count regressed to {semantic.get('hotspot_count')}")
    if semantic.get('contractible_packet_count', 0) != 0:
        failures.append(
            f"semantic quotient contractible packet count regressed to {semantic.get('contractible_packet_count')}"
        )

    projection = projection_payload.get('summary', {})
    if projection.get('monochrome_shell_count', 0) != 0:
        failures.append(
            f"projection-coloring monochrome shell count regressed to {projection.get('monochrome_shell_count')}"
        )
    if projection.get('braided_sink_count', 0) != 0:
        failures.append(
            f"projection-coloring braided sink count regressed to {projection.get('braided_sink_count')}"
        )

    structural = structural_payload.get('summary', {})
    if structural.get('active_carrier_count', 0) != 0:
        failures.append(
            f"structural hotspot report reopened with {structural.get('active_carrier_count')} carriers"
        )
    if float(structural.get('top_selector_score', 0.0)) != 0.0:
        failures.append(
            f"structural hotspot top score regressed to {structural.get('top_selector_score')}"
        )

    return sorted(failures)


def report_failures(baseline: dict[str, object]) -> list[str]:
    current_failures = collect_report_failures()
    allowed_failures = {
        str(item)
        for item in baseline.get('allowed_report_failures', [])
        if isinstance(item, str)
    }
    if not allowed_failures:
        return current_failures
    return [failure for failure in current_failures if failure not in allowed_failures]


def print_summary(prop_surfaces: list[PropSurface], public_theorems: list[PublicTheorem], suspect_theorems: list[SuspectTheorem]) -> None:
    openclaw = load_json(REPORT_PATHS['openclaw'])
    semantic = load_json(REPORT_PATHS['semantic_quotient'])
    projection = load_json(REPORT_PATHS['projection_coloring'])
    print('[canonical-policy] graph summary')
    structural_summary = openclaw['source']['structural_hotspots_summary']
    print(f"  active carriers: {structural_summary['active_carrier_count']}")
    print(f"  semantic hotspots: {semantic['summary']['hotspot_count']}")
    print(f"  contractible packets: {semantic['summary']['contractible_packet_count']}")
    print(f"  monochrome shells: {projection['summary']['monochrome_shell_count']}")
    print(f"  braided sinks: {projection['summary']['braided_sink_count']}")
    print(f"  proposition surfaces scanned: {len(prop_surfaces)}")
    print(f"  public canonical theorems scanned: {len(public_theorems)}")
    print(f"  suspect theorem surfaces scanned: {len(suspect_theorems)}")


def main() -> int:
    parser = argparse.ArgumentParser(description='Enforce canonical anti-furball and anti-fake-theorem policy.')
    parser.add_argument(
        '--write-baseline',
        action='store_true',
        help='write the current proposition/theorem debt baseline and exit',
    )
    args = parser.parse_args()

    ensure_reports_exist()
    baseline = load_json(BASELINE_PATH) if BASELINE_PATH.exists() else None
    if baseline is None and not args.write_baseline:
        print(f'[canonical-policy] missing baseline: {BASELINE_PATH}')
        print('[canonical-policy] create it with --write-baseline after auditing current policy debt.')
        raise SystemExit(1)

    prop_surfaces = scan_prop_surfaces()
    public_theorems = scan_public_theorems()
    suspect_theorems = scan_suspect_theorems(public_theorems)

    if args.write_baseline:
        write_baseline(BASELINE_PATH, prop_surfaces, public_theorems, suspect_theorems)
        print(f'[canonical-policy] wrote baseline {BASELINE_PATH}')
        print(f'[canonical-policy] recorded {len({surface.key for surface in prop_surfaces})} proposition surfaces')
        print(f'[canonical-policy] recorded {len({surface.key for surface in public_theorems})} public canonical theorems')
        print(f'[canonical-policy] recorded {len({surface.key for surface in suspect_theorems})} suspect theorem surfaces')
        return 0

    failures = []
    failures.extend(report_failures(baseline))
    failures.extend(compare_prop_baseline(baseline, prop_surfaces))
    failures.extend(compare_new_public_theorems(baseline, public_theorems))
    failures.extend(compare_suspect_theorem_baseline(baseline, suspect_theorems))

    print_summary(prop_surfaces, public_theorems, suspect_theorems)

    if failures:
        print('[canonical-policy] failures detected:')
        for failure in failures:
            print(f'  - {failure}')
        return 1

    print('[canonical-policy] policy OK')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
