#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
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
}

PROP_PATTERNS = {
    'def': re.compile(r"^\s*def\s+([A-Za-z0-9_'.]+).*:\s*Prop\s*:="),
    'abbrev': re.compile(r"^\s*abbrev\s+([A-Za-z0-9_'.]+).*:\s*Prop\s*:="),
    'structure': re.compile(r"^\s*structure\s+([A-Za-z0-9_'.]+).*:\s*Prop(?:\s+where)?"),
}

SCAN_ROOTS = [ROOT / 'lean' / 'InfoGeometry']
SKIP_PARTS = {'Unstable', 'Archive', 'Generated'}


@dataclass(frozen=True, order=True)
class PropSurface:
    kind: str
    file: str
    name: str
    line: int

    @property
    def key(self) -> tuple[str, str, str]:
        return (self.kind, self.file, self.name)

    def as_baseline_entry(self) -> dict[str, str]:
        return {'kind': self.kind, 'file': self.file, 'name': self.name}


def load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding='utf-8'))


def ensure_reports_exist() -> None:
    missing = [str(path) for path in REPORT_PATHS.values() if not path.exists()]
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


def write_baseline(path: Path, surfaces: Iterable[PropSurface]) -> None:
    unique = sorted({surface.key for surface in surfaces})
    payload = {
        'version': 1,
        'notes': [
            'Baseline of existing proposition-valued def/abbrev/structure surfaces.',
            'The canonical policy linter rejects new entries not recorded here.',
            'Removing existing entries is allowed; adding new ones requires an intentional baseline update.',
        ],
        'allowed_prop_surfaces': [
            {'kind': kind, 'file': file, 'name': name}
            for kind, file, name in unique
        ],
    }
    path.write_text(json.dumps(payload, indent=2, sort_keys=False) + '\n', encoding='utf-8')


def compare_prop_baseline(baseline_path: Path, current: list[PropSurface]) -> list[str]:
    if not baseline_path.exists():
        print(f'[canonical-policy] missing proposition baseline: {baseline_path}')
        print('[canonical-policy] create it with --write-baseline after auditing current proposition surfaces.')
        raise SystemExit(1)

    baseline = load_json(baseline_path)
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


def report_failures() -> list[str]:
    failures: list[str] = []

    openclaw = load_json(REPORT_PATHS['openclaw'])
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

    semantic = load_json(REPORT_PATHS['semantic_quotient']).get('summary', {})
    if semantic.get('hotspot_count', 0) != 0:
        failures.append(f"semantic quotient hotspot count regressed to {semantic.get('hotspot_count')}")
    if semantic.get('contractible_packet_count', 0) != 0:
        failures.append(
            f"semantic quotient contractible packet count regressed to {semantic.get('contractible_packet_count')}"
        )

    projection = load_json(REPORT_PATHS['projection_coloring']).get('summary', {})
    if projection.get('monochrome_shell_count', 0) != 0:
        failures.append(
            f"projection-coloring monochrome shell count regressed to {projection.get('monochrome_shell_count')}"
        )
    if projection.get('braided_sink_count', 0) != 0:
        failures.append(
            f"projection-coloring braided sink count regressed to {projection.get('braided_sink_count')}"
        )

    structural = load_json(REPORT_PATHS['structural_hotspots']).get('summary', {})
    if structural.get('active_carrier_count', 0) != 0:
        failures.append(
            f"structural hotspot report reopened with {structural.get('active_carrier_count')} carriers"
        )
    if float(structural.get('top_selector_score', 0.0)) != 0.0:
        failures.append(
            f"structural hotspot top score regressed to {structural.get('top_selector_score')}"
        )

    return failures


def print_summary(prop_surfaces: list[PropSurface]) -> None:
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


def main() -> int:
    parser = argparse.ArgumentParser(description='Enforce canonical anti-furball policy.')
    parser.add_argument(
        '--write-baseline',
        action='store_true',
        help='write the current proposition-surface baseline and exit',
    )
    args = parser.parse_args()

    ensure_reports_exist()
    prop_surfaces = scan_prop_surfaces()

    if args.write_baseline:
        write_baseline(BASELINE_PATH, prop_surfaces)
        print(f'[canonical-policy] wrote baseline {BASELINE_PATH}')
        print(f'[canonical-policy] recorded {len({surface.key for surface in prop_surfaces})} proposition surfaces')
        return 0

    failures = []
    failures.extend(report_failures())
    failures.extend(compare_prop_baseline(BASELINE_PATH, prop_surfaces))

    print_summary(prop_surfaces)

    if failures:
        print('[canonical-policy] failures detected:')
        for failure in failures:
            print(f'  - {failure}')
        return 1

    print('[canonical-policy] policy OK')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
