#!/usr/bin/env python3
from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    import sys
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import repo_root
else:
    from tools.pathing import repo_root


EXCLUDE_NONCANONICAL = {
    'lean/InfoGeometry/Bar.lean',
    'lean/InfoGeometry/Foo.lean',
    'lean/InfoGeometry/GraphExport.lean',
    'lean/InfoGeometry/Krein/TestTimeout.lean',
    'lean/InfoGeometry/Unstable/IBSurrogates.lean',
    'lean/InfoGeometry/Unstable/SingularUnitaryBridge.lean',
    'lean/InfoGeometry/Unstable/YangMillsBridge.lean',
}

NAMESPACE_OR_ATTRIBUTION_FIX = {
    'lean/InfoGeometry/Canonical/RobustThermodynamicRegression.lean',
    'lean/InfoGeometry/Core/ProjectiveSimplex.lean',
    'lean/InfoGeometry/Krein/Category.lean',
    'lean/InfoGeometry/Krein/KreinSpace.lean',
    'lean/InfoGeometry/Krein/State.lean',
    'lean/InfoGeometry/Krein/Superalgebra.lean',
    'lean/InfoGeometry/Projective/Normalize.lean',
}

DUPLICATE_OR_SHADOW = {
    'lean/InfoGeometry/Clifford/SplitTower.lean',
}

DIRECT_CANONICAL_PREFIXES = (
    'lean/InfoGeometry/Canonical/',
)

FACADE_BRANCH_PREFIXES = (
    'lean/InfoGeometry/Causal/',
    'lean/InfoGeometry/Clifford/',
    'lean/InfoGeometry/ExponentialFamily/',
    'lean/InfoGeometry/Krein/',
    'lean/InfoGeometry/Measure/',
    'lean/InfoGeometry/MeasureProjective/',
    'lean/InfoGeometry/Prequantum/',
    'lean/InfoGeometry/Projective/',
    'lean/InfoGeometry/Quantum/',
    'lean/InfoGeometry/Singular/',
)

DIRECT_OTHER = {
    'lean/InfoGeometry/Convex/SelfDualCone.lean',
    'lean/InfoGeometry/Cramer.lean',
    'lean/InfoGeometry/Math/Convexity.lean',
    'lean/InfoGeometry/PositiveMeasure.lean',
    'lean/InfoGeometry/RegularizedKL.lean',
    'lean/InfoGeometry/KK/NonVacuousIndex.lean',
}

NAMESPACE_RE = re.compile(r'^namespace\s+(.+)$')


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding='utf-8'))


def first_namespace(path: Path) -> str | None:
    try:
        for line in path.read_text(encoding='utf-8', errors='ignore').splitlines():
            m = NAMESPACE_RE.match(line.strip())
            if m:
                return m.group(1).strip()
    except OSError:
        return None
    return None


def classify(path_str: str) -> str:
    if path_str in EXCLUDE_NONCANONICAL:
        return 'exclude_noncanonical'
    if path_str in DUPLICATE_OR_SHADOW:
        return 'duplicate_or_shadow'
    if path_str in NAMESPACE_OR_ATTRIBUTION_FIX:
        return 'namespace_or_attribution_fix'
    if path_str.startswith(DIRECT_CANONICAL_PREFIXES):
        return 'absorb_direct_into_canonical_all'
    if path_str in DIRECT_OTHER:
        return 'absorb_direct_into_infogeometry_all'
    if path_str.startswith(FACADE_BRANCH_PREFIXES):
        return 'absorb_via_branch_facade'
    return 'review_manually'


def render_md(payload: dict[str, Any]) -> str:
    lines: list[str] = []
    cov = payload['coverage']
    lines.append('# Remaining `All` Coverage Classification')
    lines.append('')
    lines.append('This report classifies the declaration-bearing Lean files that are still outside the authoritative `InfoGeometry.All` export graph.')
    lines.append('')
    lines.append('## Summary')
    lines.append(f"- declaration-bearing source files: `{cov['repo_decl_files']}`")
    lines.append(f"- declaration-index files covered by current export root: `{cov['decl_index_files']}`")
    lines.append(f"- remaining missing declaration-bearing files: `{cov['missing_decl_files_count']}`")
    lines.append('')
    lines.append('## Buckets')
    for key, title in [
        ('absorb_direct_into_canonical_all', 'Absorb Directly Into `Canonical.All`'),
        ('absorb_direct_into_infogeometry_all', 'Absorb Directly Into `InfoGeometry.All`'),
        ('absorb_via_branch_facade', 'Absorb Via Branch Façade'),
        ('namespace_or_attribution_fix', 'Namespace / Attribution Fix Needed'),
        ('duplicate_or_shadow', 'Duplicate / Shadow Candidate'),
        ('exclude_noncanonical', 'Keep Out Of `All`'),
        ('review_manually', 'Manual Review'),
    ]:
        items = payload['buckets'][key]
        lines.append(f"### {title} ({len(items)})")
        if not items:
            lines.append('- none')
        else:
            for item in items:
                ns = item.get('namespace') or '-'
                lines.append(f"- `{item['path']}`")
                lines.append(f"  namespace: `{ns}`")
        lines.append('')
    lines.append('## Notes')
    for note in payload['notes']:
        lines.append(f'- {note}')
    lines.append('')
    return '\n'.join(lines)


def main() -> int:
    root = repo_root()
    report_path = root / 'reports' / 'dag' / 'true-root-order.json'
    obj = load_json(report_path)
    missing = list(obj['coverage']['missing_decl_files'])

    buckets: dict[str, list[dict[str, Any]]] = {
        'absorb_direct_into_canonical_all': [],
        'absorb_direct_into_infogeometry_all': [],
        'absorb_via_branch_facade': [],
        'namespace_or_attribution_fix': [],
        'duplicate_or_shadow': [],
        'exclude_noncanonical': [],
        'review_manually': [],
    }

    for rel in missing:
        ns = first_namespace(root / rel)
        buckets[classify(rel)].append({'path': rel, 'namespace': ns})

    for key in buckets:
        buckets[key].sort(key=lambda row: row['path'])

    notes = [
        'This report is a canonicalization plan, not a proof of semantic validity; every listed file already compiles in the default `InfoGeometry` library build.',
        'Files under `exclude_noncanonical` are intentionally not candidates for the public umbrella because they are tooling, unstable wrappers, timeout probes, or trivial stubs.',
        'Files under `namespace_or_attribution_fix` are not clean umbrella omissions; at least part of the problem is that their public declarations live under a shifted namespace or are poorly attributed by the declaration exporter.',
        'Example: `Projective/Normalize.lean` publishes key declarations under `PositiveMeasure.*`, and `Krein/Superalgebra.lean` publishes under `KreinGradedModule.*`.',
        'Example: `Clifford/SplitTower.lean` appears shadowed by `Clifford/Tower.lean` in the declaration index and should be deduplicated before any umbrella import decision.',
        'The safest next import pass is: add the remaining `Canonical/*` direct candidates first, then expand branch façades for projective/measure/quantum/singular branches, then fix namespace-attribution mismatches.',
    ]

    payload = {
        'source': str(report_path.relative_to(root)),
        'coverage': {
            'repo_decl_files': obj['coverage']['repo_decl_files'],
            'decl_index_files': obj['coverage']['decl_index_files'],
            'missing_decl_files_count': obj['coverage']['missing_decl_files_count'],
        },
        'buckets': buckets,
        'notes': notes,
    }

    out_dir = root / 'reports' / 'dag'
    out_dir.mkdir(parents=True, exist_ok=True)
    md_path = out_dir / 'missing-all-classification.md'
    json_path = out_dir / 'missing-all-classification.json'
    md_path.write_text(render_md(payload), encoding='utf-8')
    json_path.write_text(json.dumps(payload, indent=2), encoding='utf-8')
    print(f'[missing-all] wrote {md_path}')
    print(f'[missing-all] wrote {json_path}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
