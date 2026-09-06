#!/usr/bin/env python3
"""Scan this extension and check audit coverage; this does not inspect Lean dependencies."""
from __future__ import annotations
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    'Algebra/Zorn/PolarizedQuadraticExtension55',
    'Clifford/PolarizedMinkowski55',
    'Clifford/PolarizedBoundaryInvolutions',
    'Geometry/PolarizedBoundaryBivectors',
    'Canonical/PolarizedBoundary55PristineChain',
    'Canonical/PolarizedBoundary55Audit',
]


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(' ')
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('Unclosed Lean block comment')
    return ''.join(out)


def main() -> None:
    items: list[dict[str, str]] = []
    forbidden: list[dict[str, str]] = []
    audited: set[str] = set()
    for name in MODULES:
        path = ROOT / 'lean/InfoGeometry' / (name + '.lean')
        text = strip_comments_and_strings(path.read_text())
        for m in re.finditer(r'\b(?:sorry|admit|axiom|unsafe|implemented_by|native_decide|sorryAx)\b', text):
            forbidden.append({'path': str(path.relative_to(ROOT)), 'token': m.group()})
        if name.endswith('Audit'):
            audited = set(re.findall(r'^#print axioms (\S+)', text, re.M))
            continue
        namespace = re.search(r'^namespace (\S+)', text, re.M)
        if namespace is None:
            raise ValueError(f'No namespace in {path}')
        for m in re.finditer(r'(?m)^(?:@\[[^\n]*?\]\s*)?(private\s+)?(theorem|lemma|def|abbrev)\s+([\w\u0080-\uffff]+)', text):
            if not m[1]:
                items.append({'kind': m[2], 'name': namespace[1] + '.' + m[3],
                              'path': str(path.relative_to(ROOT))})
    if forbidden:
        raise SystemExit('Forbidden new-source tokens: ' + repr(forbidden))
    declared = {x['name'] for x in items}
    if declared != audited:
        raise SystemExit('Audit coverage mismatch: ' + repr({
            'missing': sorted(declared - audited), 'extra': sorted(audited - declared)}))
    result = {
        'new_Lean_files': len(MODULES), 'public_declarations': len(items),
        'counts': {k: sum(x['kind'] == k for x in items)
                   for k in ('theorem', 'lemma', 'def', 'abbrev')},
        'forbidden_tokens': forbidden, 'audit_coverage_matches': True,
        'transitive_axiom_audit_executed': False,
    }
    out = ROOT / 'reports/polarized_boundary55'
    out.mkdir(parents=True, exist_ok=True)
    (out / 'source-scan.json').write_text(json.dumps(result, indent=2) + '\n')
    (out / 'declaration-inventory.json').write_text(json.dumps(items, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
