#!/usr/bin/env python3
"""Comment-aware scan of the new files and audit coverage, not proof verification."""
from __future__ import annotations
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    'Core/FinitePeirceMatrix',
    'Algebra/FourthRootPeirceProjectors',
    'Clifford/ExteriorDegreePhaseFour',
    'Canonical/ExteriorCyclotomicPeirceBridge',
]
AUDIT = 'Canonical/ExteriorCyclotomicPeirceAudit'


def strip_comments(text: str) -> str:
    out: list[str] = []
    i = depth = 0
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
        raise ValueError('Unclosed Lean comment')
    return ''.join(out)


def declarations() -> list[dict[str, str]]:
    found: list[dict[str, str]] = []
    for module in MODULES:
        path = ROOT / 'lean/InfoGeometry' / (module + '.lean')
        text = strip_comments(path.read_text())
        namespace = re.search(r'^namespace (\S+)', text, re.M)
        if namespace is None:
            raise ValueError(f'Namespace missing in {path}')
        for m in re.finditer(
            r'(?m)^(?:@\[[^\n]*?\]\s*)?(private\s+)?(theorem|lemma|def|abbrev)\s+([\w\u0080-\uffff]+)', text
        ):
            if not m[1]:
                found.append({'kind': m[2], 'name': namespace[1] + '.' + m[3],
                              'path': str(path.relative_to(ROOT))})
    return found


def main() -> None:
    inventory = declarations()
    forbidden = []
    for module in [*MODULES, AUDIT]:
        path = ROOT / 'lean/InfoGeometry' / (module + '.lean')
        text = strip_comments(path.read_text())
        for m in re.finditer(r'\b(?:sorry|admit|axiom|unsafe|implemented_by|native_decide|sorryAx)\b', text):
            forbidden.append({'path': str(path.relative_to(ROOT)), 'token': m[0]})
    if forbidden:
        raise SystemExit(f'Forbidden new-source tokens: {forbidden}')
    audit_path = ROOT / 'lean/InfoGeometry' / (AUDIT + '.lean')
    audited = re.findall(r'^#print axioms (\S+)', strip_comments(audit_path.read_text()), re.M)
    declared = {d['name'] for d in inventory}
    if set(audited) != declared or len(audited) != len(declared):
        raise SystemExit('Audit coverage mismatch: ' + repr({
            'missing': sorted(declared-set(audited)), 'extra': sorted(set(audited)-declared),
            'count': len(audited), 'unique_count': len(set(audited))}))
    result = {'new_Lean_files': len(MODULES)+1, 'public_declarations': len(inventory),
              'counts': {k: sum(d['kind'] == k for d in inventory)
                         for k in ['theorem', 'lemma', 'def', 'abbrev']},
              'forbidden_tokens': forbidden, 'audit_coverage_matches': True,
              'Lean_elaboration_executed': False, 'transitive_axiom_audit_executed': False}
    out = ROOT / 'reports/cyclotomic_peirce'
    out.mkdir(parents=True, exist_ok=True)
    (out / 'source-scan.json').write_text(json.dumps(result, indent=2) + '\n')
    (out / 'declaration-inventory.json').write_text(json.dumps(inventory, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
