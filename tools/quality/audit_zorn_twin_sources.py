#!/usr/bin/env python3
"""Lexical source audit and native-audit input generation, not a proof checker."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
MODULES = [
    'Canonical/OperatorZornOrderedChannels',
    'Canonical/OperatorZornExchangeAutomorphism',
    'Canonical/OperatorZornCoefficientNucleus',
    'Canonical/OperatorZornMatrixPeirce',
    'Canonical/OperatorZornFourfoldPeirce',
    'Canonical/KreinConjugationTypeSeparation',
    'Projective/TwinRankOneWeakRatio',
    'Canonical/OperatorZornTwinCyclotomic',
]


def erase_comments_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1; out.extend('  '); i += 2
            elif text.startswith('-/', i):
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif quoted:
            if text[i] == '\\':
                out.extend('  '); i += 2
            elif text[i] == '"':
                quoted = False; out.append(' '); i += 1
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('/-', i):
            depth = 1; out.extend('  '); i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0: end = len(text)
            out.extend(' ' * (end-i)); i = end
        elif text[i] == '"':
            quoted = True; out.append(' '); i += 1
        else:
            out.append(text[i]); i += 1
    if depth or quoted:
        raise ValueError('Unterminated source comment or string')
    return ''.join(out)


def main() -> None:
    declarations: list[dict[str, str]] = []
    files = []
    for module in MODULES:
        path = ROOT / 'lean/InfoGeometry' / (module + '.lean')
        raw = path.read_bytes()
        clean = erase_comments_strings(raw.decode('utf-8'))
        forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', clean)
        if forbidden:
            raise ValueError(f'{path}: forbidden source tokens {forbidden}')
        namespace = None
        own = []
        for line in clean.splitlines():
            ns = re.match(r'^namespace\s+(\S+)', line)
            if ns: namespace = ns.group(1)
            dec = re.match(r'^(?:@\[[^\]]*\]\s*)?(def|abbrev|theorem|lemma|instance)\s+([A-Za-z_][A-Za-z_0-9]*)', line)
            if dec:
                if not namespace: raise ValueError(f'{path}: missing namespace')
                own.append({'name': namespace + '.' + dec.group(2), 'kind': dec.group(1)})
        declarations.extend(own)
        files.append({'path': str(path.relative_to(ROOT)),
                      'sha256': hashlib.sha256(raw).hexdigest(),
                      'git_blob_sha': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
                      'declaration_count': len(own),
                      'theorem_count': sum(d['kind'] in {'theorem', 'lemma'} for d in own)})
    names = [d['name'] for d in declarations]
    if not names or len(names) != len(set(names)):
        raise ValueError('Empty or duplicate declaration inventory')
    audit = 'import InfoGeometry.Canonical.OperatorZornTwinCyclotomic\n\n'
    audit += '\n'.join('#print axioms ' + name for name in names) + '\n'
    (ROOT / 'tests').mkdir(exist_ok=True)
    (ROOT / 'tests/OperatorZornTwinCyclotomicAxiomAudit.lean').write_text(audit, encoding='utf-8')
    manifest = {'lean_kernel_verified': False,
                'parent_commit': 'eb93f7405c2a8e9ad64e15c3bf172317aa960513',
                'source_modules': len(files), 'declaration_count': len(names),
                'theorem_count': sum(f['theorem_count'] for f in files),
                'source_scan': 'passed; lexical only, not elaboration or transitive-axiom verification',
                'files': files, 'declarations': declarations}
    (ROOT / 'reports').mkdir(exist_ok=True)
    (ROOT / 'reports/operator-zorn-twin-source-manifest.json').write_text(
        json.dumps(manifest, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in manifest.items() if k not in {'files','declarations'}}, indent=2))

if __name__ == '__main__':
    main()
