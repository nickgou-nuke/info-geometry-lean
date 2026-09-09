#!/usr/bin/env python3
"""Generate source hashes and the complete explicit-declaration axiom readout.

A lexical scan is not elaboration and not an audit of transitive axioms.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
PATHS = [
    'lean/InfoGeometry/Canonical/SchnakenbergHodgeConstruction.lean',
    'lean/InfoGeometry/Projective/GraphCycleEntropy.lean',
    'lean/InfoGeometry/Canonical/RealPartnerProjectiveSeparation.lean',
    'lean/InfoGeometry/Canonical/OperatorZornBilayerDefect.lean',
    'lean/InfoGeometry/Canonical/ProjectiveGraphZornBilayer.lean',
]


def stripped(text: str) -> str:
    result: list[str] = []
    depth=0
    in_string=False
    i=0
    while i < len(text):
        if depth:
            if text.startswith('/-',i): depth+=1; result.extend('  ');i+=2
            elif text.startswith('-/',i): depth-=1;result.extend('  ');i+=2
            else: result.append('\n' if text[i]=='\n' else ' ');i+=1
        elif in_string:
            if text[i]=='\\': result.extend('  ');i+=2
            elif text[i]=='"': in_string=False;result.append(' ');i+=1
            else: result.append('\n' if text[i]=='\n' else ' ');i+=1
        elif text.startswith('/-',i): depth=1;result.extend('  ');i+=2
        elif text.startswith('--',i):
            end=text.find('\n',i)
            if end<0: end=len(text)
            result.extend(' '*(end-i));i=end
        elif text[i]=='"': in_string=True;result.append(' ');i+=1
        else: result.append(text[i]);i+=1
    if depth or in_string:
        raise ValueError('Unterminated comment or string')
    return ''.join(result)


def main() -> None:
    declarations=[]
    modules=[]
    for name in PATHS:
        raw=(ROOT/name).read_bytes()
        text=raw.decode('utf-8')
        clean=stripped(text)
        banned=re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',clean)
        if banned: raise AssertionError(f'{name}: forbidden source tokens {banned}')
        namespace=''
        own=[]
        for line in clean.splitlines():
            n=re.match(r'^namespace\s+(\S+)',line)
            if n: namespace=n.group(1)
            d=re.match(r'^(?:@\[[^\]]*\]\s*)?(def|abbrev|theorem|lemma|instance)\s+([A-Za-z_][A-Za-z_0-9]*)',line)
            if d:
                if not namespace: raise AssertionError(f'{name}: declaration without namespace')
                own.append({'name':namespace+'.'+d.group(2),'kind':d.group(1)})
        if len({x['name'] for x in own})!=len(own):
            raise AssertionError(f'{name}: duplicate declaration names')
        declarations+=own
        modules.append({'path':name,'sha256':hashlib.sha256(raw).hexdigest(),
                        'git_blob_sha':hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(),
                        'theorems':sum(d['kind'] in {'theorem','lemma'} for d in own),
                        'declarations':len(own)})
    if len({x['name'] for x in declarations})!=len(declarations):
        raise AssertionError('Duplicate explicit declaration names')
    audit='import InfoGeometry.Canonical.ProjectiveGraphZornBilayer\n\n'
    audit+='\n'.join('#print axioms '+d['name'] for d in declarations)+'\n'
    (ROOT/'tests').mkdir(exist_ok=True)
    (ROOT/'tests/ProjectiveGraphZornBilayerAxiomAudit.lean').write_text(audit)
    report={'lean_kernel_verified':False,
            'parent_commit':'71e683c8388acfd6101d554aaec0771cc886d2a2',
            'source_modules':len(modules),
            'theorem_count':sum(m['theorems'] for m in modules),
            'declaration_count':len(declarations),
            'source_token_scan':'passed; lexical only, not elaboration or transitive axiom verification',
            'modules':modules}
    (ROOT/'reports').mkdir(exist_ok=True)
    (ROOT/'reports/projective-graph-zorn-source-manifest.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in {'modules','declarations'}},indent=2))

if __name__=='__main__':main()
