#!/usr/bin/env python3
"""Comment-aware scan and inventory for this extension, not transitive proof verification."""
from __future__ import annotations
import json
import re
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
MODULES=[
 'Algebra/AffineOperatorFrame',
 'Algebra/Zorn/RegularCARVacuumSeparation',
 'Algebra/Zorn/SplitIdempotentTorus',
 'Clifford/ExteriorNegativeCliffordReflection',
 'Clifford/ExteriorZornCARIntertwiner',
 'Physics/SpinAffineCasimirRigidity',
 'Quantum/QuaternionSpinTimeReversal',
 'Canonical/SpinAffineExteriorPristineChain',
 'Canonical/SpinAffineExteriorAudit',
]

def strip(text):
    out=[];i=0;depth=0
    while i<len(text):
        if depth:
            if text.startswith('/-',i):depth+=1;i+=2
            elif text.startswith('-/',i):depth-=1;i+=2
            else:out.append('\n' if text[i]=='\n' else ' ');i+=1
        elif text.startswith('/-',i):depth=1;i+=2
        elif text.startswith('--',i):
            j=text.find('\n',i);i=len(text) if j<0 else j
        elif text[i]=='"':
            i+=1
            while i<len(text):
                if text[i]=='\\':i+=2
                elif text[i]=='"':i+=1;break
                else:i+=1
            out.append(' ')
        else:out.append(text[i]);i+=1
    if depth: raise ValueError('Unclosed Lean block comment')
    return ''.join(out)

def main():
    items=[];forbidden=[];audited=set()
    for name in MODULES:
        p=ROOT/'lean/InfoGeometry'/(name+'.lean')
        text=strip(p.read_text())
        for m in re.finditer(r'\b(?:sorry|admit|axiom|unsafe|implemented_by|native_decide|sorryAx)\b',text):
            forbidden.append({'path':str(p.relative_to(ROOT)),'token':m.group()})
        if name.endswith('Audit'):
            audited=set(re.findall(r'^#print axioms (\S+)',text,re.M))
            continue
        ns=re.search(r'^namespace (\S+)',text,re.M).group(1)
        for m in re.finditer(r'(?m)^(?:@\[[^\n]*?\]\s*)?(private\s+)?(theorem|lemma|def|abbrev)\s+([\w\u0080-\uffff]+)',text):
            if not m[1]:items.append({'kind':m[2],'name':ns+'.'+m[3],
                                     'path':str(p.relative_to(ROOT))})
    if forbidden: raise SystemExit('Forbidden new-source tokens: '+repr(forbidden))
    declared={x['name'] for x in items}
    if declared != audited:
        raise SystemExit('Audit coverage mismatch: '+repr({'missing':sorted(declared-audited),
                                                         'extra':sorted(audited-declared)}))
    counts={k:sum(x['kind']==k for x in items) for k in ('theorem','lemma','def','abbrev')}
    scan={'new_Lean_files':len(MODULES),'public_declarations':len(items),'counts':counts,
          'forbidden_tokens':forbidden,'audit_coverage_matches':True,
          'transitive_axiom_audit_executed':False}
    out=ROOT/'reports/spin_affine_exterior';out.mkdir(parents=True,exist_ok=True)
    (out/'source-scan.json').write_text(json.dumps(scan,indent=2)+'\n')
    (out/'declaration-inventory.json').write_text(json.dumps(items,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(scan,indent=2))

if __name__=='__main__':main()
