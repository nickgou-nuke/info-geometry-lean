#!/usr/bin/env python3
"""New-source inventory and placeholder scan. Not a transitive Lean proof audit."""
from __future__ import annotations
from pathlib import Path
import json
import re

ROOT=Path(__file__).resolve().parents[1]
DIR=ROOT/'lean/InfoGeometry/Streaming'
REPORT=ROOT/'reports/streaming_boundary'
MODULES=['BipartiteGraphDirac','CausalMemory','G2GradedRouter','GaugeCovariantRouting',
         'PairingGapSeparation','PositiveBoundaryConditioning','StreamingBoundaryPristineChain',
         'UnipotentMemoryShift','WeakValueBoundary','StreamingBoundaryAudit']

def strip_comments(text):
    out=[];depth=0;i=0
    while i<len(text):
        if depth:
            if text.startswith('/-',i):depth+=1;i+=2
            elif text.startswith('-/',i):depth-=1;i+=2
            else:out.append('\n' if text[i]=='\n' else ' ');i+=1
        elif text.startswith('/-',i):depth=1;i+=2
        elif text.startswith('--',i):
            end=text.find('\n',i);i=len(text) if end<0 else end
        elif text[i]=='"':
            i+=1
            while i<len(text):
                if text[i]=='\\':i+=2
                elif text[i]=='"':i+=1;break
                else:i+=1
            out.append(' ')
        else:out.append(text[i]);i+=1
    if depth:raise ValueError('Unclosed block comment')
    return ''.join(out)

def main():
    decls=[];forbidden=[]
    for name in MODULES:
        p=DIR/(name+'.lean')
        code=strip_comments(p.read_text())
        for m in re.finditer(r'\b(?:sorry|admit|axiom|unsafe|implemented_by|native_decide|sorryAx)\b',code):
            forbidden.append({'path':str(p.relative_to(ROOT)),'token':m.group()})
        if p.stem=='StreamingBoundaryAudit':continue
        ns=re.search(r'^namespace (\S+)',code,re.M).group(1)
        for m in re.finditer(r'(?m)^(?:@\[[^\n]*\]\s*)?(private\s+)?(def|abbrev|theorem|lemma)\s+([^\s(:]+)',code):
            if not m[1]:decls.append({'name':ns+'.'+m[3],'kind':m[2],'path':str(p.relative_to(ROOT))})
    if forbidden:raise SystemExit('Forbidden tokens: '+repr(forbidden))
    audit=DIR/'StreamingBoundaryAudit.lean'
    expected={x['name'] for x in decls}
    commands={line.removeprefix('#print axioms ').strip() for line in audit.read_text().splitlines()
              if line.startswith('#print axioms ')}
    if expected!=commands:raise SystemExit('Audit coverage mismatch: '+repr(expected^commands))
    report={'new_lean_files':len(MODULES),'public_declarations':len(decls),
            'counts':{k:sum(d['kind']==k for d in decls) for k in ['theorem','lemma','def','abbrev']},
            'forbidden_tokens':forbidden,'audit_coverage_matches':True,
            'transitive_axiom_audit_executed':False}
    REPORT.mkdir(parents=True,exist_ok=True)
    (REPORT/'source-scan.json').write_text(json.dumps(report,indent=2)+'\n')
    (REPORT/'declaration-inventory.json').write_text(json.dumps(decls,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()

