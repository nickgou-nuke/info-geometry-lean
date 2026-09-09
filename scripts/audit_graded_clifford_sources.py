#!/usr/bin/env python3
"""Comment-aware hygiene and audit coverage; NOT a Lean elaborator."""
from pathlib import Path
import json
import re
ROOT=Path(__file__).resolve().parents[1]
PATHS=[
'Algebra/FourthRootSpectralProjectors.lean',
'Algebra/CyclotomicPeirceMatrix.lean',
'Algebra/CyclicShiftNilpotencySeparation.lean',
'Clifford/ExteriorDegreeFourierClock.lean',
'Clifford/FourFrameVolumeAndParavector.lean',
'Canonical/GradedCliffordPeirceReconstruction.lean',
'Canonical/GradedCliffordPeirceAudit.lean']

def executable(text):
    out=[];i=0;depth=0
    while i<len(text):
        if depth:
            if text.startswith('/-',i): depth+=1;i+=2
            elif text.startswith('-/',i): depth-=1;i+=2
            else: out.append('\n' if text[i]=='\n' else ' ');i+=1
        elif text.startswith('/-',i): depth=1;out.append(' ');i+=2
        elif text.startswith('--',i):
            j=text.find('\n',i);i=len(text) if j<0 else j
        elif text[i]=='"':
            i+=1
            while i<len(text):
                if text[i]=='\\': i+=2
                elif text[i]=='"': i+=1;break
                else: i+=1
            out.append(' ')
        else: out.append(text[i]);i+=1
    if depth: raise ValueError('unclosed block comment')
    return ''.join(out)

bad=[];decl=[];theorems=[]
for rel in PATHS:
    path=ROOT/'lean/InfoGeometry'/rel
    src=executable(path.read_text())
    for word in re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|sorryAx)\b',src):
        bad.append({'path':rel,'token':word})
    ns=re.search(r'^namespace (\S+)',src,re.M)
    if ns:
        for kind,name in re.findall(r'^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(def|abbrev|theorem|lemma)\s+([^\s(:]+)',src,re.M):
            full=ns.group(1)+'.'+name;decl.append(full)
            if kind in ('theorem','lemma'): theorems.append(full)
audit=(ROOT/'lean/InfoGeometry/Canonical/GradedCliffordPeirceAudit.lean').read_text()
queries=re.findall(r'^#print axioms (\S+)',audit,re.M)
if len(set(queries))!=len(queries) or set(queries)!=set(decl):
    raise SystemExit('Audit does not cover every declaration exactly once')
report={'status':'PASS' if not bad else 'FAIL','evidence':'source hygiene only; NOT elaboration or transitive axiom certification',
        'lean_files':len(PATHS),'theorems':len(theorems),'declarations':len(decl),'axiom_queries':len(queries),
        'forbidden_executable_tokens':bad}
out=ROOT/'reports/graded-clifford-source-scan.json';out.parent.mkdir(exist_ok=True)
out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if bad: raise SystemExit(1)
