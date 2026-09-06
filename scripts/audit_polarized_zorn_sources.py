#!/usr/bin/env python3
"""Comment-aware source hygiene only; not a Lean parser or kernel."""
from pathlib import Path
import json
import re

ROOT=Path(__file__).resolve().parents[1]

def executable(text: str) -> str:
    out=[]; i=0; depth=0
    while i<len(text):
        if depth:
            if text.startswith('/-',i): depth+=1; i+=2
            elif text.startswith('-/',i): depth-=1; i+=2
            else:
                out.append('\n' if text[i]=='\n' else ' '); i+=1
        elif text.startswith('/-',i): depth=1; out.append(' '); i+=2
        elif text.startswith('--',i):
            j=text.find('\n',i); i=len(text) if j<0 else j
        elif text[i]=='"':
            i+=1
            while i<len(text):
                if text[i]=='\\': i+=2
                elif text[i]=='"': i+=1; break
                else: i+=1
            out.append(' ')
        else: out.append(text[i]); i+=1
    if depth: raise ValueError('unclosed comment')
    return ''.join(out)

bad=[]; theorems=[]; declarations=[]
paths = (
    'Canonical/Cl11ZornActionSeparation.lean',
    'Canonical/OperatorZornPolarizationSymmetry.lean',
    'Canonical/PolarizedZornBoundaryCoefficient.lean',
    'Canonical/ZornPolarizationMetricBridge.lean',
    'Clifford/PolarizedFourVectorNeutralCarrier.lean',
    'Canonical/PolarizedZornReconstruction.lean',
    'Canonical/PolarizedZornReconstructionAudit.lean',
)
files=[ROOT/'lean/InfoGeometry'/p for p in paths]
for file in files:
    src=executable(file.read_text())
    for word in re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|sorryAx)\b',src):
        bad.append((str(file.relative_to(ROOT)),word))
    ns=re.search(r'^namespace (\S+)',src,re.M)
    if ns:
        for kind,name in re.findall(r'\b(theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_\']*)',src):
            declarations.append(ns.group(1)+'.'+name)
            if kind in ('theorem','lemma'): theorems.append(ns.group(1)+'.'+name)
audit=(ROOT/'lean/InfoGeometry/Canonical/PolarizedZornReconstructionAudit.lean').read_text()
queries=re.findall(r'^#print axioms (\S+)',audit,re.M)
if set(queries)!=set(declarations) or len(queries)!=len(declarations):
    raise SystemExit('Audit does not cover every new declaration exactly once')
report={'status':'PASS' if not bad else 'FAIL','evidence':'source hygiene only; NOT elaboration or transitive axiom certification',
        'lean_files':len(files),'theorems':len(theorems),'declarations':len(declarations),
        'axiom_queries':len(queries),'forbidden_executable_tokens':bad}
(ROOT/'reports').mkdir(exist_ok=True)
(ROOT/'reports/source-scan.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
if bad: raise SystemExit(1)
