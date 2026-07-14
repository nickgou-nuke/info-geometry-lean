#!/usr/bin/env python3
from pathlib import Path
from collections import Counter
import hashlib, json, os, time

ROOTS = [
    Path('/home/goutev/.hermes'), Path('/home/goutev/.codex'),
    Path('/home/goutev/.claude'), Path('/home/goutev/.pi'),
    Path('/home/goutev/.gemini'), Path('/home/goutev/.archon'),
    Path('/home/goutev/repos/info-geometry-lean-epoch3-codex-export'),
    Path('/home/goutev/repos/info-geometry-lean-fusion-migrate'),
    Path('/media/goutev/SP DS72/auto/proofs'),
]
TERMS = [
    'pauli','zorn','split octon','splitocton','quaternion','peirce','kingdon',
    'paravector','minkowski','nilpotent','projector','chirality','gamma5',
    'tomita','commutant','modularj','canonicalvectormatrixbridge',
    'canonicalvectorequiv','kingdonzorn','abstractkingdon','preimagehom',
    'hl_mul_hl','l_sector','splitquaternionzorntrialityfactindex',
]
EXTS = {'.jsonl','.json','.md','.txt','.log','.lean','.py','.patch','.diff','.yaml','.yml','.toml','.xml','.csv'}
MAX_SNIPPETS = 12

def scan_file(path, root):
    size = path.stat().st_size
    counts = Counter(); snippets=[]; sha=hashlib.sha256(); lines=0
    with path.open('rb') as f:
        for raw in f:
            sha.update(raw); lines += 1
            text = raw.decode('utf-8', errors='ignore').lower()
            hits = [t for t in TERMS if t in text]
            for t in hits: counts[t] += 1
            if hits and len(snippets) < MAX_SNIPPETS:
                snippets.append({'line':lines,'terms':hits,'text':raw.decode('utf-8',errors='replace').strip()[:500]})
    if not counts: return None, size, lines, sha.hexdigest()
    return {'root':str(root),'path':str(path),'bytes':size,'lines':lines,
            'sha256':sha.hexdigest(),'counts':dict(counts),'snippets':snippets}, size, lines, sha.hexdigest()

def main():
    out={'schema':'pauli-zorn-agent-provenance-v1','generated_at':time.time(),
         'terms':TERMS,'roots':[],'matches':[],'errors':[]}
    total_files=total_bytes=total_lines=0
    for root in ROOTS:
        rs={'path':str(root),'exists':root.exists(),'files':0,'bytes':0,'lines':0,'matches':0,'errors':0}
        if not root.exists(): out['roots'].append(rs); continue
        for base, dirs, files in os.walk(root, followlinks=False):
            dirs[:] = [d for d in dirs if d not in {'.git','.lake','node_modules','__pycache__'}]
            for name in files:
                p=Path(base)/name
                if p.suffix.lower() not in EXTS and 'session' not in name.lower() and 'history' not in name.lower(): continue
                try:
                    rec,size,lines,_=scan_file(p,root)
                    rs['files']+=1; rs['bytes']+=size; rs['lines']+=lines
                    total_files+=1; total_bytes+=size; total_lines+=lines
                    if rec: out['matches'].append(rec); rs['matches']+=1
                except Exception as exc:
                    rs['errors']+=1; out['errors'].append({'path':str(p),'error':repr(exc)})
        out['roots'].append(rs)
    out['summary']={'files':total_files,'bytes':total_bytes,'lines':total_lines,
                    'matched_files':len(out['matches']),'errors':len(out['errors'])}
    dest=Path('/home/goutev/repos/info-geometry-lean/sandbox/pauli_zorn_agent_provenance.json')
    dest.write_text(json.dumps(out,indent=2,ensure_ascii=False))
    print(json.dumps({'out':str(dest),**out['summary'],'roots':out['roots']},indent=2))

if __name__=='__main__': main()
