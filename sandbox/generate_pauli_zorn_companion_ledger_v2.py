#!/usr/bin/env python3
from pathlib import Path
from collections import Counter
import hashlib, json, os, time

ROOT=Path('/home/goutev/repos/info-geometry-lean')
OUT=ROOT/'sandbox/pauli_zorn_companion_ledger.json'
EXCLUDE={'.git','.lake','node_modules','lean','dist','build','__pycache__'}
EXTS={'.lean','.py','.md','.txt','.json','.jsonl','.yaml','.yml','.toml','.xml','.csv','.ts','.js','.sh','.patch','.diff','.agda','.v','.thy','.m2','.sage','.jl','.rs','.cpp','.hpp','.c','.h'}
TERMS=['pauli','zorn','split octon','splitocton','quaternion','peirce','kingdon','paravector','minkowski','nilpotent','projector','chirality','gamma5','tomita','commutant','modularj','canonicalvectormatrixbridge','canonicalvectorequiv','kingdonzorn','abstractkingdon','preimagehom','hl_mul_hl','splitquaternionzorntrialityfactindex']
MAX_SNIPPETS=10

def main():
 out={'schema':'pauli-zorn-companion-v2','generated_at':time.time(),'root':str(ROOT),'terms':TERMS,'files':[],'errors':[]}
 n=nb=nl=0
 for base,dirs,files in os.walk(ROOT,followlinks=False):
  dirs[:]=[d for d in dirs if d not in EXCLUDE]
  for name in files:
   p=Path(base)/name
   if p.suffix.lower() not in EXTS: continue
   try:
    size=p.stat().st_size; n+=1; nb+=size; counts=Counter(); snippets=[]; lines=0; sha=hashlib.sha256()
    with p.open('rb') as f:
     for raw in f:
      lines+=1; sha.update(raw); text=raw.decode('utf-8',errors='ignore').lower()
      hits=[t for t in TERMS if t in text]
      for t in hits: counts[t]+=1
      if hits and len(snippets)<MAX_SNIPPETS:
       snippets.append({'line':lines,'terms':hits,'text':raw.decode('utf-8',errors='replace').strip()[:500]})
    nl+=lines
    if counts:
     out['files'].append({'path':str(p),'bytes':size,'lines':lines,'sha256':sha.hexdigest(),'counts':dict(counts),'snippets':snippets})
   except Exception as exc: out['errors'].append({'path':str(p),'error':repr(exc)})
 out['summary']={'scanned_files':n,'scanned_bytes':nb,'scanned_lines':nl,'matched_files':len(out['files']),'errors':len(out['errors'])}
 OUT.write_text(json.dumps(out,indent=2,ensure_ascii=False))
 print(json.dumps({'out':str(OUT),**out['summary']},indent=2))
if __name__=='__main__': main()
