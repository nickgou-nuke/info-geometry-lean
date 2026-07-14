#!/usr/bin/env python3
from pathlib import Path
import json, re, subprocess, time

ROOT=Path('/home/goutev/repos/info-geometry-lean')
OUT=ROOT/'sandbox/pauli_zorn_git_provenance.json'
TERMS=['pauli','zorn','octon','quaternion','peirce','kingdon','paravector','minkowski','tomita','commutant','modularJ','canonicalVectorEquiv','kingdonZorn','preimageHom','Hl_mul_Hl']
PAT='('+'|'.join(re.escape(t) for t in TERMS)+')'

def run(args,timeout=600):
 p=subprocess.run(['git',*args],cwd=ROOT,text=True,capture_output=True,timeout=timeout)
 return {'args':args,'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr}

def main():
 out={'schema':'pauli-zorn-git-provenance-v1','generated_at':time.time(),'terms':TERMS,'errors':[]}
 out['refs']=run(['show-ref'])
 out['worktrees']=run(['worktree','list','--porcelain'])
 out['reflog']=run(['reflog','show','--all','--date=iso','--format=%H%x09%gd%x09%ad%x09%gs'])
 out['history_regex']=run(['log','--all','--date=iso','--format=COMMIT%x09%H%x09%ad%x09%an%x09%s','--name-status','-G',PAT,'--','lean/InfoGeometry','external_refs','formalizations','proofs','tools','docs'],timeout=600)
 out['pickaxe']={}
 for term in ['canonicalVectorEquiv','kingdonZornLinearEquiv','preimageHom_comp_realization','Hl_mul_Hl','PauliZornTrifactor','SplitOctonionModularJ','finrank_canonicalZornDerivations']:
  out['pickaxe'][term]=run(['log','--all','--date=iso','--format=COMMIT%x09%H%x09%ad%x09%an%x09%s','--name-status','-S',term,'--','lean/InfoGeometry','external_refs'],timeout=300)
 fsck=run(['fsck','--full','--unreachable','--no-reflogs'],timeout=600); out['fsck']=fsck
 unreachable=[]
 for line in (fsck['stdout']+'\n'+fsck['stderr']).splitlines():
  m=re.match(r'unreachable (blob|commit|tree) ([0-9a-f]{40,64})$',line.strip())
  if m: unreachable.append((m.group(1),m.group(2)))
 hits=[]; scanned=0
 for kind,oid in unreachable:
  if kind!='blob': continue
  p=subprocess.run(['git','cat-file','blob',oid],cwd=ROOT,capture_output=True)
  scanned+=1
  text=p.stdout.decode('utf-8',errors='ignore')
  found=sorted({t for t in TERMS if t.lower() in text.lower()})
  if found:
   snippets=[]
   for i,line in enumerate(text.splitlines(),1):
    hs=[t for t in found if t.lower() in line.lower()]
    if hs and len(snippets)<20: snippets.append({'line':i,'terms':hs,'text':line[:500]})
   hits.append({'oid':oid,'bytes':len(p.stdout),'terms':found,'snippets':snippets})
 out['unreachable_scan']={'blobs_scanned':scanned,'matching_blobs':hits}
 OUT.write_text(json.dumps(out,indent=2,ensure_ascii=False))
 print(json.dumps({'out':str(OUT),'history_bytes':len(out['history_regex']['stdout']),'unreachable_blobs':scanned,'matching_unreachable':len(hits),'pickaxe_counts':{k:v['stdout'].count('COMMIT\t') for k,v in out['pickaxe'].items()}},indent=2))
if __name__=='__main__': main()
