#!/usr/bin/env python3
import os,re,json
from pathlib import Path
ROOT=Path('/home/goutev/repos/info-geometry-lean')
OUT=ROOT/'sandbox/pauli_zorn_scan_raw.json'
SKIP={'.git','.lake','node_modules','__pycache__','.venv','venv','build','dist'}
exts={'.lean','.py','.sage','.md','.rst','.txt','.json','.yaml','.yml','.toml','.v','.thy','.gap','.g','.m2','.mac','.ipynb','.sh'}
terms={
 'pauli':r'(?i)pauli|σ[0-9+\-]|sigma(?:0|1|2|3|plus|minus)',
 'zorn':r'(?i)zorn(?:matrix|coord|split|norm|mul)?',
 'peirce':r'(?i)peirce|idempotent projector|colorProject|anticolorProject',
 'quaternion':r'(?i)quatern|biquatern|cayley.?dickson|albertstep',
 'minkowski_det':r'(?i)minkowski|lightlike|light.?cone|null momentum|casimir.{0,30}det|det.{0,30}(null|mass)',
 'ladder_projector':r'(?i)ladder|raising|lowering|nilpotent.{0,20}(operator|generator)|projector',
 'chirality':r'(?i)chirality|chiral|gamma.?5|γ.?5',
 'tomita_commutant':r'(?i)tomita|commutant|modular conjugation',
 'equivalence_inflation':r'(?i)categorical equivalence|algebra(?:ic)? equivalence|AlgEquiv|RingEquiv|LinearEquiv|inflation|isomorph'
}
rx={k:re.compile(v) for k,v in terms.items()}
declrx=re.compile(r'^\s*(?:(?:noncomputable|private|protected)\s+)*(?:@[\w\[\],.\s]+\s*)?(def|abbrev|structure|class|inductive|theorem|lemma|axiom|opaque|example|instance|corollary)\s+([\w\u0080-\uffff\'₀-₉]+)',re.M)
rows=[]
scan_roots=[ROOT/x for x in ('lean/InfoGeometry','tools','docs','external_refs','sandbox')]
for scan_root in scan_roots:
 for dp,dns,fns in os.walk(scan_root):
  dns[:]=[d for d in dns if d not in SKIP and not d.startswith('.mypy')]
  for fn in fns:
  p=Path(dp)/fn
  if p.suffix.lower() not in exts: continue
   try:
    if p.stat().st_size > 2_000_000: continue
    text=p.read_text(errors='ignore')
   except: continue
   low=text.lower()
   if not any(s in low for s in ('pauli','zorn','peirce','quatern','biquatern','cayley-dickson','cayley_dickson','albertstep')): continue
  hits={k:len(r.findall(text)) for k,r in rx.items()}
  # Core-family candidate: direct central term, or intersection with peripheral term.
  core=hits['pauli'] or hits['zorn'] or hits['peirce'] or hits['quaternion']
  if not core: continue
  dec=[]
  for m in declrx.finditer(text):
   ln=text.count('\n',0,m.start())+1
   # retain declarations with family term in +/- 400 chars or owner file itself highly central
   ctx=text[max(0,m.start()-250):min(len(text),m.end()+500)]
   dh={k:bool(r.search(ctx)) for k,r in rx.items()}
   if any(dh[k] for k in ('pauli','zorn','peirce','quaternion')):
    body=text[m.end(): text.find('\n\n',m.end()) if text.find('\n\n',m.end())!=-1 else min(len(text),m.end()+800)]
    dec.append({'kind':m.group(1),'name':m.group(2),'line':ln,'near': [k for k,v in dh.items() if v], 'body_flags':{'sorry':bool(re.search(r'\bsorry\b',body)),'admit':bool(re.search(r'\badmit(?:ted)?\b',body)),'by_proof':':= by' in body or re.search(r':\s*.*:=\s*by',body,re.S) is not None,'rfl':bool(re.search(r'\b(rfl|by\s+rfl)\b',body)),'decide':bool(re.search(r'\bdecide\b',body))}})
  rows.append({'path':str(p.relative_to(ROOT)),'extension':p.suffix.lower(),'hits':hits,'declarations':dec,'file_flags':{'sorry_count':len(re.findall(r'\bsorry\b',text)),'admit_count':len(re.findall(r'\badmit(?:ted)?\b',text)),'axiom_count':len(re.findall(r'^\s*axiom\b',text,re.M))},'lines':text.count('\n')+1})
rows.sort(key=lambda r:r['path'])
OUT.write_text(json.dumps({'root':str(ROOT),'candidate_count':len(rows),'candidates':rows},indent=2))
print(json.dumps({'out':str(OUT),'candidate_count':len(rows),'by_extension':{e:sum(r['extension']==e for r in rows) for e in sorted(set(r['extension'] for r in rows))},'sorry_files':sum(bool(r['file_flags']['sorry_count']) for r in rows),'axiom_files':sum(bool(r['file_flags']['axiom_count']) for r in rows)},indent=2))
