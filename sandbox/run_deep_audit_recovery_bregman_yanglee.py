#!/usr/bin/env python3
import os,re,json,hashlib,tarfile,zipfile,sqlite3
from pathlib import Path
from collections import Counter,defaultdict
from datetime import datetime,timezone
ROOT=Path('/home/goutev/repos/info-geometry-lean'); HOME=Path('/home/goutev')
OUTJ=ROOT/'sandbox/deep_audit_recovery_bregman_yanglee.json'; OUTM=ROOT/'sandbox/deep_audit_recovery_bregman_yanglee.md'
terms=[r'Bregman',r'Fenchel',r'Legendre',r'Jacobian',r'logNorm',r'log.?norm',r'Boltzmann',r'freeEnergy',r'free.?energy',r'twoPhasePartition',r'Lee.?Yang',r'Yang.?Lee',r'Leyang',r'zeta',r'xi',r'freez(?:e|ing|es|er)']
rx=re.compile('|'.join(terms),re.I); declrx=re.compile(r'^\s*(?:def|theorem|lemma|structure|class|abbrev|instance|axiom|opaque)\s+([\w.\'α-ωΑ-Ω]+)',re.M)
source_ext={'.lean','.patch','.diff','.rej'}; prose_ext={'.md','.txt','.json','.jsonl','.log','.yaml','.yml','.toml','.csv'}
# Explicit recovery/archive/backup/agent surfaces in repo and nearby repository snapshots.
explicit=[]
for p in ROOT.rglob('*'):
    s=str(p).lower(); n=p.name.lower()
    if (n.startswith('agent_writes_recovery') or n.startswith('agent_memory_recovery') or
        (p.parent==ROOT/'sandbox' and n.startswith('proof_recovery_')) or n in {'recover.patch','recovered_combined.lean'} or
        str(p).startswith(str(ROOT/'tools/multisystem/major_restore_non_overwriting')) or
        str(p).startswith(str(ROOT/'handover/injections')) or
        any(x in part.lower() for part in p.parts for x in ('backup','archive','recovery'))): explicit.append(p)
# Nearby archived/backup/recovery repos/dirs.
for p in (HOME/'repos').iterdir():
    if p.is_dir() and p!=ROOT and any(x in p.name.lower() for x in ('info-geometry-lean','archive','backup','recovery')): explicit.append(p)
# machine-local agent transcript/state stores, only likely data subtrees (not installed code/extensions).
agent_roots=[]
for p in [HOME/'.hermes',HOME/'.codex',HOME/'.pi',HOME/'.config'/'pi',HOME/'.local/share/pi',HOME/'.antigravity/User',HOME/'.antigravity-ide/User',HOME/'.antigravity-server/data/User',HOME/'.antigravity-ide-server/data/User']:
    if p.exists(): agent_roots.append(p)
# discover exact requested recovery directory names anywhere under home (pruned).
discovered=[]
skip={'node_modules','.lake','miniforge3','lean-dojo-venv','snap','Downloads','.cache','.git','target','extensions','bin','pkgs'}
for base,dirs,files in os.walk(HOME):
    dirs[:]=[d for d in dirs if d not in skip]
    for d in dirs:
        if d.lower().startswith(('agent_writes_recovery','agent_memory_recovery')): discovered.append(Path(base)/d)
explicit += discovered
# canonicalize roots/files; nested roots okay but de-dupe files later.
surfaces=[]
for p in explicit+agent_roots:
    try: q=p.resolve()
    except: q=p
    if q.exists() and q not in surfaces: surfaces.append(q)
# live owner index: current Lean owners, excluding artifact/sandbox/recovered trees.
owner_by_base=defaultdict(list); owner_decl=defaultdict(list)
for p in (ROOT/'lean').rglob('*.lean'):
    if '/Recovered/' in str(p): continue
    owner_by_base[p.name].append(str(p))
    try:
        t=p.read_text(errors='replace')
        for d in declrx.findall(t): owner_decl[d].append(str(p))
    except: pass
stats=Counter(); errors=[]; hits=[]; seen=set(); trunc=[]
MAX_FILE=64*1024*1024; MAX_EXCERPTS=80; CTX=4

def classify(path,text):
    ext=Path(path).suffix.lower()
    if ext in source_ext or re.search(r'(^|\n)\s*(def|theorem|lemma|structure|class|abbrev|instance|axiom|opaque)\s+',text): return 'source_or_diff'
    return 'prose_or_transcript'
def compare(path,text,decls):
    bases=[]
    bn=Path(path).name
    for suffix in ('Recovered.lean','_recovered.lean','.lean','.patch','.diff','.txt','.md'):
        if bn.endswith(suffix):
            stem=bn[:-len(suffix)]; bases += [stem+'.lean',stem.replace('Recovered','')+'.lean']; break
    owners=[]
    for b in [bn]+bases: owners += owner_by_base.get(b,[])
    for d in decls: owners += owner_decl.get(d,[])
    owners=sorted(set(owners)); comps=[]
    ah=hashlib.sha256(text.encode(errors='replace')).hexdigest()
    for o in owners[:30]:
        try:
            ot=Path(o).read_text(errors='replace'); same=ot==text
            overlap=len(set(decls)&set(declrx.findall(ot)))
            comps.append({'owner':o,'exact_content':same,'candidate_sha256':ah,'owner_sha256':hashlib.sha256(ot.encode()).hexdigest(),'shared_declarations':overlap})
        except Exception as e: errors.append(f'compare {o}: {e}')
    return owners,comps
def process_text(path,text,size,surface,virtual=False):
    if path in seen: return
    seen.add(path); stats['files_read']+=1; stats['bytes_read']+=len(text.encode(errors='replace'))
    lines=text.splitlines(); idx=[i for i,l in enumerate(lines) if rx.search(l)]
    if not idx:return
    stats['matching_files']+=1; stats['matching_lines']+=len(idx)
    decls=sorted(set(declrx.findall(text))); snippets=[]
    for i in idx[:MAX_EXCERPTS]:
        a=max(0,i-CTX);b=min(len(lines),i+CTX+1)
        snippets.append({'line':i+1,'matched_terms':sorted(set(m.group(0) for m in rx.finditer(lines[i])),key=str.lower),'context':'\n'.join(f'{j+1}: {lines[j]}' for j in range(a,b))})
    if len(idx)>MAX_EXCERPTS: trunc.append({'path':path,'reason':'excerpt_cap','total_matches':len(idx),'retained':MAX_EXCERPTS})
    owners,comps=compare(path,text,decls)
    hits.append({'path':path,'surface':str(surface),'virtual_archive_member':virtual,'size_bytes':size,'classification':classify(path,text),'match_line_count':len(idx),'declarations':decls,'owner_candidates':owners,'comparisons':comps,'snippets':snippets})
def readpath(p,surface):
    try:
        if not p.is_file():return
        stats['files_seen']+=1
        sz=p.stat().st_size
        if sz>MAX_FILE: trunc.append({'path':str(p),'reason':'file_size_cap','size':sz,'cap':MAX_FILE});stats['files_skipped_large']+=1;return
        if p.suffix.lower() in {'.tar','.gz','.tgz','.zip'}:
            try:
                if zipfile.is_zipfile(p):
                    with zipfile.ZipFile(p) as z:
                        for n in z.namelist():
                            info=z.getinfo(n)
                            if info.file_size<=MAX_FILE and Path(n).suffix.lower() in source_ext|prose_ext:
                                process_text(str(p)+'::'+n,z.read(n).decode(errors='replace'),info.file_size,surface,True);stats['archive_members_read']+=1
                elif tarfile.is_tarfile(p):
                    with tarfile.open(p) as t:
                        for m in t.getmembers():
                            if m.isfile() and m.size<=MAX_FILE and Path(m.name).suffix.lower() in source_ext|prose_ext:
                                f=t.extractfile(m); process_text(str(p)+'::'+m.name,f.read().decode(errors='replace'),m.size,surface,True);stats['archive_members_read']+=1
            except Exception as e: errors.append(f'archive {p}: {e}')
            return
        # readable textual likely files; include extensionless histories.
        if p.suffix.lower() not in source_ext|prose_ext|{'.sqlite','.db'} and p.name not in {'.hermes_history','history.jsonl'}: return
        if p.suffix.lower() in {'.sqlite','.db'}:
            # SQLite transcripts: dump textual columns rowwise with bounded rows/cells.
            try:
                con=sqlite3.connect(f'file:{p}?mode=ro',uri=True); out=[]
                for (tab,) in con.execute("select name from sqlite_master where type='table'"):
                    cols=[r[1] for r in con.execute(f'pragma table_info("{tab}")')]
                    for row in con.execute(f'select * from "{tab}" limit 200000'):
                        vals=[str(v) for v in row if isinstance(v,(str,bytes))]
                        if vals and rx.search(' '.join(vals)): out.append(f'-- table {tab}\n'+'\n'.join(vals))
                con.close()
                if out: process_text(str(p),'\n'.join(out),sz,surface)
            except Exception as e: errors.append(f'sqlite {p}: {e}')
            return
        process_text(str(p),p.read_text(errors='replace'),sz,surface)
    except (PermissionError,OSError) as e: errors.append(f'read {p}: {e}');stats['unreadable']+=1
for surface in surfaces:
    if surface.is_file(): readpath(surface,surface)
    else:
        for base,dirs,files in os.walk(surface):
            dirs[:]=[d for d in dirs if d not in {'.git','node_modules','.lake','target','extensions','bin','pkgs'}]
            for f in files: readpath(Path(base)/f,surface)
# sort, summaries
hits.sort(key=lambda x:x['path']); kinds=Counter(h['classification'] for h in hits)
report={'generated_utc':datetime.now(timezone.utc).isoformat(),'root':str(ROOT),'terms':terms,
 'scope':{'surfaces':[str(x) for x in surfaces],'agent_roots':[str(x) for x in agent_roots],'discovered_requested_dirs':[str(x) for x in discovered],
 'notes':['Current live owner index is lean/**/*.lean excluding Recovered directories.','Transcript SQLite tables were read-only and capped at 200000 rows per table.','Text files capped at 64 MiB; at most 80 contextual excerpts retained per matching file.','Binary extension/install/cache trees were excluded.']},
 'counts':dict(stats),'classification_counts':dict(kinds),'truncation':trunc,'errors':errors,'artifacts':hits}
OUTJ.write_text(json.dumps(report,indent=2,ensure_ascii=False))
md=['# Deep audit: recovery Bregman / Jacobian / free-energy / Yang–Lee','',f'Generated: `{report["generated_utc"]}`','',
'## Scope and counts','',f'- Surfaces: **{len(surfaces)}**; files seen: **{stats["files_seen"]}**; files read: **{stats["files_read"]}**; bytes read: **{stats["bytes_read"]}**.',f'- Matching artifacts: **{stats["matching_files"]}**; matching lines: **{stats["matching_lines"]}**; archive members read: **{stats["archive_members_read"]}**.',f'- Classification: `{dict(kinds)}`; truncation records: **{len(trunc)}**; read errors: **{len(errors)}**.','',
'### Audited surfaces']+[f'- `{x}`' for x in surfaces]+['','## Findings','']
for h in hits:
    md += [f'### `{h["path"]}`','',f'- Surface: `{h["surface"]}`',f'- Kind: **{h["classification"]}**; matching lines: **{h["match_line_count"]}**; size: **{h["size_bytes"]}** bytes.',f'- Declarations: '+(', '.join(f'`{d}`' for d in h['declarations']) if h['declarations'] else '_none extracted_'),f'- Current owner candidates: '+(', '.join(f'`{o}`' for o in h['owner_candidates']) if h['owner_candidates'] else '_none by basename/declaration_')]
    if h['comparisons']:
        md.append('- Comparisons: '+ '; '.join(f'`{c["owner"]}` exact={c["exact_content"]}, shared_decls={c["shared_declarations"]}' for c in h['comparisons']))
    md += ['','Representative matched contexts:','']
    for s in h['snippets'][:8]: md += [f'- Line {s["line"]}, terms `{", ".join(s["matched_terms"])}`:', '```text',s['context'],'```']
    if len(h['snippets'])>8: md.append(f'- _{len(h["snippets"])-8} more excerpts are in JSON._')
    md.append('')
md += ['## Truncation and errors','', 'Full structured truncation/error records are in the JSON.']
for t in trunc: md.append(f'- Truncated `{t["path"]}`: {t["reason"]}.')
for e in errors: md.append(f'- Error: `{e}`')
OUTM.write_text('\n'.join(md)+'\n')
print(json.dumps({'json':str(OUTJ),'markdown':str(OUTM),'counts':dict(stats),'hits':len(hits),'surfaces':len(surfaces),'truncation':len(trunc),'errors':len(errors)},indent=2))
