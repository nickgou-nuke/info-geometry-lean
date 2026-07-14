#!/usr/bin/env python3
"""Bounded exhaustive scan outside lean/, .git/, and .lake/."""
from __future__ import annotations
import hashlib, json, os, re
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/home/goutev/repos/info-geometry-lean')
OUT = ROOT / 'sandbox/pauli_zorn_companion_ledger.json'
EXCLUDED_DIR_NAMES = {'.git', '.lake'}
EXPLICIT = ['tools','proofs','formalizations','formalization','formal','coq','isabelle','docs','external_refs','tmp','sandbox']
RECOVERY_ARCHIVE_TOPS = sorted(p.name for p in ROOT.iterdir() if p.is_dir() and ('recover' in p.name.lower() or 'archive' in p.name.lower()))
CODE_EXT = {'.py','.sage','.g','.gap','.m2','.sing','.v','.thy','.ml','.mli','.hs','.lhs','.rs','.c','.cc','.cpp','.cxx','.h','.hpp','.java','.scala','.js','.jsx','.ts','.tsx','.sh','.bash','.zsh','.fish','.aql','.lean','.ipynb'}
PROSE_EXT = {'.md','.markdown','.rst','.txt','.tex','.bib','.adoc','.org','.html','.htm','.xml','.yaml','.yml','.toml','.json','.jsonl','.csv','.tsv','.cff'}
ELIGIBLE = CODE_EXT | PROSE_EXT
ARCHIVE_EXT = {'.zip','.tar','.tgz','.gz','.bz2','.xz','.7z','.rar','.jar','.war','.whl','.deb','.rpm','.zst'}
KEYWORDS = {
 'pauli': re.compile(r'(?i)\bpauli\b|\bsigma[_ ]?[0-3xyz]\b|σ[₀₁₂₃xyz]?'),
 'zorn': re.compile(r'(?i)\bzorn(?:\w*)\b'),
 'quaternion': re.compile(r'(?i)\b(?:bi|dual|split)?quaternion(?:ic|s)?\b|\bquaternions?\b'),
 'peirce': re.compile(r'(?i)\bpeirce(?:\w*)\b'),
}
BRIDGES = {
 'determinant_minkowski': re.compile(r'(?i)det(?:erminant)?.{0,80}(?:minkowski|null|light.?cone|mass)|(?:minkowski|null|light.?cone|mass).{0,80}det(?:erminant)?'),
 'ladder_projector': re.compile(r'(?i)(?:ladder|raising|lowering|nilpotent).{0,80}projector|projector.{0,80}(?:ladder|raising|lowering|nilpotent)'),
 'chirality': re.compile(r'(?i)\bchiral(?:ity)?\b|gamma.?5|γ.?5'),
 'tomita_commutant': re.compile(r'(?i)\btomita\b|\bcommutant\b|modular conjugation'),
 'equivalence': re.compile(r'(?i)\b(?:equivalence|equivalent|isomorph(?:ism|ic)?|bijection|AlgEquiv|RingEquiv|LinearEquiv)\b'),
}
OVERCLAIM = re.compile(r'(?i)\b(?:fully|completely|rigorously|formally)\s+(?:proved|verified|formalized|complete)|\b(?:proves?|establishes?|demonstrates?)\s+(?:the\s+)?(?:full|complete|exact|physical)|\bno\s+(?:axioms|assumptions|gaps|sorries)\b|\bproduction[- ]ready\b|\btheorem[- ]complete\b')
WEAK_MARKERS = re.compile(r'(?i)\b(?:TODO|FIXME|sorry|admit(?:ted)?|axiom|placeholder|conjecture|assum(?:e|ption)|heuristic|surrogate|numerical(?:ly)?|evidence only|not (?:yet )?proved)\b')
MAX_SNIPPET = 280

roots = [ROOT/x for x in EXPLICIT if (ROOT/x).exists()] + [ROOT/x for x in RECOVERY_ARCHIVE_TOPS]
# Root files are an explicit lane.
files: dict[str, tuple[Path,str]] = {}
for p in ROOT.iterdir():
    if p.is_file(): files[p.name]=(p,'root_files')
for base in roots:
    lane = base.relative_to(ROOT).parts[0]
    for dp,dns,fns in os.walk(base):
        dns[:] = [d for d in dns if d not in EXCLUDED_DIR_NAMES]
        for fn in fns:
            p=Path(dp)/fn
            rel=p.relative_to(ROOT).as_posix()
            files.setdefault(rel,(p,lane))

archive_files=[]; skipped=[]; inventories=[]; matches=[]
lane_stats=defaultdict(Counter)
for rel,(p,lane) in sorted(files.items()):
    try: size=p.stat().st_size
    except OSError as e:
        skipped.append({'path':rel,'reason':'stat_error','detail':str(e)}); lane_stats[lane]['skipped']+=1; continue
    suffix=p.suffix.lower()
    if suffix in ARCHIVE_EXT:
        archive_files.append({'path':rel,'size_bytes':size,'suffix':suffix,'lane':lane})
    if suffix not in ELIGIBLE:
        skipped.append({'path':rel,'reason':'non_source_doc_class','size_bytes':size,'suffix':suffix or None,'lane':lane})
        lane_stats[lane]['skipped']+=1; continue
    try:
        raw=p.read_bytes()
    except OSError as e:
        skipped.append({'path':rel,'reason':'read_error','detail':str(e),'size_bytes':size,'lane':lane}); lane_stats[lane]['skipped']+=1; continue
    if b'\x00' in raw[:65536]:
        skipped.append({'path':rel,'reason':'binary_or_nul','size_bytes':size,'suffix':suffix,'lane':lane}); lane_stats[lane]['skipped']+=1; continue
    text=raw.decode('utf-8',errors='replace')
    kind='code' if suffix in CODE_EXT else 'prose'
    counts={k:len(rx.findall(text)) for k,rx in KEYWORDS.items()}
    bridge_counts={k:len(rx.findall(text)) for k,rx in BRIDGES.items()}
    term_total=sum(counts.values())
    lines=text.splitlines()
    hit_lines=[]; overclaim_lines=[]
    for no,line in enumerate(lines,1):
        terms=[k for k,rx in KEYWORDS.items() if rx.search(line)]
        bridges=[k for k,rx in BRIDGES.items() if rx.search(line)]
        if terms:
            hit_lines.append({'line':no,'terms':terms,'bridges':bridges,'snippet':line.strip()[:MAX_SNIPPET]})
        if OVERCLAIM.search(line) and (terms or term_total):
            overclaim_lines.append({'line':no,'snippet':line.strip()[:MAX_SNIPPET],'weak_marker_same_line':bool(WEAK_MARKERS.search(line))})
    rec={'path':rel,'lane':lane,'class':kind,'suffix':suffix,'size_bytes':size,'line_count':len(lines),
         'sha256':hashlib.sha256(raw).hexdigest(),'keyword_counts':counts,'bridge_counts':bridge_counts,
         'weak_marker_counts':{'sorry':len(re.findall(r'\bsorry\b',text,re.I)),'admit':len(re.findall(r'\badmit(?:ted)?\b',text,re.I)),'axiom':len(re.findall(r'(?im)^\s*axiom\b',text)),'todo_fixme':len(re.findall(r'(?i)\b(?:TODO|FIXME)\b',text))}}
    inventories.append(rec)
    lane_stats[lane]['eligible_scanned']+=1; lane_stats[lane][kind]+=1
    if size>5_000_000: lane_stats[lane]['oversized_scanned']+=1
    if term_total:
        lane_stats[lane]['matching_files']+=1; lane_stats[lane][f'matching_{kind}']+=1
        matches.append({**rec,'hit_lines':hit_lines,'overclaim_lines':overclaim_lines})

all_lanes=sorted(set([x for x in EXPLICIT if (ROOT/x).exists()] + RECOVERY_ARCHIVE_TOPS + ['root_files']))
lane_summary={}
for lane in all_lanes:
    s=lane_stats[lane]
    lane_summary[lane]={k:s[k] for k in sorted(s)}
    lane_summary[lane]['incomplete_lane']=s['eligible_scanned']==0 or s['matching_files']==0
    lane_summary[lane]['incomplete_reason']='no eligible source/doc files scanned' if s['eligible_scanned']==0 else ('no Pauli/Zorn/quaternion/Peirce match' if s['matching_files']==0 else None)

overclaims=[]
for m in matches:
    for o in m['overclaim_lines']:
        overclaims.append({'path':m['path'],'class':m['class'],**o})
oversized=[{'path':r['path'],'size_bytes':r['size_bytes'],'class':r['class'],'lane':r['lane'],'disposition':'scanned_in_full'} for r in inventories if r['size_bytes']>5_000_000]
ledger={
 'schema':'pauli-zorn-companion-ledger/v1','generated_at':datetime.now(timezone.utc).isoformat(),
 'scope':{'root':str(ROOT),'included_explicit_roots':EXPLICIT,'included_recovery_archive_top_roots':RECOVERY_ARCHIVE_TOPS,'included_root_files':True,'excluded_directory_names':['lean','.git','.lake'],'note':'Top-level lean/ is outside scope; nested .git and .lake directories pruned. Non-source/document classes are inventoried as skipped.'},
 'method':{'source_extensions':sorted(CODE_EXT),'prose_extensions':sorted(PROSE_EXT),'oversized_threshold_bytes':5_000_000,'oversized_policy':'scan in full','case_insensitive_families':list(KEYWORDS),'code_and_prose_separated':True},
 'summary':{'paths_considered':len(files),'eligible_scanned':len(inventories),'matching_files':len(matches),'matching_code_files':sum(x['class']=='code' for x in matches),'matching_prose_files':sum(x['class']=='prose' for x in matches),'archive_files':len(archive_files),'skipped_files':len(skipped),'oversized_scanned':len(oversized),'overclaim_candidate_lines':len(overclaims)},
 'lane_summary':lane_summary,
 'incomplete_lanes':[{'lane':k,'reason':v['incomplete_reason']} for k,v in lane_summary.items() if v['incomplete_lane']],
 'oversized_files':oversized,'archive_files':archive_files,'skipped_files':skipped,
 'overclaim_candidates':overclaims,
 'matching_code':[m for m in matches if m['class']=='code'],
 'matching_prose':[m for m in matches if m['class']=='prose'],
 'complete_scanned_inventory':inventories,
}
OUT.write_text(json.dumps(ledger,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(ledger['summary'],indent=2)); print(OUT)
