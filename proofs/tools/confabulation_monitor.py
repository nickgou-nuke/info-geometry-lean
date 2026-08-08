#!/usr/bin/env python3
"""
Confab/sanity audit for normalized Lean artifacts.

Scans target Lean files for:
  - exact sorry markers
  - trivial exact-rfl/by trivial proofs on nontrivial lemmas
  - symbols defined but unused/undocumented as deliverables
  - imports used but possibly missing basic mathlib prerequisites

This is a conservative, deterministic audit. It does not prove correctness;
it flags confab/vacuity contracts and missing author-side evidence.
"""

import argparse
import re, sys, os
from pathlib import Path

RE_SORRY = re.compile(r'\bsorry\b')
RE_TRIVIAL_PROOF = re.compile(r':=\s*(by\s*\nrfl|by\s*\nring|by\s*\ndecide)\b', )
RE_IMPORT = re.compile(r'import\s+([A-Za-z0-9_.]+)')
RE_THEOREM = re.compile(r'^(theorem|lemma|def)\s+([A-Za-z0-9_\']+)', )
RE_FINDTYPE = re.compile(r'(Fintype|Fin n|Finset)')
ANTI_CONFAB_VOCABULARY = (
 'theorem-honest',
 'theorem_honest',
 'theorem honest',
 'zero-sorry',
 'zero_sorry',
 'zero sorry',
 'zero-sorries',
 'zero_sorries',
 'zero sorries',
 'zero-axiom',
 'zero_axiom',
 'zero axiom',
 'zero-axioms',
 'zero_axioms',
 'zero axioms',
 'oops',
 'opaque',
)
RE_ANTI_CONFAB_VOCABULARY = re.compile(
 r'\b(' + '|'.join(re.escape(part) for part in ANTI_CONFAB_VOCABULARY) + r')\b',
 re.IGNORECASE,
)
def suspicious_symbol_name(sym):
 low = sym.lower()
 low = low.replace('boundary', '')
 return any(part in low for part in (
  'witness',
  'certificate',
  'sample',
  'bound',
  'socket',
  'ownerdebt',
  'debt',
  'generalized_sorry',
  'theorem_honest',
  'zerosorry',
  'zero_sorry',
  'zerosorries',
  'zero_sorries',
  'zeroaxiom',
  'zero_axiom',
  'zeroaxioms',
  'zero_axioms',
  'oops',
  'opaque',
 ))

REPO = Path('/home/goutev/auto')
DEFAULT_TARGETS = [
 REPO/'proofs'/'ThermodynamicTKKBridge.lean',
 REPO/'proofs'/'VacuumTopology.lean',
 REPO/'proofs'/'VacuumCohomology.lean',
 Path('/home/goutev/auto/proofs/BregmanQKernel.lean'),
 Path('/home/goutev/auto/proofs/FrameJacobiPauliCluster.lean'),
]

parser = argparse.ArgumentParser(description="Conservative Lean confabulation audit.")
parser.add_argument("files", nargs="*", help="Lean files to audit. Defaults to the historical target list.")
args = parser.parse_args()

targets = [Path(p) for p in args.files] if args.files else DEFAULT_TARGETS

report = []
for path in targets:
 if not path.exists():
  report.append({
   'path': str(path),
   'symbol_count': 0,
   'import_count': 0,
   'sorry_count': 0,
   'trivial_count': 0,
   'unused_symbols': [],
   'flag_excerpt': 'MISSING_FILE',
  })
  continue
 src = path.read_text()
 lines = src.splitlines()
 symbols = []
 unused_symbols = []
 imports = []
 trivials = []
 sorrys = []
 suspicious_symbols = []
 vocab_hits = []
 for i,l in enumerate(lines, start=1):
  m = RE_SORRY.search(l)
  if m:
   sorrys.append((i,l.strip()))
  m = RE_TRIVIAL_PROOF.search(l)
  if m:
   trivials.append((i,l.strip()))
  m = RE_THEOREM.match(l)
  if m:
   sym = m.group(2)
   if sym in symbols:
    continue
   if suspicious_symbol_name(sym):
    suspicious_symbols.append((i, sym))
   used = sum(1 for ll in lines if sym in ll)
   if used <= 2:
    unused_symbols.append(sym)
   symbols.append(sym)
  if l.startswith('import '):
   imports.append(l.strip())
  if RE_ANTI_CONFAB_VOCABULARY.search(l):
   vocab_hits.append((i, l.strip()))

 flag_excerpt = '\n'.join(l for _,l in (trivials+sorrys)[:10])
 if suspicious_symbols:
  suspicious_excerpt = '\n'.join(f"{i}:{sym}" for i, sym in suspicious_symbols[:10])
  flag_excerpt = (flag_excerpt + '\n' + suspicious_excerpt).strip()
 if vocab_hits:
  vocab_excerpt = '\n'.join(f"{i}:{line}" for i, line in vocab_hits[:10])
  flag_excerpt = (flag_excerpt + '\n' + vocab_excerpt).strip()
 report.append({
  'path': str(path),
  'symbol_count': len(symbols),
  'import_count': len(imports),
  'sorry_count': len(sorrys),
  'trivial_count': len(trivials),
  'unused_symbols': unused_symbols[:8],
  'flag_excerpt': flag_excerpt,
 })

print('AUDIT_CONFAB_V1')
for r in report:
 p=r['path']
 print(f"PATH {p}")
 print(f"THEOREMS_OR_DEFS={r['symbol_count']}")
 print(f"IMPORTS={r['import_count']}")
 print(f"SORRY={r['sorry_count']}")
 print(f"TRIVIAL_PROOFS={r['trivial_count']}")
 print(f"UNUSED_OR_UNDOCUMENTED_SYMBOLS={r['unused_symbols']}")
 print(f"FLAG_EXCERPT={r['flag_excerpt']}")
 print('END')
