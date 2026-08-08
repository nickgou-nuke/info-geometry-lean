#!/usr/bin/env python3
"""
Remediation patcher for Lean artifacts.
Applies small textual fixes to reduce confabulation markers when lake build fails.
"""

import sys
from pathlib import Path

REPO = Path('/home/goutev/auto')
TARGETS = [
 Path('/home/goutev/auto/proofs/ThermodynamicTKKBridge.lean'),
 Path('/home/goutev/auto/proofs/VacuumTopology.lean'),
 Path('/home/goutev/auto/proofs/VacuumCohomology.lean'),
 Path('/home/goutev/auto/proofs/BregmanQKernel.lean'),
 Path('/home/goutev/auto/proofs/FrameJacobiPauliCluster.lean'),
]

def text_replace(path: Path, old: str, new: str) -> bool:
 txt = path.read_text()
 if old not in txt:
  return False
 path.write_text(txt.replace(old, new))
 return True

# Typical confab fix: trivial trivial proofs should be labeled, or add 'sorry' only when explicitly allowed.
fixes = {
 'theorem empty_trivial': 'theorem empty_trivial -- to be proved or moved to lemma',
}

for p in TARGETS:
 if not p.exists():
  continue
 for old,new in fixes.items():
  if text_replace(p, old, new):
   print(f'PATCHED {p}: {old} -> {new}')
   break

print('REMEDIATION_DONE')
