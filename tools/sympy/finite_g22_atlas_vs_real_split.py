#!/usr/bin/env python3
"""Separate finite Atlas `G2(2)` facts from real split-octonion `Aut(O_s)` facts.

This script is deliberately a boundary/audit tool.  It verifies finite-group
statements with GAP/AtlasRep/CTblLib and Sage, while explicitly refusing to turn
those finite Chevalley facts into the real Lie-group classification
`Aut(O_s) = G_{2(2)}`.

Verified finite facts here:
  * Atlas/CTblLib identifies `G2(2)` with character table `U3(3).2` of order 12096.
  * `G2(2)'` has character table `U3(3)` of order 6048.
  * A concrete Atlas permutation group `U3(3).2` has automorphism group order 12096.
  * A concrete `PSU(3,3)` has automorphism group order 12096.
  * `PGL(3,3)` has order 5616, so `PΓL(3,3)=PGL(3,3)` in characteristic 3
    is not the order-12096 group.

Real split-octonion classification status is separate: it is supported by the
rank-14 derivation computation in `split_octonion_derivation_classification.py`,
but not fully closed in Lean as a global automorphism/Lie-group theorem.
"""

from __future__ import annotations

from pathlib import Path
import subprocess

GAP = Path("/home/goutev/miniforge3/envs/sage/bin/gap")
SAGE = Path("/home/goutev/miniforge3/envs/sage/bin/sage")


def run_gap() -> str:
    if not GAP.exists():
        return "GAP_SKIPPED missing"
    code = r'''
LoadPackage("atlasrep", false);;
LoadPackage("ctbllib", false);;
for name in ["G2(2)", "G2(2)'", "U3(3)", "U3(3).2", "L3(3)"] do
  ct := CharacterTable(name);
  if ct = fail then
    Print("GAP_TABLE ", name, " fail\n");
  else
    Print("GAP_TABLE ", name, " order ", Size(ct), " identifier ", Identifier(ct), "\n");
  fi;
od;
A := AtlasGroup("U3(3).2");;
Print("GAP_ATLAS_U3_3_DOT_2_ORDER ", Size(A), "\n");
Print("GAP_ATLAS_U3_3_DOT_2_DEGREE ", LargestMovedPoint(A), "\n");
Print("GAP_AUT_ATLAS_U3_3_DOT_2_ORDER ", Size(AutomorphismGroup(A)), "\n");
S := PSU(3,3);;
Print("GAP_PSU_3_3_ORDER ", Size(S), "\n");
Print("GAP_AUT_PSU_3_3_ORDER ", Size(AutomorphismGroup(S)), "\n");
P := PGL(3,3);;
Print("GAP_PGL_3_3_ORDER ", Size(P), "\n");
QUIT;
'''
    proc = subprocess.run([str(GAP), "-q"], input=code, text=True, capture_output=True, timeout=300)
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr or proc.stdout)
    return proc.stdout.strip()


def run_sage() -> str:
    if not SAGE.exists():
        return "SAGE_SKIPPED missing"
    code = r'''
from sage.all import *
q = 3
# |PGL_3(q)| = |GL_3(q)| / (q-1); F_3 has no nontrivial field automorphism,
# hence PΓL_3(3)=PGL_3(3).
gl = prod(q**3 - q**i for i in range(3))
pgl = gl // (q - 1)
print("SAGE_GL_3_3_ORDER", gl)
print("SAGE_PGL_3_3_ORDER", pgl)
print("SAGE_PGAMMAL_3_3_ORDER", pgl)
R = RootSystem(['G',2])
print("SAGE_G2_RANK", len(R.index_set()))
print("SAGE_G2_POSITIVE_ROOTS", len(list(R.root_poset())))
from sage.algebras.lie_algebras.classical_lie_algebra import LieAlgebraChevalleyBasis
g = LieAlgebraChevalleyBasis(QQ, ['G',2])
print("SAGE_G2_LIE_DIM", g.dimension())
'''
    proc = subprocess.run([str(SAGE), "-c", code], text=True, capture_output=True, timeout=300)
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr or proc.stdout)
    return proc.stdout.strip()


def main() -> None:
    gap_out = run_gap()
    sage_out = run_sage()
    print(gap_out)
    print(sage_out)
    assert "GAP_TABLE G2(2) order 12096 identifier U3(3).2" in gap_out
    assert "GAP_TABLE G2(2)' order 6048 identifier U3(3)" in gap_out
    assert "GAP_AUT_ATLAS_U3_3_DOT_2_ORDER 12096" in gap_out
    assert "GAP_AUT_PSU_3_3_ORDER 12096" in gap_out
    assert "GAP_PGL_3_3_ORDER 5616" in gap_out
    assert "SAGE_PGAMMAL_3_3_ORDER 5616" in sage_out
    assert "SAGE_G2_LIE_DIM 14" in sage_out
    print("BOUNDARY finite Atlas G2(2)=U3(3).2 order 12096; PΓL3(3) order 5616; real Aut(O_s)=G_{2(2)} is a separate Lie-group theorem")


if __name__ == "__main__":
    main()
