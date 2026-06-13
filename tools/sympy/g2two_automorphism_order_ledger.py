#!/usr/bin/env python3
"""Finite `G2(2)` automorphism-order ledger.

This script verifies the order ledger that protects against the common
misidentification

    Aut(G2(2)) ≅ PΓL_3(3).

Exact boundary:
  * This is a finite Atlas/Chevalley group check, not the real split-octonion
    Lie-group theorem `Aut(O_s)=G_{2(2)}`.
  * GAP/Atlas identifies finite `G2(2)` with `U3(3).2` of order 12096.
  * GAP identifies `G2(2)'` with `U3(3)` of order 6048.
  * The true order-compatible extension is the unitary lane `Aut(PSU_3(3))`,
    whose GAP order is 12096.
  * Over the prime field F_3, PΓL_3(3)=PGL_3(3)=PSL_3(3), whose order is 5616.

The companion Lean file records only exact natural-number equalities and
inequalities; it does not claim group isomorphisms from arithmetic alone.
"""

from __future__ import annotations

from pathlib import Path
import subprocess

import sympy as sp

GAP = Path("/home/goutev/miniforge3/envs/sage/bin/gap")


def pgl_order(q: int, n: int) -> int:
    gl = sp.prod(q**n - q**i for i in range(n))
    return int(gl // (q - 1))


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
A := AtlasGroup("G2(2)");;
Print("GAP_ATLAS_G2_2_ORDER ", Size(A), "\n");
Print("GAP_ATLAS_G2_2_DEGREE ", LargestMovedPoint(A), "\n");
Print("GAP_ATLAS_G2_2_CENTER_ORDER ", Size(Center(A)), "\n");
Print("GAP_AUT_ATLAS_G2_2_ORDER ", Size(AutomorphismGroup(A)), "\n");
S := PSU(3,3);;
Print("GAP_PSU_3_3_ORDER ", Size(S), "\n");
Print("GAP_AUT_PSU_3_3_ORDER ", Size(AutomorphismGroup(S)), "\n");
L := PSL(3,3);;
Print("GAP_PSL_3_3_ORDER ", Size(L), "\n");
P := PGL(3,3);;
Print("GAP_PGL_3_3_ORDER ", Size(P), "\n");
QUIT;
'''
    proc = subprocess.run([str(GAP), "-q"], input=code, text=True, capture_output=True, timeout=300)
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr or proc.stdout)
    return proc.stdout.strip()


def main() -> None:
    g2_two_order = 12096
    g2_two_derived_order = 6048
    psu3_3_order = g2_two_derived_order
    pgamma_u3_3_order = psu3_3_order * 2
    gl3_f3_order = int(sp.prod(3**3 - 3**i for i in range(3)))
    pgl3_f3_order = pgl_order(3, 3)
    psl3_f3_order = pgl3_f3_order  # gcd(3, 3-1)=1, so PSL_3(3)=PGL_3(3) by order.
    p_gamma_l3_f3_order = pgl3_f3_order  # F_3 has no nontrivial field automorphism.

    assert g2_two_derived_order * 2 == g2_two_order
    assert psu3_3_order == 6048
    assert pgamma_u3_3_order == 12096
    assert pgamma_u3_3_order == g2_two_order
    assert gl3_f3_order == 11232
    assert pgl3_f3_order == 5616
    assert psl3_f3_order == 5616
    assert p_gamma_l3_f3_order == 5616
    assert p_gamma_l3_f3_order != g2_two_order

    print("SYMPY_G2_TWO_ORDER", g2_two_order)
    print("SYMPY_G2_TWO_DERIVED_ORDER", g2_two_derived_order)
    print("SYMPY_G2_TWO_DERIVED_INDEX_TWO", g2_two_derived_order * 2 == g2_two_order)
    print("SYMPY_PSU_3_3_ORDER", psu3_3_order)
    print("SYMPY_PGAMMAU_3_3_ORDER", pgamma_u3_3_order)
    print("SYMPY_PGAMMAU_3_3_EQ_G2_2", pgamma_u3_3_order == g2_two_order)
    print("SYMPY_GL_3_3_ORDER", gl3_f3_order)
    print("SYMPY_PSL_3_3_ORDER", psl3_f3_order)
    print("SYMPY_PGL_3_3_ORDER", pgl3_f3_order)
    print("SYMPY_PGAMMAL_3_3_ORDER", p_gamma_l3_f3_order)
    print("SYMPY_PGAMMAL_3_3_NE_G2_2", p_gamma_l3_f3_order != g2_two_order)

    gap_out = run_gap()
    print(gap_out)
    assert "GAP_TABLE G2(2) order 12096 identifier U3(3).2" in gap_out
    assert "GAP_TABLE G2(2)' order 6048 identifier U3(3)" in gap_out
    assert "GAP_ATLAS_G2_2_ORDER 12096" in gap_out
    assert "GAP_ATLAS_G2_2_CENTER_ORDER 1" in gap_out
    assert "GAP_AUT_ATLAS_G2_2_ORDER 12096" in gap_out
    assert "GAP_PSU_3_3_ORDER 6048" in gap_out
    assert "GAP_AUT_PSU_3_3_ORDER 12096" in gap_out
    assert "GAP_PSL_3_3_ORDER 5616" in gap_out
    assert "GAP_PGL_3_3_ORDER 5616" in gap_out

    print("BOUNDARY finite G2(2)=U3(3).2 order 12096; G2(2)'=U3(3) order 6048; true unitary extension Aut(PSU3(3)) order 12096; false linear lane PΓL3(3)=PGL3(3)=PSL3(3) order 5616")


if __name__ == "__main__":
    main()
