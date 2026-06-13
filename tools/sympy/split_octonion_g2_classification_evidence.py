#!/usr/bin/env python3
"""Computational evidence for the split-octonion/G2 classification lane.

This is NOT a proof of Aut(O_s)=G_{2(2)}.  It collects finite/computer-algebra
invariants that any future proof should connect:
  * Sage: octonion derivation algebra linear system has dimension 14;
  * Sage: G2 root system has 12 roots and Weyl group order 12;
  * GAP/Atlas: finite Chevalley/Atlas group G2(2) has order 12096;
  * clifford/galgebra: a 7D split-signature carrier has the expected signs.

Lean authority remains a conditional classification certificate, not this script.
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SAGE = Path("/home/goutev/miniforge3/envs/sage/bin/sage")
GAP = Path("/home/goutev/miniforge3/envs/sage/bin/gap")


def run_sage() -> dict[str, int | list[int]]:
    script = ROOT / ".tmp_split_octonion_g2_evidence.sage.py"
    script.write_text(
        r'''
from sage.all import *
from sage.algebras.octonion_algebra import OctonionAlgebra
import json

def derivation_dim(params):
    O=OctonionAlgebra(QQ,*params)
    basis=list(O.basis())
    n=len(basis)
    coords=[]
    for i in range(n):
        row=[]
        for j in range(n):
            v=O(basis[i]*basis[j]).vector()
            row.append([QQ(v[k]) for k in range(n)])
        coords.append(row)
    var_count=n*n
    equations=[]
    def idx(a,b): return a*n+b
    for i in range(n):
        for j in range(n):
            for k in range(n):
                coeff=[QQ(0)]*var_count
                for l in range(n): coeff[idx(k,l)] += coords[i][j][l]
                for a in range(n): coeff[idx(a,i)] -= coords[a][j][k]
                for b in range(n): coeff[idx(b,j)] -= coords[i][b][k]
                equations.append(coeff)
    M=Matrix(QQ,equations)
    return var_count - M.rank()

W=WeylGroup(['G',2])
R=RootSystem(['G',2])
result={
  'derivation_dims': [int(derivation_dim(p)) for p in [(1,1,1),(-1,-1,-1),(1,-1,1),(1,1,-1)]],
  'g2_roots': int(len(list(R.ambient_space().roots()))),
  'g2_weyl_order': int(W.order()),
  'g2_cartan_det': int(R.cartan_matrix().det()),
}
print(json.dumps(result, sort_keys=True))
'''
    )
    try:
        out = subprocess.check_output([str(SAGE), str(script)], text=True)
    finally:
        script.unlink(missing_ok=True)
    return json.loads(out.strip().splitlines()[-1])


def run_gap() -> dict[str, int | bool]:
    gap_script = r'''
LoadPackage("atlasrep");;
LoadPackage("ctbllib");;
G := AtlasGroup("G2(2)");;
D := AtlasGroup("G2(2)'");;
Print("G2_ORDER=", Size(G), "\n");
Print("G2_DERIVED_ORDER=", Size(D), "\n");
Print("G2_PERFECT=", IsPerfectGroup(G), "\n");
Print("G2_DERIVED_SIMPLE=", IsSimpleGroup(D), "\n");
QUIT;
'''
    out = subprocess.check_output([str(GAP), "-q"], input=gap_script, text=True)
    data: dict[str, int | bool] = {}
    for line in out.strip().splitlines():
        if line.startswith("G2_ORDER="):
            data["g2_2_order"] = int(line.split("=", 1)[1])
        elif line.startswith("G2_DERIVED_ORDER="):
            data["g2_2_derived_order"] = int(line.split("=", 1)[1])
        elif line.startswith("G2_PERFECT="):
            data["g2_2_perfect"] = line.split("=", 1)[1].strip() == "true"
        elif line.startswith("G2_DERIVED_SIMPLE="):
            data["g2_2_derived_simple"] = line.split("=", 1)[1].strip() == "true"
    return data


def verify_clifford_galgebra() -> dict[str, bool | int]:
    import clifford  # type: ignore
    from galgebra.ga import Ga  # type: ignore

    layout, blades = clifford.Cl(4, 3)
    e1 = blades["e1"]
    e5 = blades["e5"]
    cliff = {
        "cl43_dim": len(layout.blades),
        "cl43_e1_square_plus": int((e1 * e1)(0)) == 1,
        "cl43_e5_square_minus": int((e5 * e5)(0)) == -1,
    }
    ga = Ga("e1 e2 e3 e4 e5 e6 e7", g=[1,1,1,1,-1,-1,-1])
    basis = list(ga.mv_basis)
    galg = {
        "galgebra_e1_square_plus": str(basis[0] * basis[0]) == "1",
        "galgebra_e5_square_minus": str(basis[4] * basis[4]) == "-1",
    }
    return {**cliff, **galg}


def main() -> None:
    sage = run_sage()
    assert sage["derivation_dims"] == [14, 14, 14, 14]
    assert sage["g2_roots"] == 12
    assert sage["g2_weyl_order"] == 12
    assert sage["g2_cartan_det"] == 1

    gap = run_gap()
    assert gap["g2_2_order"] == 12096
    assert gap["g2_2_derived_order"] == 6048

    cg = verify_clifford_galgebra()
    assert cg["cl43_dim"] == 128
    assert cg["cl43_e1_square_plus"]
    assert cg["cl43_e5_square_minus"]
    assert cg["galgebra_e1_square_plus"]
    assert cg["galgebra_e5_square_minus"]

    print("SPLIT_OCTONION_G2_CLASSIFICATION_EVIDENCE_OK")
    print(json.dumps({"sage": sage, "gap": gap, "clifford_galgebra": cg}, sort_keys=True))
    print("scope: computational invariants/evidence only; full Aut(O_s)=G_{2(2)} requires Lean classification certificate")


if __name__ == "__main__":
    main()
