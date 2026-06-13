#!/usr/bin/env python3
"""GAP-backed finite order ledger for G2(2) automorphism claims.

Repairs the common misstatement `Aut(G2(2)) ≅ PΣL_3(3)` with order 12096.
Over F_3 the field automorphism group is trivial and |PGL_3(3)|=|PSL_3(3)|=5616,
so it cannot be the 12096 group.

GAP/Atlas confirms:
  |G2(2)| = 12096,
  |G2(2)'| = 6048,
  [G2(2):G2(2)'] = 2,
  |Aut(G2(2))| = 12096,
  Out(G2(2)) has order 1 in the Atlas model.
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

GAP = Path("/home/goutev/miniforge3/envs/sage/bin/gap")


def run_gap() -> dict[str, int | bool]:
    script = r'''
LoadPackage("atlasrep");;
LoadPackage("ctbllib");;
G := AtlasGroup("G2(2)");;
D := DerivedSubgroup(G);;
A := AutomorphismGroup(G);;
F := GF(3);;
Glin := GeneralLinearGroup(3,F);;
Slin := SpecialLinearGroup(3,F);;
Print("G2_ORDER=", Size(G), "\n");
Print("G2_DERIVED_ORDER=", Size(D), "\n");
Print("G2_DERIVED_INDEX=", Index(G,D), "\n");
Print("G2_PERFECT=", IsPerfectGroup(G), "\n");
Print("G2_DERIVED_SIMPLE=", IsSimpleGroup(D), "\n");
Print("AUT_G2_ORDER=", Size(A), "\n");
Print("OUT_G2_ORDER=", Size(A)/Size(InnerAutomorphismsAutomorphismGroup(A)), "\n");
Print("PGL3_3_ORDER=", Size(Glin)/(Size(F)-1), "\n");
Print("PSL3_3_ORDER=", Size(Slin)/Gcd(3,Size(F)-1), "\n");
QUIT;
'''
    out = subprocess.check_output([str(GAP), "-q"], input=script, text=True)
    data: dict[str, int | bool] = {}
    for line in out.splitlines():
        if "=" not in line:
            continue
        key, val = line.strip().split("=", 1)
        if val in {"true", "false"}:
            data[key.lower()] = val == "true"
        else:
            data[key.lower()] = int(val)
    return data


def main() -> None:
    d = run_gap()
    assert d["g2_order"] == 12096
    assert d["g2_derived_order"] == 6048
    assert d["g2_derived_index"] == 2
    assert d["g2_perfect"] is False
    assert d["g2_derived_simple"] is True
    assert d["aut_g2_order"] == 12096
    assert d["out_g2_order"] == 1
    assert d["pgl3_3_order"] == 5616
    assert d["psl3_3_order"] == 5616
    assert d["pgl3_3_order"] != d["g2_order"]

    print("G2TWO_AUTOMORPHISM_ORDER_LEDGER_OK")
    print(json.dumps(d, sort_keys=True))
    print("scope: finite GAP/Atlas order ledger; no Lean group isomorphism constructed")


if __name__ == "__main__":
    main()
