#!/usr/bin/env python3
"""
Clifford/galgebra sanity witness for the finite digest.

This is not the authoritative proof layer.  Lean/SymPy/Sage/GAP own the finite
algebraic checks; this script only confirms the same Clifford anticommutation
shape when galgebra is available.
"""

from __future__ import annotations


def main() -> None:
    try:
        from galgebra.ga import Ga
    except Exception as exc:  # pragma: no cover - environment dependent
        print(f"SKIP: galgebra unavailable ({exc})")
        return

    print("=== galgebra Clifford sanity witness ===")
    built = Ga.build("e f", g=[1, -1])
    ga = built[0]
    if len(built) == 2:
        e, f = built[1]
    else:
        e, f = built[1], built[2]
    assert (e * e).scalar() == 1
    assert (f * f).scalar() == -1
    assert e * f + f * e == 0
    print("PASS: galgebra e^2=1, f^2=-1, ef+fe=0")


if __name__ == "__main__":
    main()
