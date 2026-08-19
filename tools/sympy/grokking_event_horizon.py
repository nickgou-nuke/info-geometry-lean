#!/usr/bin/env python3
"""SymPy twin for the EP/KAN shared square-zero interface.

The script checks that the finite Jordan exceptional-point nilpotent and the
finite KAN-wallpaper translation generator are both square-zero.  It does not
identify their carriers or prove a physical/cognitive equivalence theorem.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    print("--- SymPy Twin: EP/KAN Shared Square-Zero Interface ---")

    N_ep = sp.Matrix([[0, 1], [0, 0]])
    T_x = sp.Matrix([[1, 0, 1], [0, 1, 0], [0, 0, 1]])
    I3 = sp.eye(3)
    N_kan = T_x - I3

    assert N_ep * N_ep == sp.zeros(2, 2)
    assert N_ep != sp.zeros(2, 2)
    print("EP Jordan nilpotent: N^2 = 0 and N != 0: OK")

    assert N_kan * N_kan == sp.zeros(3, 3)
    assert N_kan != sp.zeros(3, 3)
    print("KAN-wallpaper translation generator: n^2 = 0 and n != 0: OK")

    print("[SUCCESS] EP and KAN finite checks share the square-zero interface.")


if __name__ == "__main__":
    main()
