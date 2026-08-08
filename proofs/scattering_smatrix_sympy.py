#!/usr/bin/env python3
"""SymPy witness for braid-word scattering S-matrices.

Checks both conventions:
- parity gate P = sigma3*iSigma2 = sigma_x with P^3=P;
- phase gate G = iP with G^2=-I and G^3=-G.

The scattering matrix is an ordered product of local gates along a braid word.
For the current uniform local representation, Artin-equivalent words give the
same S-matrix.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(name: str, matrix: sp.Matrix) -> None:
    residue = matrix.applyfunc(lambda x: sp.simplify(sp.expand_func(x).rewrite(sp.exp)))
    if residue != sp.zeros(*residue.shape):
        print(f"{name}: FAIL")
        print(residue)
        raise SystemExit(1)
    print(f"{name}: PASS")


def scattering(word: list[int], gate: sp.Matrix) -> sp.Matrix:
    out = sp.eye(gate.rows)
    for _ in word:
        out = gate * out
    return sp.simplify(out)


def main() -> int:
    sigma3 = sp.Matrix([[1, 0], [0, -1]])
    i_sigma2 = sp.Matrix([[0, 1], [-1, 0]])
    parity_gate = sigma3 * i_sigma2
    phase_gate = sp.I * parity_gate

    assert_zero("parity gate P^3=P", parity_gate**3 - parity_gate)
    assert_zero("phase gate G^2=-I", phase_gate**2 + sp.eye(2))
    assert_zero("phase gate G^3=-G", phase_gate**3 + phase_gate)

    left_adjacent = [0, 1, 0]
    right_adjacent = [1, 0, 1]
    left_separated = [0, 2]
    right_separated = [2, 0]

    assert_zero(
        "S parity adjacent Artin",
        scattering(left_adjacent, parity_gate) - scattering(right_adjacent, parity_gate),
    )
    assert_zero(
        "S parity separated Artin",
        scattering(left_separated, parity_gate) - scattering(right_separated, parity_gate),
    )
    assert_zero(
        "S phase adjacent Artin",
        scattering(left_adjacent, phase_gate) - scattering(right_adjacent, phase_gate),
    )
    assert_zero(
        "S phase separated Artin",
        scattering(left_separated, phase_gate) - scattering(right_separated, phase_gate),
    )

    print("OK scattering S-matrix SymPy witness completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
