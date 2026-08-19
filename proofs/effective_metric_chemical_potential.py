#!/usr/bin/env python3
"""Symbolic witness for the chemical-potential metric shadow.

Finite statement mirrored in `ChemicalPotentialMetricBridge.lean`:

    E -> E - dmu
    det(P_mu sigma^mu) shifts by dmu^2 - 2*E*dmu.

The continuum Tolman/Ehrenfest and Einstein-equation readings remain deferred_interfaces.
"""

import sympy as sp


def main() -> None:
    E, px, py, pz, dmu = sp.symbols("E px py pz dmu")

    X = sp.Matrix(
        [
            [E + pz, px - sp.I * py],
            [px + sp.I * py, E - pz],
        ]
    )
    X_shift = sp.Matrix(
        [
            [E - dmu + pz, px - sp.I * py],
            [px + sp.I * py, E - dmu - pz],
        ]
    )

    q = sp.expand(X.det())
    q_shift = sp.expand(X_shift.det())
    deformation = sp.simplify(q_shift - q)
    expected = sp.expand(dmu**2 - 2 * E * dmu)

    assert sp.simplify(q - (E**2 - px**2 - py**2 - pz**2)) == 0
    assert sp.simplify(deformation - expected) == 0

    time_scale = 1 - dmu
    g00 = sp.expand(time_scale**2)
    assert sp.simplify(g00 - (1 - dmu) ** 2) == 0

    E00 = sp.Matrix([[1, 0], [0, 0]])
    assert E00.det() == 0
    assert E00**3 == E00

    print("det Pauli frame:", q)
    print("shifted determinant:", q_shift)
    print("chemical-potential deformation:", deformation)
    print("expected deformation:", expected)
    print("local g00 shadow:", g00)
    print("E00 det:", E00.det(), "E00^3=E00:", E00**3 == E00)
    print("effective_metric_chemical_potential.py: finite audit passed")


if __name__ == "__main__":
    main()
