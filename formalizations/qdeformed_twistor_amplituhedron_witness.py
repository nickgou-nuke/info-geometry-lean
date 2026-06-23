#!/usr/bin/env python3
"""Finite witness for the q-deformed twistor/amplituhedron bridge.

This mirrors `QDeformedTwistorAmplituhedronBridge.lean`.

It checks only finite algebra:

* the Kuzmin open window is `abs(q) < 1`;
* `q=0` is interior, while `q=-1` and `q=1` are boundary endpoints;
* the k=2,n=2 q-Gram matrix is positive at a sample interior value;
* the q-CCR relation reduces to Toeplitz, CAR, and CCR endpoint readouts.

It is not a C*-classification proof and it is not an amplituhedron-invariance
or scattering-amplitude theorem.
"""

from __future__ import annotations

import json

import sympy as sp


def gram_matrix_k2_n2(q_value: sp.Expr) -> sp.Matrix:
    return sp.Matrix(
        [
            [1, 0, 0, q_value],
            [0, 1, q_value, 0],
            [0, q_value, 1, 0],
            [q_value, 0, 0, 1],
        ]
    )


def verify_open_window() -> dict[str, bool]:
    return {
        "zero_inside": bool(abs(sp.Rational(0)) < 1),
        "minus_one_outside": bool(not (abs(sp.Rational(-1)) < 1)),
        "one_outside": bool(not (abs(sp.Rational(1)) < 1)),
    }


def verify_q_gram() -> dict[str, object]:
    q = sp.Rational(1, 2)
    gram = gram_matrix_k2_n2(q)
    eigenvals = sorted(gram.eigenvals().keys())
    return {
        "q": str(q),
        "symmetric": bool(gram == gram.T),
        "positive_eigenvalues": bool(all(ev > 0 for ev in eigenvals)),
        "eigenvalues": [str(ev) for ev in eigenvals],
    }


def verify_qccr_endpoints() -> dict[str, bool]:
    delta, aadag = sp.symbols("delta aadag")

    def astar_a(q_value: int) -> sp.Expr:
        return delta + q_value * aadag

    toeplitz = sp.simplify(astar_a(0) - delta)
    car = sp.simplify(astar_a(-1) + aadag - delta)
    ccr = sp.simplify(astar_a(1) - aadag - delta)
    return {
        "toeplitz_q0": bool(toeplitz == 0),
        "car_q_minus_one": bool(car == 0),
        "ccr_q_one": bool(ccr == 0),
    }


def main() -> None:
    checks = {
        "open_window": verify_open_window(),
        "q_gram": verify_q_gram(),
        "qccr_endpoints": verify_qccr_endpoints(),
        "non_claims": [
            "no C-star classification theorem asserted",
            "no q-deformed amplituhedron invariance theorem asserted",
            "no q-deformed BCFW or scattering-amplitude theorem asserted",
        ],
    }

    assert all(checks["open_window"].values())
    assert checks["q_gram"]["symmetric"]
    assert checks["q_gram"]["positive_eigenvalues"]
    assert all(checks["qccr_endpoints"].values())

    print("QDEFORMED_TWISTOR_AMPLITUHEDRON_WITNESS_OK")
    print(json.dumps(checks, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
