#!/usr/bin/env python3
from __future__ import annotations

import sympy as sp


def vector_field(A, B, C, z):
    return -C * z**2 + 2 * A * z + B


def discriminant(A, B, C):
    return sp.expand((2 * A) ** 2 - 4 * (-C) * B)


def trace_zero_matrix(A, B, C):
    return sp.Matrix([[A, B], [C, -A]])


def verify_symbolic_identity():
    A, B, C = sp.symbols("A B C")
    M = trace_zero_matrix(A, B, C)
    delta = discriminant(A, B, C)
    det_term = sp.expand(-4 * M.det())
    assert sp.expand(delta - det_term) == 0
    return sp.simplify(delta), sp.simplify(M.det())


def verify_packets():
    z = sp.symbols("z")
    packets = {
        "parabolic": (1, 1, -1),
        "hyperbolic": (1, 0, -1),
        "elliptic": (0, 1, -1),
        "loxodromic": (1, 1, sp.I),
    }
    reports = {}
    for name, (A, B, C) in packets.items():
        M = trace_zero_matrix(A, B, C)
        vf = sp.expand(vector_field(A, B, C, z))
        delta = sp.expand(discriminant(A, B, C))
        roots = sp.solve(sp.Eq(vf, 0), z)
        reports[name] = {
            "matrix": M.tolist(),
            "determinant": sp.expand(M.det()),
            "vector_field": vf,
            "discriminant": delta,
            "roots": roots,
        }

    assert reports["parabolic"]["discriminant"] == 0
    assert reports["hyperbolic"]["discriminant"] == 4
    assert reports["elliptic"]["discriminant"] == -4
    assert sp.im(reports["loxodromic"]["discriminant"]) != 0
    return reports


def main():
    delta, detM = verify_symbolic_identity()
    reports = verify_packets()
    print("symbolic_discriminant =", delta)
    print("symbolic_det =", detM)
    for name, report in reports.items():
        print(f"[{name}]")
        print("  determinant =", report["determinant"])
        print("  vector_field =", report["vector_field"])
        print("  discriminant =", report["discriminant"])
        print("  roots =", report["roots"])
    print("MOBIUS_INFINITESIMAL_SYMPY_OK")


if __name__ == "__main__":
    main()
