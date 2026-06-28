#!/usr/bin/env sage -python
from sage.all import QQ, CC, Infinity, Matrix, PolynomialRing, I
import json
import sys


def mobius_matrix(a, b, c, d, ring=None):
    if ring is None:
        ring = QQ
    M = Matrix(ring, [[a, b], [c, d]])
    assert abs(complex(M.det()) - 1) < 1e-10
    return M


def mobius_action(M, z):
    a, b, c, d = M[0, 0], M[0, 1], M[1, 0], M[1, 1]
    if z == Infinity:
        return Infinity if c == 0 else a / c
    denom = c * z + d
    if denom == 0:
        return Infinity
    return (a * z + b) / denom


def fixed_polynomial(M):
    R = PolynomialRing(M.base_ring(), 'z')
    z = R.gen()
    a, b, c, d = M[0, 0], M[0, 1], M[1, 0], M[1, 1]
    return c * z**2 + (d - a) * z - b


def multiplier_at_fixed_point(M, fp):
    a, _, c, d = M[0, 0], M[0, 1], M[1, 0], M[1, 1]
    if fp == Infinity:
        return 1 / (a**2)
    return 1 / ((c * fp + d) ** 2)


def sigma_value(M):
    return (M.trace() ** 2) / M.det()


def classify_sigma(sigma):
    if abs(complex(sigma) - 4) < 1e-10:
        return "parabolic"
    if abs(complex(sigma).imag) > 1e-10:
        return "loxodromic"
    if complex(sigma).real < 4:
        return "elliptic"
    return "hyperbolic"


def packet(name):
    if name == "hyperbolic":
        return mobius_matrix(2, 0, 0, QQ(1) / 2), [0, Infinity]
    if name == "parabolic":
        return mobius_matrix(1, 1, 0, 1), [Infinity]
    if name == "elliptic":
        return mobius_matrix(0, -1, 1, 0), None
    if name == "loxodromic":
        return mobius_matrix(CC(1 + I), CC(1), CC(I), CC(1), ring=CC), None
    raise ValueError(f"unknown packet: {name}")


def main(name):
    M, fixed_points_hint = packet(name)
    sigma = sigma_value(M)
    classification = classify_sigma(sigma)
    assert classification == name

    fp = fixed_polynomial(M)
    eigenvalues = sorted(str(v) for v in M.eigenvalues())
    report = {
        "classification": classification,
        "matrix": [[str(M[i, j]) for j in range(2)] for i in range(2)],
        "trace": str(M.trace()),
        "determinant": str(M.det()),
        "sigma": str(sigma),
        "fixed_polynomial": str(fp),
        "eigenvalues": eigenvalues,
    }

    if fixed_points_hint is not None:
        report["fixed_points"] = [str(x) for x in fixed_points_hint]

    if name == "hyperbolic":
        mul_zero = multiplier_at_fixed_point(M, 0)
        mul_inf = multiplier_at_fixed_point(M, Infinity)
        orbit = [1]
        value = 1
        for _ in range(4):
            value = mobius_action(M, value)
            orbit.append(value)
        assert orbit == [1, 4, 16, 64, 256]
        report["multiplier_at_zero"] = str(mul_zero)
        report["multiplier_at_infinity"] = str(mul_inf)
        report["forward_orbit_from_1"] = [str(x) for x in orbit]

    print(json.dumps(report, indent=2, sort_keys=True))
    print("MOBIUS_SAGE_OK")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: sage tools/sage/mobius_sage.py <hyperbolic|parabolic|elliptic|loxodromic>")
        sys.exit(1)
    main(sys.argv[1])
