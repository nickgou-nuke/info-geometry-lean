#!/usr/bin/env python3
from __future__ import annotations

import json
import sys
from dataclasses import dataclass

import sympy as sp

z = sp.symbols("z")


@dataclass(frozen=True)
class MobiusReport:
    matrix: list[list[str]]
    trace: str
    determinant: str
    sigma: str
    classification: str
    fixed_polynomial: str
    fixed_points: list[str]
    eigenvalues: list[str]
    projective_eigendirections: list[str]
    multiplier_at_zero: str | None = None
    multiplier_at_infinity: str | None = None
    attracting_fixed_point: str | None = None
    pairing_invariant: bool = True
    quaternion_norm_symbolic: str | None = None
    forward_orbit_from_1: list[str] | None = None


def contragredient(M: sp.Matrix) -> sp.Matrix:
    a, b, c, d = M[0, 0], M[0, 1], M[1, 0], M[1, 1]
    return sp.Matrix([[d, -b], [-c, a]])


def mobius_action(M: sp.Matrix, value):
    a, b, c, d = M[0, 0], M[0, 1], M[1, 0], M[1, 1]
    if value == sp.oo:
        return sp.oo if c == 0 else sp.simplify(a / c)
    denom = sp.simplify(c * value + d)
    if denom == 0:
        return sp.oo
    return sp.simplify((a * value + b) / denom)


def mobius_fixed_polynomial(M: sp.Matrix, variable: sp.Symbol = z):
    a, b, c, d = M[0, 0], M[0, 1], M[1, 0], M[1, 1]
    return sp.expand(c * variable**2 + (d - a) * variable - b)


def projective_ratio(v: sp.Matrix):
    if sp.simplify(v[1, 0]) == 0:
        return sp.oo
    return sp.simplify(v[0, 0] / v[1, 0])


def multiplier_at_fixed_point(M: sp.Matrix, fixed_point):
    a, _, c, d = M[0, 0], M[0, 1], M[1, 0], M[1, 1]
    if fixed_point == sp.oo:
        return sp.simplify(1 / a**2)
    return sp.simplify(1 / (c * fixed_point + d) ** 2)


def classify_stability(multiplier):
    value = sp.N(multiplier)
    return "attracting" if abs(complex(value)) < 1 else "repelling"


def classify_mobius(M: sp.Matrix) -> str:
    """Classify by trace squared over determinant: sigma = (tr)^2 / det"""
    tr = M.trace()
    det = M.det()
    sigma = sp.simplify(tr**2 / det)
    if sigma == 4:
        return "parabolic"
    if sigma.is_real:
        if sigma < 4:
            return "elliptic"
        return "hyperbolic"
    return "loxodromic"


def verify_packet(M: sp.Matrix, expected_class: str | None = None) -> MobiusReport:
    assert sp.simplify(M.det() - 1) == 0

    tr = sp.simplify(M.trace())
    det = sp.simplify(M.det())
    sigma = sp.simplify(tr**2 / det)
    classification = classify_mobius(M)

    if expected_class:
        assert classification == expected_class, f"Expected {expected_class}, got {classification}"

    fp = sp.factor(mobius_fixed_polynomial(M))
    eigvects = M.eigenvects()
    eigenvalues = [sp.simplify(ev) for ev, _, _ in eigvects]

    directions = []
    for ev, mult, basis in eigvects:
        for v in basis:
            directions.append(str(projective_ratio(v)))
    directions = sorted(set(directions))

    # Fixed points of Möbius action: solve c*z^2 + (d-a)*z - b = 0
    # Include infinity when c == 0 (parabolic/hyperbolic with c=0)
    a, b, c, d = M[0, 0], M[0, 1], M[1, 0], M[1, 1]
    fixed_points = [str(sp.nsimplify(r)) for r in sp.solve(mobius_fixed_polynomial(M), z)]
    if c == 0:
        fixed_points.append("oo")

    mul_zero = None
    mul_inf = None
    attracting = None
    orbit = None

    if "0" in fixed_points:
        mul_zero = multiplier_at_fixed_point(M, sp.Integer(0))
    if "oo" in fixed_points:
        mul_inf = multiplier_at_fixed_point(M, sp.oo)
        if mul_inf is not None:
            attracting = "infinity" if classify_stability(mul_inf) == "attracting" else "zero"
    elif "0" in fixed_points and mul_zero is not None:
        attracting = "zero" if classify_stability(mul_zero) == "attracting" else "infinity"

    if classification == "hyperbolic":
        orbit = [sp.Integer(1)]
        current = sp.Integer(1)
        for _ in range(4):
            current = mobius_action(M, current)
            orbit.append(current)

    eta1, eta2, th1, th2 = sp.symbols("eta1 eta2 th1 th2")
    eta = sp.Matrix([[eta1], [eta2]])
    theta = sp.Matrix([[th1], [th2]])
    lhs = sp.simplify((contragredient(M).T * eta).dot(M * theta))
    rhs = sp.simplify(eta.dot(theta))
    pairing = sp.simplify(lhs - rhs) == 0

    w, x, y, qz = sp.symbols("w x y qz")
    H = sp.Matrix(
        [[w + x * sp.I, y + qz * sp.I], [-y + qz * sp.I, w - x * sp.I]]
    )
    quaternion_norm = sp.expand(H.det())

    return MobiusReport(
        matrix=[[str(M[i, j]) for j in range(2)] for i in range(2)],
        trace=str(tr),
        determinant=str(det),
        sigma=str(sigma),
        classification=classification,
        fixed_polynomial=str(fp),
        fixed_points=fixed_points,
        eigenvalues=[str(v) for v in eigenvalues],
        projective_eigendirections=directions,
        multiplier_at_zero=str(mul_zero) if mul_zero is not None else None,
        multiplier_at_infinity=str(mul_inf) if mul_inf is not None else None,
        attracting_fixed_point=attracting,
        pairing_invariant=pairing,
        quaternion_norm_symbolic=str(quaternion_norm),
        forward_orbit_from_1=[str(v) for v in orbit] if orbit else None,
    )


# Loxodromic example in SL(2,C): determinant 1 and non-real trace
lox = sp.Matrix([[1 + sp.I, 1], [sp.I, 1]])

PACKETS = {
    "hyperbolic": sp.Matrix([[sp.Integer(2), 0], [0, sp.Rational(1, 2)]]),
    "parabolic": sp.Matrix([[sp.Integer(1), sp.Integer(1)], [0, sp.Integer(1)]]),
    "elliptic": sp.Matrix([[0, sp.Integer(-1)], [sp.Integer(1), 0]]),
    "loxodromic": lox,
}


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 mobius_sympy.py <classification>")
        print("Classifications:", ", ".join(PACKETS.keys()))
        sys.exit(1)

    key = sys.argv[1]
    if key not in PACKETS:
        print(f"Unknown classification: {key}")
        sys.exit(1)

    report = verify_packet(PACKETS[key], expected_class=key)
    print(json.dumps(report.__dict__, indent=2, sort_keys=True))
    print("MOBIUS_SYMPY_OK")


if __name__ == "__main__":
    main()
