#!/usr/bin/env python3
"""Finite symbolic audit for the discrete Hodge stabilizer layer.

This mirrors `InfoGeometry.Topology.DiscreteHodgeStabilizer`.

Checked finite claims:
* the degree-one stabilizer Hamiltonian is `L1 = d1.T*d1 + d0*d0.T`;
* the quadratic form `x.T*L1*x` is the sum of face and vertex check energies;
* exact and coexact local error sectors are orthogonal when `d1*d0 = 0`;
* filled triangle: harmonic one-form sector is trivial;
* hollow triangle: the cycle harmonic form is orthogonal to exact errors.

No continuum Hodge theorem, code-distance theorem, or QFT claim is made here.
"""

from __future__ import annotations

import sympy as sp


def require_zero(name: str, expr) -> None:
    simplified = sp.simplify(expr)
    if getattr(simplified, "shape", None) is not None:
        simplified = simplified.applyfunc(sp.simplify)
        if simplified != sp.zeros(*simplified.shape):
            raise AssertionError(f"{name} failed:\n{simplified}")
    elif simplified != 0:
        raise AssertionError(f"{name} failed: {simplified}")
    print(f"[ok] {name}")


def require_equal(name: str, lhs, rhs) -> None:
    require_zero(name, lhs - rhs)


def filled_triangle_checks() -> None:
    # Oriented triangle: vertices 0,1,2; edges 01,12,02; face 012.
    d0 = sp.Matrix(
        [
            [-1, 1, 0],
            [0, -1, 1],
            [-1, 0, 1],
        ]
    )
    d1 = sp.Matrix([[-1, -1, 1]])

    require_zero("filled triangle cochain condition d1*d0", d1 * d0)

    x0, x1, x2 = sp.symbols("x0 x1 x2")
    x = sp.Matrix([x0, x1, x2])

    L1 = d1.T * d1 + d0 * d0.T
    face_energy = (d1 * x).dot(d1 * x)
    vertex_energy = (d0.T * x).dot(d0.T * x)
    quadratic = (x.T * L1 * x)[0]

    require_equal(
        "filled triangle stabilizer quadratic form",
        quadratic,
        face_energy + vertex_energy,
    )
    require_equal("filled triangle L1 determinant", L1.det(), sp.Integer(27))

    phi0, phi1, phi2, psi = sp.symbols("phi0 phi1 phi2 psi")
    exact_error = d0 * sp.Matrix([phi0, phi1, phi2])
    coexact_error = d1.T * sp.Matrix([psi])
    require_zero("filled triangle exact/coexact orthogonality", exact_error.dot(coexact_error))

    kernel = L1.nullspace()
    if kernel:
        raise AssertionError(f"filled triangle should have trivial harmonic sector: {kernel}")
    print("[ok] filled triangle harmonic one-form sector is trivial")

    print("filled triangle L1 =")
    sp.pprint(L1)


def hollow_triangle_checks() -> None:
    # Same one-skeleton, but no filled face.  This keeps the one-cycle as a
    # non-trivial harmonic code vector.
    d0 = sp.Matrix(
        [
            [-1, 1, 0],
            [0, -1, 1],
            [-1, 0, 1],
        ]
    )
    L1 = d0 * d0.T
    h = sp.Matrix([1, 1, -1])

    require_zero("hollow triangle harmonic vector is coclosed", d0.T * h)
    require_zero("hollow triangle harmonic vector is in ker L1", L1 * h)

    a, b, c = sp.symbols("a b c")
    exact_error = d0 * sp.Matrix([a, b, c])
    require_zero("hollow triangle harmonic/exact orthogonality", h.dot(exact_error))

    kernel = L1.nullspace()
    if len(kernel) != 1:
        raise AssertionError(f"hollow triangle should have beta1=1, got {kernel}")
    print("[ok] hollow triangle harmonic sector has dimension 1")
    print("hollow triangle harmonic basis =", kernel[0].T)


def main() -> None:
    filled_triangle_checks()
    hollow_triangle_checks()


if __name__ == "__main__":
    main()
