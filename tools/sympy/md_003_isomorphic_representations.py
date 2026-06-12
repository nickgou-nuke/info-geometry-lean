#!/usr/bin/env python3
"""Finite witness for MD 003 isomorphic representations and metrics.

Mirrors `InfoGeometry.Physics.MD003IsomorphicRepresentations`.

Verified theorem-safe content only:
* normalized Pauli determinant gives the (-,+,+,+) interval via -2 det;
* normalized Pauli trace form is the Euclidean coordinate dot product;
* coordinates are recovered by trace against normalized axes;
* quaternion norm shadow equals the trace self-pairing;
* complex biquaternion matrix coordinates and unit multiplication table;
* unnormalized Pauli soldering forms satisfy the finite Fierz identity.
"""

from __future__ import annotations

import itertools
import sympy as sp


def assert_zero(expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed:\n{reduced}")


def assert_matrix_zero(mat: sp.Matrix, label: str) -> None:
    reduced = mat.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*reduced.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def main() -> int:
    print("=" * 72)
    print("MD 003 ISOMORPHIC REPRESENTATIONS FINITE CORE")
    print("=" * 72)

    I2 = sp.eye(2)
    s1 = sp.Matrix([[0, 1], [1, 0]])
    s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    s3 = sp.Matrix([[1, 0], [0, -1]])
    sigma = [I2, s1, s2, s3]

    dt, dx, dy, dz, c = sp.symbols("dt dx dy dz c")
    X_std = dt * I2 + dx * s1 + dy * s2 + dz * s3
    X_norm = c * X_std
    det_interval = sp.expand((-2) * X_norm.det()).subs(c**2, sp.Rational(1, 2))
    assert_zero(det_interval - (-dt**2 + dx**2 + dy**2 + dz**2), "Minkowski interval from determinant")
    print("determinant/Minkowski interval: OK")

    u, v, w, r = sp.symbols("u v w r")
    Y_std = u * I2 + v * s1 + w * s2 + r * s3
    Y_norm = c * Y_std
    trace_form = sp.trace(X_norm * Y_norm).subs(c**2, sp.Rational(1, 2))
    coord_dot = dt * u + dx * v + dy * w + dz * r
    assert_zero(trace_form - coord_dot, "trace Euclidean coordinate metric")
    print("trace/Euclidean metric: OK")

    axes = [c * S for S in sigma]
    coords = [dt, dx, dy, dz]
    for k, coord in enumerate(coords):
        recovered = sp.trace(axes[k] * X_norm).subs(c**2, sp.Rational(1, 2))
        assert_zero(recovered - coord, f"trace coordinate recovery {k}")
    print("trace coordinate recovery: OK")

    quat_norm = dt**2 + dx**2 + dy**2 + dz**2
    trace_self = sp.trace(X_norm * X_norm).subs(c**2, sp.Rational(1, 2))
    assert_zero(trace_self - quat_norm, "quaternion norm shadow equals trace self-pairing")
    print("quaternion norm / trace self-pairing: OK")

    q0, q1, q2, q3 = sp.symbols("q0 q1 q2 q3")
    biquat = q0 * I2 - sp.I * q1 * s1 - sp.I * q2 * s2 - sp.I * q3 * s3
    assert_zero(sp.trace(I2 * biquat) / 2 - q0, "biquaternion q0 trace readout")
    assert_zero(sp.I * sp.trace(s1 * biquat) / 2 - q1, "biquaternion q1 trace readout")
    assert_zero(sp.I * sp.trace(s2 * biquat) / 2 - q2, "biquaternion q2 trace readout")
    assert_zero(sp.I * sp.trace(s3 * biquat) / 2 - q3, "biquaternion q3 trace readout")

    e0 = I2
    e1 = -sp.I * s1
    e2 = -sp.I * s2
    e3 = -sp.I * s3
    assert_matrix_zero(e1 * e1 + e0, "biquaternion e1 square")
    assert_matrix_zero(e2 * e2 + e0, "biquaternion e2 square")
    assert_matrix_zero(e3 * e3 + e0, "biquaternion e3 square")
    assert_matrix_zero(e1 * e2 - e3, "biquaternion e1e2=e3")
    assert_matrix_zero(e2 * e3 - e1, "biquaternion e2e3=e1")
    assert_matrix_zero(e3 * e1 - e2, "biquaternion e3e1=e2")
    print("complex biquaternion matrix readout/table: OK")

    eps = sp.Matrix([[0, 1], [-1, 0]])
    eta = [-1, 1, 1, 1]
    for A, Ap, B, Bp in itertools.product(range(2), repeat=4):
        lhs = sum(eta[a] * sigma[a][A, Ap] * sigma[a][B, Bp] for a in range(4))
        rhs = -2 * eps[A, B] * eps[Ap, Bp]
        assert_zero(lhs - rhs, f"unnormalized Fierz {(A, Ap, B, Bp)}")
    print("finite unnormalized Fierz identity: OK")

    print("=" * 72)
    print("MD 003 ISOMORPHIC REPRESENTATIONS FINITE CORE VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
