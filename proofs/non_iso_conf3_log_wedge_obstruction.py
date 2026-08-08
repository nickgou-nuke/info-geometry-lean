#!/usr/bin/env python3
"""Check the dlog Arnold relation for three D=4 light-cone quadrics.

For hyperplane arrangements the usual Arnold relation is an identity of
logarithmic one-forms.  For the quadratic divisors

  q12 = q(x-y), q23 = q(y-z), q13 = q(x-z),

the analogous expression

  dlog(q12)^dlog(q23) - dlog(q12)^dlog(q13) + dlog(q23)^dlog(q13)

is not identically zero.  This script computes a concrete non-isotropic sample
where the common-denominator numerator has a nonzero coefficient.
"""

from __future__ import annotations

from itertools import combinations


SIG = (1, -1, -1, -1)


def q(v: tuple[int, int, int, int]) -> int:
    return sum(s * a * a for s, a in zip(SIG, v))


def sub(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(x - y for x, y in zip(a, b))


def grad_qdiff(
    a: tuple[int, ...], b: tuple[int, ...], which: str, mu: int
) -> int:
    """Derivative of q(a-b) in coordinate mu of the first/second variable."""
    val = 2 * SIG[mu] * (a[mu] - b[mu])
    if which == "first":
        return val
    if which == "second":
        return -val
    return 0


def wedge_coeff(u: list[int], v: list[int], i: int, j: int) -> int:
    return u[i] * v[j] - u[j] * v[i]


def full_gradients(x: tuple[int, ...], y: tuple[int, ...], z: tuple[int, ...]) -> tuple[list[int], ...]:
    g12 = []
    g23 = []
    g13 = []
    for point in ("x", "y", "z"):
        for mu in range(4):
            g12.append(
                grad_qdiff(x, y, "first" if point == "x" else "second" if point == "y" else "none", mu)
            )
            g23.append(
                grad_qdiff(y, z, "first" if point == "y" else "second" if point == "z" else "none", mu)
            )
            g13.append(
                grad_qdiff(x, z, "first" if point == "x" else "second" if point == "z" else "none", mu)
            )
    return g12, g23, g13


def arnold_numerator_coeff(
    x: tuple[int, ...], y: tuple[int, ...], z: tuple[int, ...], i: int, j: int
) -> int:
    q12 = q(sub(x, y))
    q23 = q(sub(y, z))
    q13 = q(sub(x, z))
    g12, g23, g13 = full_gradients(x, y, z)
    return (
        wedge_coeff(g12, g23, i, j) * q13
        - wedge_coeff(g12, g13, i, j) * q23
        + wedge_coeff(g23, g13, i, j) * q12
    )


def main() -> None:
    x = (1, 0, 0, 0)
    y = (0, 2, 0, 0)
    z = (0, 0, 3, 0)
    q12, q23, q13 = q(sub(x, y)), q(sub(y, z)), q(sub(x, z))
    assert (q12, q23, q13) == (-3, -13, -8)

    coeffs = {
        (i, j): arnold_numerator_coeff(x, y, z, i, j)
        for i, j in combinations(range(12), 2)
    }
    nonzero = {k: v for k, v in coeffs.items() if v != 0}
    assert nonzero
    # Component dx0 ^ dy0, with variable order x0..x3,y0..y3,z0..z3.
    assert coeffs[(0, 4)] == 52

    print("non_iso_conf3_log_wedge_obstruction.py: dlog Arnold obstruction passed")
    print("sample q12,q23,q13 =", (q12, q23, q13))
    print("common-denominator numerator coefficient dx0^dy0 =", coeffs[(0, 4)])
    print("nonzero 2-form coefficients at sample =", len(nonzero), "of", len(coeffs))


if __name__ == "__main__":
    main()
